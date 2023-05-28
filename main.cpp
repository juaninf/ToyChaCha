#include <iostream>
#include "chacha.h"

void pretty_print_state(ul * state, int state_len) {
    for (int i=0;i<state_len;i++) {
        printf("0x%02x ", state[i]);
        if ((i+1)%4==0)
            printf("\n");
    }
}

int main() {
    ul zeroState[16]  = { 1 };
    ul masterKey[8]  = { 0 };
    pretty_print_state(zeroState, 16);
    ENCRYPTION(zeroState, masterKey, false, 4);
    pretty_print_state(zeroState, 16);
    std::cout << "Hello, World!" << std::endl;
    return 0;
}
