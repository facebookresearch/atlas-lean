# Register state after feeding a bit sequence

For a register width $r \in \mathbb{N}$, a width-$r$ taps word $g$, and a finite MSB-first bit sequence $B \in \{0, 1\}^*$, the register state $\mathrm{run}_{r, g}(B)$ is the state reached by starting the zero-initialized unreflected serial CRC Mealy machine in state $0$ and feeding the bits of $B$ sequentially.
