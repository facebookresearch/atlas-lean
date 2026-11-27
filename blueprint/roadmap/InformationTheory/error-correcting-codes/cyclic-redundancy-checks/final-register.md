# Final register state after flushing with zero bits

For a register width $r \in \mathbb{N}$, a width-$r$ taps word $g$, and a finite MSB-first payload $B \in \{0, 1\}^*$, the final CRC register state $\mathrm{final}_{r, g}(B)$ is the register state obtained by running the zero-initialized unreflected serial CRC register on $B$ followed by $r$ zero bits:

$$\mathrm{final}_{r, g}(B) = \mathrm{run}_{r, g}(B \mathbin{\Vert} 0^r).$$
