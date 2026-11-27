# Zero-initialized unreflected serial CRC Mealy machine

For a register width $r \in \mathbb{N}$ and a width-$r$ taps word $g$, the unreflected serial CRC linear-feedback shift register is the Mealy machine with state alphabet and output alphabet equal to the set of width-$r$ binary words, input alphabet $\{0, 1\}$, initial state $0$, and transition-output function

$$(w, b) \longmapsto (w', w'), \qquad w' = \mathrm{step}_{r, g}(w, b),$$

so on each input bit the machine updates its register by one unreflected serial CRC step and outputs the new register state.
