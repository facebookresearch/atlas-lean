# Run invariant of the unreflected serial CRC register

Let $r \in \mathbb{N}$, let $g$ be a width-$r$ taps word with monic binary modulus $M_g = X^r + P_g \in \mathbb{F}_2[X]$, and let $B \in \{0, 1\}^*$ be any finite MSB-first bit sequence. After running $B$ from the zero register, the binary polynomial of the register equals the remainder of the message polynomial modulo $M_g$:

$$P_{\mathrm{run}_{r, g}(B)} = m(B) \bmod M_g.$$
