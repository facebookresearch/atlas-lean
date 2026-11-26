# Final serial register equals the shifted message remainder (taps form)

Let $r \in \mathbb{N}$, let $g$ be a width-$r$ taps word with monic binary modulus $M_g = X^r + P_g \in \mathbb{F}_2[X]$, and let $B \in \{0, 1\}^*$ be a finite MSB-first payload. After flushing with $r$ zero bits, the binary polynomial of the final unreflected serial CRC register equals the shifted message remainder modulo $M_g$:

$$P_{\mathrm{final}_{r, g}(B)} = (m(B) X^r) \bmod M_g.$$
