# Final serial register equals the shifted message remainder for any monic generator

Let $r \in \mathbb{N}$, let $g \in \mathbb{F}_2[X]$ be a monic polynomial of degree $r$ (including $r = 0$, where $g = 1$), and let $t$ be the width-$r$ taps word formed from the low coefficients $g_0, \dots, g_{r-1}$ of $g$. For every finite MSB-first payload $B \in \{0, 1\}^*$, the binary polynomial of the final unreflected serial CRC register run with taps $t$ equals the shifted message remainder modulo $g$:

$$P_{\mathrm{final}_{r, t}(B)} = (m(B) X^r) \bmod g.$$
