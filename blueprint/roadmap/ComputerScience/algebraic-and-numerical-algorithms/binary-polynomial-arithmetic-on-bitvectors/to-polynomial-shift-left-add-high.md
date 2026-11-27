# Binary polynomial of a one-bit left shift

Let $s \in \mathbb{N}$ and let $w$ be a width-$s$ binary word with binary polynomial $P_w = \sum_{i=0}^{s-1} w_i X^i \in \mathbb{F}_2[X]$. Let $w \ll 1$ be $w$ shifted left by one bit within width $s$ (that is, $2w \bmod 2^s$), and let $c \in \{0, 1\}$ be the most significant bit of $w$ ($c = w_{s-1}$ when $s \ge 1$, and $c = 0$ when $s = 0$). Then in $\mathbb{F}_2[X]$,

$$P_{w \ll 1} + c X^s = X P_w.$$
