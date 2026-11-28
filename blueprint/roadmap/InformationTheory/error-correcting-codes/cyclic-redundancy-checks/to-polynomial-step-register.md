# Polynomial long-division step for the unreflected serial register

Let $r \in \mathbb{N}$, let $g$ and $w$ be width-$r$ binary words, and let $b \in \{0, 1\}$. Let $M_g = X^r + P_g \in \mathbb{F}_2[X]$ be the monic binary modulus of $g$ (so $M_g = 1$ when $r = 0$). Then one unreflected serial CRC register step corresponds to one polynomial long-division step modulo $M_g$:

$$P_{\mathrm{step}_{r, g}(w, b)} = (P_w X + \beta(b)) \bmod M_g.$$
