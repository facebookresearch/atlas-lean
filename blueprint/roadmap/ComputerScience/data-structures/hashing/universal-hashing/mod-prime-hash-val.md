# Value of the mod-prime hash

For natural numbers $p$ and $m$ with $m > 0$ and elements
$a, b, x$ of $\mathbb{Z}/p\mathbb{Z}$, the mod-prime hash value
$h_{a,b}(x) \in \{0, \dots, m - 1\}$, read as a natural number, equals
$\operatorname{val}(ax + b) \bmod m$. Here $ax + b$ is computed in $\mathbb{Z}/p\mathbb{Z}$, and
$\operatorname{val}(z)$ is the canonical natural-number representative of $z$: the residue in
$\{0, \dots, p - 1\}$ when $p > 0$, and $|z|$ when $p = 0$.
