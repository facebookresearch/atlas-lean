# Certified enclosure of a computed sum

Let $n \in \mathbb{N}$, $\ell, \hat\ell, \delta \in \mathbb{R}^n$ and $S, E \in \mathbb{R}$. Suppose each summand is evaluated with error $|\hat\ell_i - \ell_i| \le \delta_i$, and the computed values are accumulated with $|S - \sum_i \hat\ell_i| \le E$ (for rounded recursive summation with unit roundoff $u$ one may take $E = ((1 + u)^n - 1)\sum_i|\hat\ell_i|$). Then

$$\Big|S - \sum_{i} \ell_i\Big| \le E + \sum_i \delta_i.$$
