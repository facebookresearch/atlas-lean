# Total turning of a boundary orbit is bounded by its length

Let $K \subseteq \mathbb{Z}^2$ and let $a$ be a boundary dart of $K$ (its tail lies in $K$ and its head does not). Let $\sigma_K$ be the successor map on darts along the boundary of $K$, and let $p$ be the minimal period of $a$ under $\sigma_K$ restricted to boundary darts of $K$ (the least $p \ge 1$ with $\sigma_K^p(a) = a$, and $p = 0$ if there is none). For a dart $e$ with direction $u$, write $r = (u_1, -u_0)$ for $u$ rotated clockwise by a quarter turn, and let the signed turn $\tau_K(e)$ be $1$ if $\mathrm{head}(e) + r \in K$, $0$ if $\mathrm{head}(e) + r \notin K$ but $\mathrm{tail}(e) + r \in K$, and $-1$ otherwise. Then the total signed turning around the orbit satisfies

$$\Big|\sum_{i=0}^{p-1} \tau_K\big(\sigma_K^i(a)\big)\Big| \le p.$$
