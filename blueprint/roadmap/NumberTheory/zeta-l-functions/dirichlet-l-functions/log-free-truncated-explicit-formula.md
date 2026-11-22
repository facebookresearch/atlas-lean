# Log-free truncated explicit formula for Dirichlet characters

There are absolute constants $C$ and $C'$ such that, for every modulus $q \ge 2$, every Dirichlet
character $\chi$ modulo $q$ and every real $x \ge q^{C}$,

$$
\Bigl| \sum_{n \le x} \Lambda(n) \chi(n) - \delta_\chi x + \sum_{\rho} \frac{x^\rho}{\rho} \Bigr|
\le C' \, \frac{x}{q^2} \log^2 q,
$$

where $\delta_\chi$ is $1$ if $\chi$ is principal and $0$ otherwise, and $\rho$ runs over the zeros
of $L(\cdot, \chi)$ with $\operatorname{Re} \rho > 3/4$ and $|\operatorname{Im} \rho| \le q^2$,
counted with multiplicity. Compared with the truncated explicit formula at height $T = q^2$, the
error term has no power of $\log x$.

The proof refines the proof of the truncated explicit formula rather than applying it. In the
truncated Perron formula, the terms $n$ close to $x$ are bounded there with $\Lambda(n) \le \log x$,
which loses a factor $\log x$; instead, their contribution is bounded with an upper bound of
Brun–Titchmarsh type for the number of primes in a short interval $(x, x + y]$, of order
$y / \log y$, the prime powers $p^k$ with $k \ge 2$ in such an interval being comparatively few.

## Sources

- T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>, Exercise 5 (for non-principal $\chi$ of modulus $q$ and $x \ge q^{C}$ with $C$ large, $\sum_{n \le x} \Lambda(n) \chi(n) = -\sum_{\operatorname{Re} \rho > 3/4,\ |\operatorname{Im} \rho| \le q^2} x^\rho / \rho + O((x/q^2) \log^2 q)$, with an additional term $x$ for the principal character), and the author's comment of 3 August 2018 on the notes: the log-free version requires replacing "the somewhat crude analysis in the proof of the truncated Perron formula" by "the log-free bound provided by the Brun–Titchmarsh inequality".
