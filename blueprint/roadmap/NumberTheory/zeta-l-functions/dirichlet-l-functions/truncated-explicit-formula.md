# Truncated explicit formula for $\psi(x, \chi)$

For every real $\varepsilon$ with $0 < \varepsilon < 1$ there is a constant $C$ such that, for
every modulus $q \ge 1$, every Dirichlet character $\chi$ modulo $q$ and all real $x, T \ge 2$,

$$
\Bigl| \sum_{n \le x} \Lambda(n) \chi(n) - \delta_\chi x + \sum_{\rho} m_\rho \frac{x^\rho}{\rho} \Bigr|
\le C \Bigl( x^{\varepsilon} \log^2 (qT) + \frac{x}{T} \log^2 (xqT) \Bigr),
$$

where $\delta_\chi$ is $1$ if $\chi$ is principal and $0$ otherwise, $\rho$ runs over the zeros
$\rho \ne 1$ of $L(\cdot, \chi)$ with $\operatorname{Re} \rho \ge \varepsilon$ and
$|\operatorname{Im} \rho| \le T$, which are finitely many, and $m_\rho$ is the order of the zero
$\rho$. Here $\Lambda$ is the von Mangoldt function and $L(\cdot, \chi)$ the meromorphic
continuation of $\sum_{n \ge 1} \chi(n) n^{-s}$.

The proof applies the truncated Perron formula, a uniform estimate for a partial sum
$\sum_{n \le x} a_n$ by a contour integral of $\sum_n a_n n^{-s}$ over a vertical segment of
height $T$, to the coefficients $\Lambda(n) \chi(n)$ of $-L'/L(\cdot, \chi)$, and then moves the
contour to the left, picking up the residues at the zeros. Moving the contour uses local
estimates from Jensen's formula and the Borel–Carathéodory theorem: the number of zeros with
imaginary part in an interval of length $1$ is $O(\log(q(2 + |t|)))$, and $L'/L$ is a sum over
those zeros up to $O(\log(q(2 + |t|)))$.

## Sources

- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014), <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>: Exercise 45(iv) for non-principal $\chi$ (zeros counted with multiplicity, Remark 17), whose proof repeats that of Theorem 21 with Exercise 45(i)–(iii) (local zero counts and the approximate formula for $L'/L$) and the truncated Perron formula (Proposition 12); and Theorem 21 for $\zeta$, which gives the principal characters, since for a principal character $\chi$ modulo $q$ the zeros of $L(\cdot, \chi)$ with $\operatorname{Re} \rho > 0$ are those of $\zeta$, with the same orders, and $\sum_{n \le x} \Lambda(n) (1 - \chi(n)) \le \log q \cdot \log x / \log 2$.
