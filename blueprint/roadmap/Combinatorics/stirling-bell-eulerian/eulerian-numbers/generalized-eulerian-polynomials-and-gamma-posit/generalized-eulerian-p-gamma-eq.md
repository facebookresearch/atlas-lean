# The gamma coefficients of the generalized Eulerian polynomials count permutations

Fix
$n \ge 0$ and let $P_n(q, t; x, y)$ be the generalized Eulerian polynomial. For a permutation $w$
of $\{0, 1, \dots, n-1\}$ write $\mathrm{cyc}(w)$ for its number of cycles (fixed points counted
as cycles), $\mathrm{fix}(w)$ for its number of fixed points, $\mathrm{exc}(w)$ for its number of
excedances (points $i$ with $w(i) > i$) and $\mathrm{dexc}(w)$ for its number of double
excedances. For $k \ge 0$ and rational $q, t$ let $\gamma_{n,k}(q, t)$ be the sum of
$q^{\mathrm{cyc}(w)} t^{\mathrm{fix}(w)}$ over the permutations $w$ of $\{0, 1, \dots, n-1\}$
with $\mathrm{exc}(w) = k$ and $\mathrm{dexc}(w) = 0$. Then for all rational $q, t, x, y$ with
$x \ne y$,

$$
P_n(q, t; x, y) = \sum_{k=0}^{\lfloor n/2 \rfloor} \gamma_{n,k}(q, t) x^k y^k (x + y)^{n - 2k},
$$

and for every $k \ge 0$ and all rational $q, t$,
$\gamma_{n,k}(q, t) = \sum_{i=0}^{n} \sum_{j=0}^{n} \gamma_{n,k,i,j} q^i t^j$, where
$\gamma_{n,k,i,j}$ is the number of permutations $w$ of $\{0, 1, \dots, n-1\}$ with
$\mathrm{exc}(w) = k$, $\mathrm{dexc}(w) = 0$, $\mathrm{cyc}(w) = i$ and $\mathrm{fix}(w) = j$.

## Sources

- Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 7 (`jis-2024-24.1.5-thm-7`).
