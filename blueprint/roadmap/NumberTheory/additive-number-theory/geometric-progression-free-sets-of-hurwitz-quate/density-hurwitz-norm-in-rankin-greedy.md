# Density of Hurwitz quaternions with norm in Rankin's greedy set

A Hurwitz quaternion is a
quaternion whose four rational coordinates are either all integers or all halves of odd integers;
its norm is the sum of the squares of its coordinates. For a natural number $N$ let $S(N)$ be the
set of nonzero Hurwitz quaternions of norm at most $N$. Let $G$ be the set of positive integers
$n$ such that, for every prime $p$, the base-$3$ digits of the exponent $\nu_p(n)$ of $p$ in $n$
include no $2$ (this is Rankin's greedy set of positive integers avoiding 3-term geometric
progressions), and let $H_G$ be the set of Hurwitz quaternions whose norm lies in $G$. With
$f(x) = \prod_{i \ge 0} \bigl(1 + x^{-3^i}\bigr)$, the ratio $|H_G \cap S(N)| / |S(N)|$ tends,
as $N \to \infty$, to

$$\frac{6}{\pi^2} \, f(4) \prod_{p > 2} \Bigl( f(p) - \frac{f(p^2)}{p} \Bigr),$$

the product running over the odd primes $p$.

The paper writes this constant as $(f(2^2)/\zeta(2)) \prod_{p > 2} (f(p) - f(p^2)/p)$, using
$1/\zeta(2) = 6/\pi^2$, and gives its value as approximately $0.782643$.

## Sources

- Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding 3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article 24.7.7, Theorem 7 (restated as the unnumbered theorem of the introduction).
