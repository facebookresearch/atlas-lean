# Hurwitz zeta at $3/4$ and odd arguments

For every integer $k \ge 1$,

$$
\zeta(2k+1, \tfrac34) = -\frac{2^{2k-1} \pi^{2k+1} |E_{2k}|}{(2k)!} +
2^{2k} (2^{2k+1} - 1) \zeta(2k+1),
$$

where $\zeta(s, a)$ is the Hurwitz zeta function (for $\operatorname{Re} s > 1$,
$\zeta(s, a) = \sum_{n \ge 0} (n + a)^{-s}$), $\zeta(s)$ is the Riemann zeta function and $E_{2k}$
is the even-index Euler number.

The even-index Euler numbers are defined by a binomial recurrence equivalent to the generating
function $1 / \cosh t = \sum_n E_n t^n / n!$. The source writes $k \in \mathbb{N}$; $k = 0$ is
excluded since $s = 1$ is the pole of both zeta functions.

## Sources

- László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 3 (`jis-2025-25.4.4-lem-3`).
