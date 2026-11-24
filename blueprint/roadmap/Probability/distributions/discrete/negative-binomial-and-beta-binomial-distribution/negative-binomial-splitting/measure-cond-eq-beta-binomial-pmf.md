# Negative binomial splitting for random variables

Let $(\Omega, \mu)$ be a probability space, $X, Y$ independent measurable $\mathbb{N}$-valued random
variables, $r_1, r_2 > 0$ and $0 < p < 1$, with $\mu(X = j) = \mathrm{NB}_{r_1, p}(j)$ and
$\mu(Y = j) = \mathrm{NB}_{r_2, p}(j)$ for all $j$ (the [negative binomial mass
function](../negative-binomial/neg-binomial-pmf.md)). Then for all $k \le n$,

$$\frac{\mu(X = k,\ X + Y = n)}{\mu(X + Y = n)} = \mathrm{BB}(n; r_1, r_2)(k),$$

where $\mathrm{BB}$ is the [beta-binomial mass function](../beta-binomial/beta-binomial-pmf.md).
