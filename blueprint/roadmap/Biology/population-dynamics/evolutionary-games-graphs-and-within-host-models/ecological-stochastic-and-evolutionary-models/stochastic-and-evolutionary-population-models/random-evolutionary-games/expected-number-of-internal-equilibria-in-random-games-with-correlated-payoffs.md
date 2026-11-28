# Expected number of internal equilibria in random games with correlated payoffs

**Setting.** In a $d$-player game with two strategies $A$ and $B$, let $a_k$ (resp. $b_k$) be the payoff to an $A$- (resp. $B$-) player facing $k$ $A$-players among the other $d - 1$, and $\beta_k = a_k - b_k$. Interior rest points $x \in (0, 1)$ of the replicator dynamics solve $\sum_k \beta_k \binom{d-1}{k}x^k(1 - x)^{d-1-k} = 0$, equivalently, with $y = x/(1 - x) > 0$,

$$P(y) = \sum_{k=0}^{d-1}\beta_k\binom{d-1}{k}y^k = 0.$$

Let the $\beta_k$ be jointly Gaussian, standardized, with $\mathrm{corr}(\beta_i, \beta_j) = r \in [0, 1]$ for $i \ne j$, and let $E(r, d)$ be the expected number of internal equilibria (positive roots of $P$).

**Theorem.**

1. *(Integral formula.)* $E(r, d) = 2\int_0^1 f(t; r, d)\,dt$, where $f$ is the Edelman–Kostlan density of real zeros,

    $$f(t; r, d) = \frac1\pi\sqrt{\partial_x\partial_y \log K(x, y)\big|_{x = y = t}}, \qquad K(x, y) = (1 - r)\sum_{i=0}^{d-1}\binom{d-1}{i}^2 (xy)^i + r(1 + x)^{d-1}(1 + y)^{d-1},$$

    and $f$ satisfies $f(1/t) = t^2 f(t)$, which reduces the integral over $(0, \infty)$ to $(0, 1)$.

2. *(Correlation reduces equilibria.)* For each $t$, $r \mapsto f(t; r, d)$ is decreasing; hence $r \mapsto E(r, d)$ is decreasing.
3. *(Stable equilibria.)* If $(a_k)$ and $(\beta_k)$ are exchangeable, the expected number of stable internal equilibria is $SE(r, d) = E(r, d)/2$, also decreasing in $r$.
4. *(Large $d$, formal asymptotics.)* $E(0, d) \sim \tfrac12\sqrt{2d - 1}$; for $0 < r < 1$, $E(r, d) \sim \dfrac{8\,\Gamma(5/4)^2}{\sqrt\pi}\cdot\dfrac{d^{1/4}(1 - r)^{1/2}}{2\pi^{5/4}r^{1/2}}$; and $E(1, d) = 0$.

## Expansion

The positive roots of $P$ are the internal equilibria, so $E$ is the expected number of positive zeros of a Gaussian random polynomial, given by the Kac–Rice/Edelman–Kostlan formula in terms of the covariance kernel $K(x, y) = \mathbb E[P(x)P(y)]$. The kernel splits into an independent part (weights $\binom{d-1}{i}^2$) and a fully correlated rank-one part $r(1 + x)^{d-1}(1 + y)^{d-1}$; the rank-one part makes $P$ behave like a common random multiple of $(1 + y)^{d-1}$, which has no positive roots, so increasing $r$ suppresses sign changes. This drops the growth from $d^{1/2}$ (independent payoffs) to $d^{1/4}$ for any fixed correlation.

## Sources

- Manh Hong Duong, Hoang Minh Tran and The Anh Han, "On the Expected Number of Internal Equilibria in Random Evolutionary Games with Correlated Payoff Matrix", Dynamic Games and Applications 9 (2019), 458–485, <https://doi.org/10.1007/s13235-018-0276-4>; numbering as in arXiv:1708.01672: Theorem 1.1, Theorems 3.2, 3.4, 3.6 and Proposition 4.1.
