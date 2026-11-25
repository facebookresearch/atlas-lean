# A path more than 2ηZ inside the tube stays in it a little longer

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md)
with finite species set $S$, finite reaction set $\rho$ and propensities $\lambda_r$, and let
$N \ge 1$. Let $X$ satisfy the [random time-change equations](is-chain-path.md) of $C$ driven by
functions $y_r \colon [0, \infty) \to \mathbb{N}$, and let $x$ be a
[solution of the mean-field equation](is-solution.md) of the network of $C$ on $t \ge 0$, for some
real rate functions. Write $D$ for the [deviation](deviation.md) of $X/N$ from $x$ and
$Z = \sum_r \|\zeta_r\|_1$ for the [sum of the ℓ¹ norms of the reaction vectors](stoich-norm.md).
Let $T$ and $\delta$ be real and $B, \eta \ge 0$, and suppose that:

- $\lambda_r(z)/N \le B$ for every reaction $r$, every $s \in [0, T]$ and every count vector
  $z \in \mathbb{N}^S$ with $\|z/N - x(s)\|_1 < \delta$;
- $|y_r(N a)/N - a| \le \eta$ for every reaction $r$ and every $a \in [0, (B + 1) T]$.

Let $t_0 \in [0, T)$ and let $A$ be real with $D(s) \le A$ for every $s \in [0, t_0]$ and
$A + 2 \eta Z < \delta$. Then there is $\varepsilon > 0$ such that $D(s) < \delta$ for every
$s \in [t_0, t_0 + \varepsilon)$.

Proof: leaving the tube would need a jump that the clock bound forbids. For $s \ge t_0$ near $t_0$
the [scaled clocks](scaled-clock.md) $\Lambda_r$ stay in $[0, (B + 1) T]$, so the clock bound at
both ends gives
$|y_r(N \Lambda_r(s))/N - y_r(N \Lambda_r(t_0))/N| \le |\Lambda_r(s) - \Lambda_r(t_0)| + 2 \eta$;
the scaled clocks and $x$ are continuous, so $D(s)$ is at most $D(t_0) + 2 \eta Z$ plus a term that
tends to $0$ as $s \to t_0$.
