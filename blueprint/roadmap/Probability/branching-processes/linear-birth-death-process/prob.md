# Kendall's law of the linear birth–death process

For real numbers $b, d, t$, with $\alpha(t)$ [Kendall's extinction
probability](extinction-prob.md) and $\beta(t)$ [the geometric tail ratio](geom-ratio.md), define
for $n \in \mathbb{N}$

$$p_0(t) = \alpha(t), \qquad p_{n+1}(t) = (1 - \alpha(t))(1 - \beta(t))\, \beta(t)^n .$$

For $b, d \ge 0$ and $t \ge 0$, $p_n(t) = P(X_t = n \mid X_0 = 1)$ is the law at time $t$ of the
linear birth–death process with per-capita birth rate $b$ and death rate $d$ started from one
individual.

## Sources

- D. G. Kendall, *On the generalized "birth-and-death" process*, Annals of Mathematical
  Statistics 19 (1948), 1–15.
