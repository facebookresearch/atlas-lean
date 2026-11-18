# Talagrand's inequality bounds $W_1$

Let $X$ be a second-countable metric space with a σ-algebra containing the open sets. If a
probability measure $m$ on $X$ satisfies [Talagrand's inequality](satisfies-talagrand.md) with
constant $C \in \mathbb{R}$, then

$$W_1(\mu, m)^2 \le C^+ \operatorname{KL}(\mu \,\|\, m)$$

for every probability measure $\mu$, in $[0, \infty]$ with $C^+ = \max(C, 0)$, because $W_1 \le W_2$; for
$C \ge 0$ the factor is $C$ itself. This is the $T_1$ form of the
transport inequality, the form that controls integrals of Lipschitz functions.

## Background

- [Monotonicity of the Wasserstein distances in the exponent](../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-mono.md):
  $W_1 \le W_2$.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Remark 6.6 (for $W_1 \le W_2$).
