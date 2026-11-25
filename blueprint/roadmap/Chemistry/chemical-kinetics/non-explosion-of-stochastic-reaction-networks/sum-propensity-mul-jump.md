# Propensity-weighted sum of the values after one reaction

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set $\rho$ of reactions, propensities $\lambda_r$, [total propensity](total-rate.md)
$\lambda$ and [generator](generator.md) $L$. For every function $V : \mathbb{N}^S \to \mathbb{R}$ and
every state $x \in \mathbb{N}^S$,

$$
\sum_{r \in \rho} \lambda_r(x)\, V\bigl(x - \mathrm{src}(r) + \mathrm{prod}(r)\bigr)
= L V(x) + \lambda(x)\, V(x),
$$

with the [state after $r$ fires](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md)
computed by truncated subtraction. The left side is $\lambda(x)$ times the mean of $V$ at the next
state, the mean over the [jump kernel](jump-pmf.md) at $x$; when $\lambda(x) = 0$ both sides of the
identity are $0$.
