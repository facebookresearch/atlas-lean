# Jump kernel of a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set $\rho$ of reactions, propensities $\lambda_r$ and [total propensity](total-rate.md)
$\lambda$. Its jump kernel gives, for each state $x \in \mathbb{N}^S$, a probability distribution
$P(x, \cdot)$ on $\mathbb{N}^S$, the law of the next state. At a state with $\lambda(x) = 0$ (an
absorbing state) it is the point mass at $x$. At a state with $\lambda(x) > 0$ it is the image of
the [law of the next reaction](reaction-pmf.md) under $r \mapsto x - \mathrm{src}(r) + \mathrm{prod}(r)$,
the [state after $r$ fires](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md):
for $y \in \mathbb{N}^S$,

$$
P(x, \{y\}) = \sum_{r \in \rho,\ x - \mathrm{src}(r) + \mathrm{prod}(r) = y}
\frac{\lambda_r(x)}{\lambda(x)}.
$$

Reactions that lead to the same state add up their probabilities, and a reaction with
$\mathrm{prod}(r) = \mathrm{src}(r)$ and $\lambda_r(x) > 0$ gives a jump from $x$ to itself.
