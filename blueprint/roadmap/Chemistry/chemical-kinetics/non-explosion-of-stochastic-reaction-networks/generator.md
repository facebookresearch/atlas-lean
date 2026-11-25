# Generator of a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set $\rho$ of reactions and propensities $\lambda_r$. For a function
$V : \mathbb{N}^S \to \mathbb{R}$ and a state $x \in \mathbb{N}^S$, the generator of $N$ applied to
$V$ at $x$ is

$$
L V(x) = \sum_{r \in \rho} \lambda_r(x)
\bigl(V(x - \mathrm{src}(r) + \mathrm{prod}(r)) - V(x)\bigr),
$$

where $x - \mathrm{src}(r) + \mathrm{prod}(r)$ is the
[state after $r$ fires](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/fire.md),
computed coordinatewise with natural-number subtraction truncated at $0$. A reaction whose
reactants are missing at $x$ has $\lambda_r(x) = 0$ and contributes nothing, so only reactions with
$\mathrm{src}(r) \le x$, for which the subtraction is exact, enter the sum.
