# Stochastic chemical reaction network

A stochastic chemical reaction network on a set $S$ of species, with reactions indexed by a set
$\rho$ (any sets), consists of a
[chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) on $S$ and
$\rho$, which gives each reaction $r$ a source complex $\mathrm{src}(r) \in \mathbb{N}^S$ and a
product complex $\mathrm{prod}(r) \in \mathbb{N}^S$, together with a propensity
$\lambda_r : \mathbb{N}^S \to \mathbb{R}$ for each reaction $r$ such that, for every state
$x \in \mathbb{N}^S$ (molecule counts):

- $\lambda_r(x) \ge 0$;
- $\lambda_r(x) = 0$ when the state lacks the reactants of $r$, that is, when
  $x_s < \mathrm{src}(r)_s$ for some species $s$.

In the model, reaction $r$ fires at rate $\lambda_r(x)$ in state $x$ and moves the state to
$x - \mathrm{src}(r) + \mathrm{prod}(r)$; by the second condition this subtraction is exact
whenever $\lambda_r(x) > 0$ (Anderson–Kurtz 2015, ch. 2). With finitely many species, the
[stochastic mass-action propensities](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md)
$\lambda_r(x) = \kappa_r \prod_s x_s (x_s - 1) \cdots (x_s - \mathrm{src}(r)_s + 1)$ with rate
constants $\kappa_r \ge 0$ satisfy both conditions.
