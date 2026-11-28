# Kernel-density acquisition function

An experiment planner can propose its next condition without a Gaussian-process posterior: weight each past observation by a kernel density, average the observed values with those weights, and add one uniform density standing for ignorance. A single parameter biases the proposal towards exploitation or exploration.

Let $\mathcal{D}_n = \{(\boldsymbol{x}_k, f_k)\}_{k=1}^{n}$, $n \ge 1$, be observations of an objective on a measurable domain $\mathcal{X}$ of positive finite volume, let $p_k \colon \mathcal{X} \to \mathbb{R}_{>0}$ be a density attached to observation $k$, and let $p_{\mathrm{u}}$ be the uniform density on $\mathcal{X}$, which is positive and finite by that hypothesis. The kernel-regression surrogate and the acquisition function are

$$
s(\boldsymbol{x}) = \frac{\sum_{k=1}^{n} f_k\, p_k(\boldsymbol{x})}{\sum_{k=1}^{n} p_k(\boldsymbol{x})} ,
\qquad
\alpha_{\lambda}(\boldsymbol{x}) = \frac{\sum_{k=1}^{n} f_k\, p_k(\boldsymbol{x}) + \lambda\, p_{\mathrm{u}}(\boldsymbol{x})}{\sum_{k=1}^{n} p_k(\boldsymbol{x}) + p_{\mathrm{u}}(\boldsymbol{x})} ,
\qquad \lambda \in \mathbb{R} .
$$

The planner evaluates the objective at a point of small $\alpha_{\lambda}$, and a batch is obtained by using several values of $\lambda$ at once.

The two displays are different functions, and they do not agree at $\lambda = 0$: with one observation of value $f_1 = 1$, $s \equiv 1$ while $\alpha_0 = p_1/(p_1 + p_{\mathrm{u}}) < 1$ everywhere. What holds is that $\alpha_0$ approaches $s$ wherever the kernel mass dominates the uniform term. Both denominators are positive, so both functions are defined everywhere on $\mathcal{X}$.

The parameter acts pointwise and monotonically: $\alpha_{\lambda}(\boldsymbol{x})$ is increasing in $\lambda$ with derivative $p_{\mathrm{u}}/(\sum_k p_k + p_{\mathrm{u}}) \in (0,1]$, near zero where observations are dense and near one where they are sparse, so a large positive $\lambda$ raises the value of unexplored regions and a large negative $\lambda$ lowers it. This is an algebraic property of the family; where the minimizer moves is not determined by it. Existence of a minimizer needs more than positivity, for instance a compact domain with continuous densities; the source instead searches by uniform sampling with local refinement, which returns an approximate minimizer. The convention is minimization of the objective; for maximization, negate the objective values and the whole expression, not $\lambda$ alone.

The construction uses only that each $p_k$ is a positive density attached to one observation. In the source these come from a Bayesian neural network trained on the observed points, and the surrogate is a Nadaraya–Watson estimate; neither object is needed to state the acquisition function.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes a measurable domain of positive finite volume, positive densities, and defines $s$ and $\alpha_{\lambda}$ by the display; well-definedness is positivity of the denominators. Monotonicity in $\lambda$ is differentiation of a quotient affine in $\lambda$. The failure of $\alpha_0 = s$ is the one-observation computation above. Attainment of the minimum is a separate hypothesis: compactness of $\mathcal{X}$ with continuous $p_k$, or the sampled search the source uses, stated as an approximation.

## Context

Graduate. The acquisition function of Häse, Roch, Kreisbeck and Aspuru-Guzik for self-driving laboratories, where batches of parallel experiments must be proposed cheaply; the categorical extension and the hierarchical scalarisation of this chapter build on it.

## Sources

- Florian Häse, Loïc M. Roch, Christoph Kreisbeck and Alán Aspuru-Guzik, *PHOENICS: A Universal Deep Bayesian Optimizer*, ACS Central Science 4 (2018) 1134–1145, Eqs. 10–12 and Section III B–C, including the sampled search with local refinement. DOI [10.1021/acscentsci.8b00307](https://doi.org/10.1021/acscentsci.8b00307), arXiv:[1801.01469v1](https://arxiv.org/abs/1801.01469v1).
