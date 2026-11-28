# Categorical kernel-density acquisition on the simplex

Planning over discrete choices, such as which ligand or solvent to use, needs densities on categories. Relaxing a categorical variable to the interior of the probability simplex, in the chart that drops one coordinate, carries the kernel-density acquisition function to categorical domains.

Let a categorical variable have $n \ge 2$ options and relax it to the relative interior of the simplex,

$$
\Delta^{n-1}_{\circ} = \Big\{ \mathbf{z} \in \mathbb{R}^{n} \;\Big|\; z_i > 0, \; \sum_{i=1}^{n} z_i = 1 \Big\} ,
$$

parametrized by the coordinate chart $(z_1, \dots, z_{n-1}) \mapsto \mathbf{z}$ with $z_n = 1 - \sum_{i<n} z_i$, and carrying the pushforward of Lebesgue measure on that chart. For class weights $\pi = (\pi_1, \dots, \pi_n)$, $\pi_i > 0$, and temperature $\tau > 0$, the concrete density with respect to that measure is

$$
p_{\pi,\tau}(\mathbf{z}) = \Gamma(n)\, \tau^{n-1} \prod_{k=1}^{n} \left( \frac{\pi_k z_k^{-\tau-1}}{\sum_{i=1}^{n} \pi_i z_i^{-\tau}} \right) ,
$$

and a sample is drawn from independent standard Gumbel variates $g_k$ by

$$
z_k = \frac{\exp\big((\log \pi_k + g_k)/\tau\big)}{\sum_{i=1}^{n} \exp\big((\log \pi_i + g_i)/\tau\big)} .
$$

With one such density $p_k$ per observation, observed values $f_k$, the uniform density $p_{\mathrm{u}}$ on the simplex *with respect to the same chart measure*, and a sampling parameter $\lambda$, the acquisition function is

$$
\alpha(\mathbf{z}) = \frac{\sum_{k=1}^{n_{\mathrm{obs}}} f_k\, p_k(\mathbf{z}) + \lambda\, p_{\mathrm{u}}(\mathbf{z})}{\sum_{k=1}^{n_{\mathrm{obs}}} p_k(\mathbf{z}) + p_{\mathrm{u}}(\mathbf{z})} ,
$$

and a candidate is projected to the category of its largest coordinate, under a fixed deterministic tie selector; without one the projection is set-valued.

The reference measure is not optional. Against the induced Euclidean measure of the affine hull the displayed formula is not a probability density: for $n = 2$, $\tau = 1$ and equal weights it equals $1$ at every point $(t, 1-t)$, while the induced arclength element is $\sqrt{2}\,\mathrm{d}t$, so its integral is $\sqrt{2}$. In the chart above it integrates to one, and dividing by $\sqrt{n}$ would convert it to the induced-measure convention.

The relaxation makes the planner differentiable in a categorical variable, and the temperature controls how sharply the density concentrates near the vertices, which lie outside the open simplex. An infimum of $\alpha$ need not be attained: with one observation of value $f_1 = 0$, two categories, $\lambda > 0$ and $0 < \tau < 1$, the kernel density diverges towards a vertex while $\alpha$ stays positive and tends to zero. The source searches random candidates with local refinement, which certifies no optimum. A single-option variable needs a separate convention, since the relaxation is then a point. The descriptor-guided variant reparametrizes the densities using descriptors of the options, changing the parametrization and not the form of the acquisition.

## Depends on

- [Kernel-density acquisition function](kernel-density-acquisition-function.md)
- [Gumbel form of the Karlin–Altschul limit distribution](../../../../Probability/random-walks/calibration-of-karlin-altschul-p-values/exp-neg-mul-exp-eq-gumbel-cdf.md)

## Proof depends on

None.

## Expansion

A formal development defines the open simplex with the chart and its pushforward measure, the concrete density, and the Gumbel-softmax sampler specialized from the location–scale Gumbel law at location $0$ and scale $1$, which the linked page supplies. Two further statements are separate results and are not consequences of the parent acquisition page: that $p_{\pi,\tau}$ is the density of the sampler with respect to the chart measure, and the low-temperature concentration on a vertex. The tie selector is part of the projection, and attainment of an optimum needs a boundary or approximation policy.

## Context

Graduate. The categorical generalization by Häse, Aldeghi, Hickman, Roch and Aspuru-Guzik of the kernel-density planner, aimed at chemistry, where most design variables are discrete choices of reagents.

## Sources

- Florian Häse, Matteo Aldeghi, Riley J. Hickman, Loïc M. Roch and Alán Aspuru-Guzik, *Gryffin: An algorithm for Bayesian optimization of categorical variables informed by expert knowledge*, Applied Physics Reviews 8 (2021) 031406, Section III A and supplementary Section S.1 A, Eqs. 3–5, with the random-candidate search and the descriptor-guided variant. DOI [10.1063/5.0048164](https://doi.org/10.1063/5.0048164), arXiv:[2003.12127v2](https://arxiv.org/abs/2003.12127v2).
- Chris J. Maddison, Andriy Mnih and Yee Whye Teh, *The Concrete Distribution: A Continuous Relaxation of Discrete Random Variables*, International Conference on Learning Representations 2017, Definition 1 and its Jacobian computation, which fix the chart and the reference measure. arXiv:[1611.00712v3](https://arxiv.org/abs/1611.00712v3).
