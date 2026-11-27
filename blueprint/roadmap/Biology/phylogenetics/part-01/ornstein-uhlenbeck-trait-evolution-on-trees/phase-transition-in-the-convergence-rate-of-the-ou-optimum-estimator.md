# Phase transition in the convergence rate of the Ornstein–Uhlenbeck optimum estimator on phylogenies

**Model.** A continuous trait evolves along an ultrametric species tree $\mathcal T$ with $n$ leaves and height $T$ by an Ornstein–Uhlenbeck process

$$dX_t = -\alpha\,(X_t - \mu)\,dt + \sigma\,dB_t,$$

with selection strength $\alpha > 0$, optimum $\mu$, and stationary variance $\gamma = \sigma^2/(2\alpha)$. The root value is drawn from $\mathcal N(\mu, \gamma)$, and at each branching point independent copies continue along the daughter edges; the data are the trait values at the leaves. Let $\hat\mu$ be the maximum likelihood estimator of $\mu$ given $\alpha$. For a sequence of trees $(\mathcal T_k)$ with $n_k$ leaves and heights $T_k$, define the upper growth rate $\overline\Lambda^{g} = \limsup_k \frac{\log n_k}{T_k}$ (and the lower one with $\liminf$).

**Theorem.**

1. (Consistency.) $\hat\mu^{(k)}$ is consistent if and only if, for every $s > 0$, the number of lineages of $\mathcal T_k$ at time $s$ before the leaves tends to infinity. This holds for nested or growing tree sequences whose height tends to infinity.
2. (General lower bound.) For every ultrametric tree,

$$\mathrm{Var}_{\mathcal T}[\hat\mu] \ \ge\ \gamma\Big(e^{-2\alpha T} + \frac{1 - e^{-2\alpha T}}{n}\Big).$$

3. (Supercritical regime.) If $\overline\Lambda^{g} > 2\alpha$, then for every $\varepsilon > 0$ there is a subsequence along which $\mathrm{Var}[\hat\mu^{(k)}] \ge \gamma\,n_k^{-2\alpha/(\overline\Lambda^{g} - \varepsilon)}$, so $\hat\mu$ is not $\sqrt{n_k}$-consistent.
4. (Subcritical regime.) If $\overline\Lambda^{g} < 2\alpha$, then $\mathrm{Var}[\hat\mu^{(k)}] = \Omega(n_k^{-1})$, and it is $O(n_k^{-1+\varepsilon})$ when the growth rate equals the branching number of the sequence.

**Corollary (Yule trees).** For a Yule tree with speciation rate $\lambda$, almost surely $\hat\mu$ is consistent; it is $\sqrt{n}$-consistent if $\lambda < 2\alpha$; and if $\lambda > 2\alpha$, for every $\varepsilon > 0$,

$$C'\,n^{-2\alpha/\lambda - \varepsilon} \ \le\ \mathrm{Var}[\hat\mu] \ \le\ C\,n^{-2\alpha/\lambda + \varepsilon}.$$

In contrast, $\alpha$ and $\gamma$ can be estimated at rate $n^{-1/2}$ on such trees, from the many pairs of closely related leaves.

So adding species helps estimate the selective optimum only when the tree grows slower than the decorrelation rate $2\alpha$ of the OU process; on rapidly branching phylogenies the shared ancestry caps the information.

## Expansion

The variance of the best linear unbiased estimator equals the effective resistance of an electrical network on the tree: for any unit flow $\theta$ from the root to the leaves, $\mathrm{Var}[Y_\theta] = \gamma e^{-2\alpha T}(1 + \sum_b R_b\theta_b^2)$ with edge resistances $R_b$ that grow like $e^{2\alpha s}$ with the distance $s$ from the root, and $\mathrm{Var}[\hat\mu]$ is the infimum over flows. When lineages proliferate faster than $e^{2\alpha s}$, a uniform flow makes the resistance bounded and the variance is of order $e^{-2\alpha T} = n^{-2\alpha/\Lambda}$, worse than $n^{-1}$; when they proliferate slower, the leaves are nearly independent and the variance is of order $1/n$. The link between flows and the branching number of the tree gives the matching upper bounds.

## Sources

- Cécile Ané, Lam Si Tung Ho, Sebastien Roch, "Phase transition on the convergence rate of parameter estimation under an Ornstein-Uhlenbeck diffusion on a tree", arXiv (2014). Section 2 (model, growth rates), Theorems 1–4, Corollaries 1–4, Propositions 1–3. <https://doi.org/10.48550/arXiv.1406.1568>. Published version: Journal of Mathematical Biology 74(1-2) (2017), 355–385, <https://doi.org/10.1007/s00285-016-1029-x>; locators above refer to the arXiv version.
