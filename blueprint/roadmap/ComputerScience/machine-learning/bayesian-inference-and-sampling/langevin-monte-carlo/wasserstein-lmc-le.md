# Wasserstein convergence of Langevin Monte Carlo (Dalalyan)

Let $p \ge 1$ and $f : \mathbb{R}^p \to \mathbb{R}$ be differentiable with, for some $m, M > 0$ and all $\theta, \theta'$,

$$
f(\theta) - f(\theta') - \nabla f(\theta')^\top(\theta - \theta') \ge \tfrac m2\|\theta - \theta'\|^2, \qquad \|\nabla f(\theta) - \nabla f(\theta')\| \le M\|\theta - \theta'\| ,
$$

and let $\pi$ have density $e^{-f}/\int e^{-f}$. Let $0 < h \le 2/(m+M)$ and let $\nu_k$ be the law of the $k$-th [Langevin Monte Carlo](lmc-step.md) iterate, started from a law $\nu_0$ with finite second moment. Then for every $K \ge 0$,

$$
W_2(\nu_K, \pi) \le (1 - mh)^K\, W_2(\nu_0, \pi) + 1.82\,\frac{M}{m}\,(hp)^{1/2} .
$$

The first term is the contraction of gradient descent on the $m$-strongly convex, $M$-smooth $f$; the second is the bias of the Euler discretization of the Langevin diffusion, which does not vanish as $K \to \infty$. To reach $W_2(\nu_K, \pi) \le \varepsilon$ it suffices to take $h \asymp m^2\varepsilon^2/(M^2 p)$ and $K \asymp (p/\varepsilon^2)\log(p/\varepsilon)$ iterations. The finite second moment of $\nu_0$, implicit in the source, rules out the indeterminate product $0\cdot\infty$ when $mh = 1$.

## Background

- [Wasserstein distance](../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md): the metric $W_2$ in which the bound is stated.
- [Linear convergence of gradient descent for strongly convex functions](../../../../Analysis/convex-analysis-and-variations/gradient-descent/gradient-descent-strongly-convex-linear.md): the noiseless analogue; Dalalyan recovers $\|\theta_K - \theta^\star\| \le (1 - m/M)^K\|\theta_0 - \theta^\star\|$ from this bound in the zero-temperature limit (Section 3 of the source).
- [Convergence of the JKO scheme to the Fokker–Planck equation](../../../../MeasureTheory/optimal-transport/wasserstein-gradient-flows-and-the-jko-scheme/jko-scheme/tendsto-jko-fokker-planck.md): the law of the Langevin diffusion is the Wasserstein gradient flow of the free energy, of which this algorithm is a discretization.
- [Talagrand's transport inequality](../../../../Probability/concentration-inequalities/transport-cost-inequalities/satisfies-talagrand.md): strongly log-concave targets satisfy $W_2^2 \le (2/m)\,\mathrm{KL}$, which converts the relative-entropy bounds of Cheng and Bartlett into $W_2$ bounds.

## Sources

- A. S. Dalalyan, *Further and stronger analogy between sampling and optimization: Langevin Monte Carlo and gradient descent*, arXiv:1704.04752v2, the corrected arXiv version of the COLT 2017 paper (the proceedings version prints a different constant), Theorem 1(a), under condition (1).
- A. Durmus and É. Moulines, *High-dimensional Bayesian inference via the unadjusted Langevin algorithm*, arXiv:1605.01559 (Bernoulli 25 (2019)): the earlier Wasserstein bound, recalled as (6) in Dalalyan's paper.
