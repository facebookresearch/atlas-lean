# Equivalence and singularity of Wright–Fisher diffusion path measures

**Model.** The Wright–Fisher diffusion with mutation and selection solves
$$dX_t = \tfrac12\big[\theta_1(1 - X_t) - \theta_2 X_t + s\,X_t(1 - X_t)\,\eta(X_t)\big]dt + \sqrt{X_t(1 - X_t)}\,dW_t,$$
with parameter $\vartheta = (\theta_1, \theta_2, s) \in [0,\infty)^2 \times \mathbb{R}$ (mutation rates $\theta_1/2$, $\theta_2/2$ toward and away from the focal allele, selection strength $s$) and a Lipschitz, not identically zero $\eta \colon [0,1] \to \mathbb{R}$ (dominance or frequency dependence). Let $\mathbb{P}^T_\vartheta$ be the law of the path on $[0, T]$ and $\mathbb{P}^0_\vartheta$ its restriction to the germ $\sigma$-field $\mathcal{F}_0 = \bigcap_{t > 0}\mathcal{F}_t$. Two measures are *equivalent* ($\sim$) if mutually absolutely continuous and *singular* ($\perp$) if carried by disjoint sets; only for equivalent measures does a path likelihood exist.

**Theorem.**
1. *(Selection only, Dawson.)* For every $T \in [0, \infty)$, $\mathbb{P}^T_{(\theta_1,\theta_2,s)} \sim \mathbb{P}^T_{(\theta_1,\theta_2,0)}$ with density
$$\frac{d\mathbb{P}^T_{(\theta_1,\theta_2,s)}}{d\mathbb{P}^T_{(\theta_1,\theta_2,0)}} = \exp\Big(\frac{s}{2}\int_0^T \sqrt{X_t(1-X_t)}\,\eta(X_t)\,dW_t - \frac{s^2}{8}\int_0^T X_t(1-X_t)\,\eta^2(X_t)\,dt\Big).$$
2. *(Occupation integrals at a reflecting boundary.)* If $X_0 = 0$ and $\theta_1 \in (0, 1)$, then for each $t > 0$, almost surely $\int_0^t X_s^{-\kappa}\,ds < \infty$ for $0 \le \kappa < \theta_1$ and $= \infty$ for $\kappa \ge \theta_1$; more generally $\int_0^t f(X_s)\,ds$ is finite or infinite according as $f(x)x^{\theta_1 - 1}$ is integrable near $0$ or not.
3. *(Instant singularity at the boundary.)* If $X_0 = 0$ and $\theta_1 \ne \theta_1'$, or $X_0 = 1$ and $\theta_2 \ne \theta_2'$, then $\mathbb{P}^0_\vartheta \perp \mathbb{P}^0_{\vartheta'}$: the mutation rate into an absent allele is revealed by the path in an arbitrarily short time.
4. *(Consistency of estimation from $X_0 \in (0,1)$.)* As $T \to \infty$: if $\theta_1, \theta_2 \ge 1$ the maximum likelihood estimator of $(\theta_1, \theta_2)$ (with $s$ known) is strongly consistent; if $\theta_1, \theta_2 > 0$ a modified estimator that reads off a mutation parameter exactly whenever the path hits a separating boundary is strongly consistent; if exactly one of $\theta_1, \theta_2$ is $0$, the other cannot be estimated consistently (the path is absorbed at the corresponding boundary) while the zero one can; if both are $0$, neither can.

## Expansion

Changing only selection changes the drift by $\frac s2 X(1-X)\eta(X)$, which divided by the volatility $\sqrt{X(1-X)}$ stays bounded, so Novikov's condition holds and Girsanov gives equivalence. Changing mutation rates adds a drift difference of order $\sqrt{(1-x)/x}$ near $0$, which blows up at the boundary; the question becomes whether $\int (1/X_s)\,ds$ is finite, which is decided by the boundary classification (reflecting for $\theta_1 < 1$, entrance for $\theta_1 \ge 1$). Near $0$ the diffusion behaves like a squared Bessel process of dimension $2\theta_1$, whose occupation behavior separates different dimensions instantly. These dichotomies determine when likelihood-based inference of mutation and selection from frequency time series is possible.

## Sources

- P. A. Jenkins, "The mutual arrangement of Wright–Fisher diffusion path measures and its impact on parameter estimation", arXiv:2410.15955 (2024), Equation for the Wright–Fisher SDE (Section 1), Theorem 3.1, Theorem 5.1, Corollaries 5.2–5.3, Theorems 5.5 and 5.8, Theorem 6.1, <https://doi.org/10.48550/arXiv.2410.15955>.
