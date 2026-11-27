# Moment-ratio gamma approximation to Gaussian quadratic form tails

**Setting.** Let $X\sim\mathcal{N}(\mu,\Sigma)$ in $\mathbb{R}^n$ with $\Sigma$ positive definite (so $\Sigma^{1/2}$ is invertible), let $A \ne 0$ be positive semidefinite, and $Q = X^\top A X$. (For $A = 0$, $Q \equiv 0$ is deterministic and there is nothing to approximate.) Variance-component and kernel association statistics in statistical genetics (kernel-machine pathway tests, SKAT, sum-of-powered-score tests) have this form, and gene-based genome-wide scans need right tails $P(Q>q)$ near $2.5\times10^{-6}$ and below. Writing $M = (\Sigma^{1/2})^\top A\Sigma^{1/2} = P\Lambda P^\top$, $Q \overset{d}{=} (Z+\tilde\mu)^\top\Lambda(Z+\tilde\mu)$ with $Z$ standard normal and $\tilde\mu = P^\top(\Sigma^{1/2})^{-1}\mu$: a weighted sum of independent (non-central) $\chi^2_1$ variables. Its cumulants are

$$c_k = 2^{k-1}(k-1)!\bigl(\operatorname{tr}(\Lambda^k) + k\,\tilde\mu^\top\Lambda^k\tilde\mu\bigr) = 2^{k-1}(k-1)!\bigl(\operatorname{tr}((A\Sigma)^k) + k\,\mu^\top(A\Sigma)^{k-1}A\mu\bigr),$$

with mean $c_1$, variance $c_2$, skewness $\gamma_Q = c_3/c_2^{3/2}$ and kurtosis $\kappa_Q = c_4/c_2^2 + 3$. Under these assumptions $\Lambda \ne 0$, so $c_2, c_3, c_4 > 0$: the variance is positive and the standardized moments are defined, with $\gamma_Q > 0$ and $\kappa_Q > 3$.

**General moment-matching framework.** Choose a reference variable $Y$ with CDF $F_Y(\cdot\mid\theta)$ and approximate $Q$ by $T = aY + b$. Standardized moments of $T$ do not depend on $(a,b)$, so mean and variance are always matched by

$$a^* = \frac{\sigma_Q}{\sigma_Y(\theta)}, \qquad b^* = \mu_Q - a^*\mu_Y(\theta),$$

and $\theta$ is fitted to higher standardized moments, giving $P(Q>q)\approx 1 - F_Y\bigl(\tfrac{\sigma_Y}{\sigma_Q}(q-\mu_Q) + \mu_Y \mid \theta^*\bigr)$. Satterthwaite–Welch (gamma, $b=0$, two moments), Hall–Buckley–Eagleson (gamma, skewness), Liu–Tang–Zhang (non-central $\chi^2_d(\delta)$, skewness and kurtosis) and Wood's $F$ approximation are all instances.

**Moment-ratio (MR) method.** Take $Y\sim\mathrm{Gamma}(\alpha,1)$, whose skewness is $2/\sqrt\alpha$ and excess kurtosis $6/\alpha$, and match the ratio of skewness to excess kurtosis:

$$\frac{2/\sqrt\alpha}{6/\alpha} = \frac{\gamma_Q}{\kappa_Q - 3} \quad\Longrightarrow\quad \alpha^* = \frac{9\,\gamma_Q^2}{(\kappa_Q-3)^2}.$$

The solution always exists (unlike two-moment matching in the non-central chi-square family) and uses both third- and fourth-moment information. A variant (ME) instead minimizes $(\gamma_Y-\gamma_Q)^2 + (\kappa_Y-\kappa_Q)^2$ over $\alpha$, which reduces to $\gamma_Q\alpha^{3/2} - 2(10-3\kappa_Q)\alpha - 36 = 0$ with a unique positive root.

In simulations with block-correlated covariances, MR controls type I error nearly as well as exact characteristic-function inversion (Imhof/Davies) at far-right-tail levels while being markedly faster, and improves on the earlier moment-matching approximations there.

## Depends on

- [Standard Gaussian quadratic form as a weighted chi-square sum](../skat-variance-component-test/std-gaussian-map-inner-eq-weighted-chi-s.md)

## Expansion

Matching the ratio rather than both moments trades one equation for one parameter, so existence is automatic for any $\gamma_Q>0$ and $\kappa_Q>3$; the shape $\alpha^*$ sets how heavy the fitted gamma tail is, and $(a^*,b^*)$ place it at the right mean and scale. The cumulants need only traces: given $B^{k-1}$ and $B^k$ for $B = A\Sigma$, one gets $\operatorname{tr}B^{2k-1} = \sum_{i,j}(B^{k-1})_{ij}(B^k)_{ji}$ and $\operatorname{tr}B^{2k} = \sum_{i,j}(B^k)_{ij}(B^k)_{ji}$ in $O(n^2)$ time, so a single matrix product yields the first four cumulants of a centered $Q$, versus an $O(n^3)$ eigendecomposition.

## Sources

- Hong Zhang, Judong Shen and Zheyang Wu, "A Fast and Accurate Approximation to the Distributions of Quadratic Forms of Gaussian Variables", *Journal of Computational and Graphical Statistics* 31 (2022), 304–311, <https://doi.org/10.1080/10618600.2021.2000423>. Numbering as in the preprint arXiv:2005.00905v2, <https://arxiv.org/abs/2005.00905v2>: Section 2 (Lemma 2.1, moment-matching framework, moment-ratio and minimized-error methods) and Section 3 (simulations).
