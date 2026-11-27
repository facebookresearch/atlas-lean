# Finite-sample likelihood ratio distributions for three-taxon species-tree tests

**General approximation.** Consider $n$ i.i.d. observations from a model with open parameter space $\Theta \subset \mathbb{R}^k$, nested submodels $\Theta_0 \subset \widetilde\Theta \subseteq \Theta$, null $H_0 : \theta \in \Theta_0$ and alternative $\theta \in \widetilde\Theta \setminus \Theta_0$. Let $\theta_0 \in \Theta_0$ have non-singular Fisher information $\mathcal{I}(\theta_0) = (\mathcal{I}^{1/2})^{\mathsf T}\mathcal{I}^{1/2}$ and let $Y \sim \mathcal{N}(\sqrt{n}\,\mathcal{I}^{1/2}\theta_0, I)$.

**Theorem.** Under the regularity conditions of the classical local asymptotic theory of likelihood ratio tests, the likelihood ratio statistic $\Lambda_n$ is approximately distributed as

$$W = \inf_{\tau \in \sqrt{n}\,\mathcal{I}^{1/2}\Theta_0}\|Y - \tau\|^2 - \inf_{\tau \in \sqrt{n}\,\mathcal{I}^{1/2}\widetilde\Theta}\|Y - \tau\|^2,$$

in the sense that $\Lambda_n$ and $W$ converge in distribution to the same limit. Unlike the chi-squared limit, $W$ uses the actual shape of $\Theta_0$ at scale $\sqrt n$, not only its tangent cone at $\theta_0$, so it remains accurate when $\theta_0$ is near (but not at) a boundary or singularity.

**Three-taxon models.** Under the multispecies coalescent on a rooted three-species tree $c|ab$ with internal branch length $t \ge 0$, the rooted gene-tree topologies have probabilities $(p_{C|AB}, p_{B|CA}, p_{A|BC}) = (1 - \tfrac23 e^{-t}, \tfrac13 e^{-t}, \tfrac13 e^{-t})$. In **model T1** the null is $\Theta_0 = \{p_1 \ge p_2 = p_3 > 0\}$ in the open 2-simplex (species tree $c|ab$), which has a boundary point at $(\tfrac13,\tfrac13,\tfrac13)$; in **model T3** the null is the union of the three such sets (some species tree), which is singular at that point. Write the true point as $\theta_0 = (1 - \tfrac23\phi_0, \tfrac13\phi_0, \tfrac13\phi_0)$ with $\phi_0 = e^{-t} \in (0,1]$, and let $Z \sim \mathcal{N}(0,1)$, $\bar Z \sim \mathcal{N}(\mu_0, 1)$ be independent with

$$\mu_0 = \sqrt{2n}\,\frac{1 - \phi_0}{\sqrt{\phi_0(3 - 2\phi_0)}}, \qquad \alpha_0 = \arctan\frac{1}{\sqrt{3(3 - 2\phi_0)}} .$$

**Proposition.**

1. (Model T1) $\Lambda_n$ is approximately distributed as $\widetilde\Lambda_n = Z^2 + \tfrac12\big(1 - \operatorname{sgn}\bar Z\big)\bar Z^2$, whose density for $\lambda > 0$ is

$$f(\lambda) = \frac14 e^{-\lambda/2}\Big[\sqrt{\frac{2}{\pi\lambda}}\Big(1 + \operatorname{erf}\frac{\mu_0}{\sqrt2}\Big) - e^{-\mu_0^2/2}M_0(\mu_0\sqrt\lambda)\Big]$$

for an explicit special function $M_0$.
2. (Model T3) $\Lambda_n$ is approximately distributed as

$$\widetilde\Lambda_n = \min\Big(Z^2 + \tfrac12\big(1 - \operatorname{sgn}\bar Z\big)\bar Z^2,\ \sin^2\alpha_0\big(Z + \cot\alpha_0\,\operatorname{sgn}(Z)\,\bar Z\big)^2\Big),$$

which also has a closed-form density in terms of error functions.

As $\mu_0 \to \infty$ (long internal branch) the T1 approximation tends to $\chi^2_1$, and at $\phi_0 = 1$ ($\mu_0 = 0$) to the mixture $\tfrac12\chi^2_1 + \tfrac12\chi^2_2$, interpolating between the regular and boundary limits.

## Expansion

Local asymptotic normality makes the rescaled log-likelihood quadratic, so $\Lambda_n$ is close to the difference of squared distances from a Gaussian vector to the rescaled null and full parameter sets, which is the classical limit when the sets are replaced by tangent cones. Keeping the sets at the finite scale $\sqrt n\,\mathcal{I}^{1/2}\Theta_0$ changes nothing asymptotically but captures the geometry seen at the actual sample size. For T1 the null is, after whitening, a ray in the plane: $Z$ is the coordinate orthogonal to it (always counted) and $\bar Z$ the coordinate along it, counted only when it falls past the boundary point. For T3 the null consists of three rays meeting at angles determined by $\alpha_0$, and the statistic is the squared distance to the nearest ray.

## Sources

- Jonathan D. Mitchell, Elizabeth S. Allman, John A. Rhodes, "Hypothesis testing near singularities and boundaries", Electronic Journal of Statistics 13 (2019), 2150–2193, <https://doi.org/10.1214/19-ejs1576>. Published version of arXiv:1806.08458, cited next; locators there refer to the arXiv version.
- Jonathan D. Mitchell, Elizabeth S. Allman, John A. Rhodes, "Hypothesis testing near singularities and boundaries", arXiv (2018). Examples (Models T1 and T3), Theorem 3.1, Propositions 4.1, 4.2, 5.1, 5.2. <https://doi.org/10.48550/arXiv.1806.08458>
