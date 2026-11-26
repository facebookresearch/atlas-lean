# Posterior number of causal variants at a locus

Let $S = (S_1, \dots, S_m)^\top$ be the marginal association $z$-scores of $m$ variants in a locus with LD (correlation) matrix $\Sigma$. Under a linear model with standardized genotypes, let $\Lambda = (\lambda_1, \dots, \lambda_m)^\top$ be the vector of normalized causal effects (non-centralities). Approximately, jointly

$$S \mid \Lambda \sim N(\Sigma \Lambda, \Sigma),$$

so $\mathbb{E}[S_c \mid \Lambda] = (\Sigma\Lambda)_c$: each marginal statistic sums the causal effects through LD. Only in the special case of a single causal variant $c$ (or when no other causal variant is correlated with $c$) does this reduce to $S_c \sim N(\lambda_c, 1)$; for example, two causal variants with $\lambda_1 = \lambda_2 = 1$ and LD $r_{12} = \tfrac12$ give $\mathbb{E}[S_1 \mid \Lambda] = 1.5$. Let $C \in \{0,1\}^m$ be the causal configuration ($c_i = 1$ if variant $i$ is causal) and place the prior $\Lambda \mid C \sim N(0, \Sigma_C)$ with $\Sigma_C = \sigma^2 \operatorname{diag}(c_1, \dots, c_m)$, so non-causal variants have zero effect. Integrating out $\Lambda$,

$$S \mid C \sim N\!\left(0,\ \Sigma + \Sigma \Sigma_C \Sigma\right).$$

Assume from here on that $\Sigma$ is positive definite, so that these Gaussian laws have densities and $\Sigma^{-1}$ exists; a singular $\Sigma$ (for example two perfectly correlated markers) makes $P(S \mid C)$ undefined as a density even for the empty configuration, and such markers must first be merged or pruned. With independent prior probability $\gamma$ of being causal, $P(C) = \prod_i \gamma^{c_i}(1 - \gamma)^{1 - c_i}$ (or variant-specific $\gamma_i$ from functional annotation), the posterior probability that the locus contains exactly $k$ causal variants is

$$\Pr(N_c = k \mid S) = \frac{\sum_{|C| = k} P(S \mid C)\, P(C)}{\sum_{C} P(S \mid C)\, P(C)},$$

the denominator running over all configurations, including the empty one. A locus shows **allelic heterogeneity** when $\Pr(N_c \ge 2 \mid S)$ is large.

**Fast likelihood.** Evaluating $P(S \mid C)$ directly costs $O(m^3)$. Writing $\Sigma\Sigma_C\Sigma$ through its rank-$k$ factor (with $k = |C|$ causal indices $\alpha_1, \dots, \alpha_k$), set $U \in \mathbb R^{m \times k}$ with $U_{\alpha_i, i} = \sigma$ and zeros elsewhere, and $V \in \mathbb R^{k \times m}$ with $V_{i, j} = \sigma\, r_{\alpha_i, j}$, so that $\Sigma_C \Sigma = U V$ and

$$S^\top(\Sigma + \Sigma\Sigma_C\Sigma)^{-1} S = S^\top (I_m + U V)^{-1} \Sigma^{-1} S,$$

$$(I_m + UV)^{-1} = I_m - U (I_k + V U)^{-1} V$$

by the Woodbury identity, and $\det(\Sigma + \Sigma\Sigma_C\Sigma) = \det\Sigma \cdot \det(I_k + VU)$ by the matrix determinant lemma. Since $\Sigma^{-1}S$ and $\det\Sigma$ do not depend on $C$, each configuration costs $O(m^2 k)$ rather than $O(m^3)$.

## Remarks

Conditional on $\Lambda$, $S$ is Gaussian with mean $\Sigma\Lambda$ (each marginal statistic sums the causal effects through LD) and covariance $\Sigma$; a Gaussian prior on $\Lambda$ makes the marginal law Gaussian with covariance $\Sigma + \Sigma\Sigma_C\Sigma$. The posterior on $N_c$ is Bayes' rule summed over configurations of each size; in practice the sum is restricted to configurations with at most a few causal variants. Writing $\Sigma + \Sigma\Sigma_C\Sigma = \Sigma(I_m + \Sigma_C\Sigma)$ gives both the quadratic-form identity and the determinant factorization. Applied to GWAS summary statistics, the method was assessed in simulations and found that many genome-wide significant loci for complex traits are likely to carry two or more causal variants.

## Sources

- F. Hormozdiari, A. Zhu, G. Kichaev et al., "Widespread allelic heterogeneity in complex traits", The American Journal of Human Genetics 100 (2017), 789–802, Material and Methods ("Computing the Likelihood of Causal Configuration", "Computing the Number of Independent Causal Variants in a Locus", "Reducing the Computational Complexity"; Equations 1–12; Equation 2 is the single-causal-variant case and Equation 4 the joint model with several causal variants), <https://doi.org/10.1016/j.ajhg.2017.04.005> (PMC5420356).
