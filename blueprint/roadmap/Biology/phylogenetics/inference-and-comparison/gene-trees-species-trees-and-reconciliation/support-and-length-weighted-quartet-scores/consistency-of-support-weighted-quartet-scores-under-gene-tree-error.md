# Consistency of support-weighted quartet scores under gene-tree error

**Multispecies coalescent.** For a quartet $Q = \{a,b,c,d\}$ with species-tree topology $ab|cd$ and internal branch of length $d_Q$ coalescent units, let $\theta_Q = 1 - e^{-d_Q}$. A true gene tree $G^*$ satisfies

$$\Pr(\delta_{G^*}(ab|cd) = 1) = \tfrac13(1 + 2\theta_Q), \qquad \Pr(\delta_{G^*}(ac|bd) = 1) = \Pr(\delta_{G^*}(ad|bc) = 1) = \tfrac13(1 - \theta_Q).$$

**MSC+Error+Support model.** Each estimated gene tree $G$ is drawn given $G^*$ as follows, per quartet $Q$: with probability $\alpha_{G,Q} \in [0,1]$ (the gene's signal, drawn independently of $G^*$ with mean $\bar\alpha_Q$ and variance $\sigma_\alpha^2$) the estimated quartet equals the true one; otherwise it is one of the three topologies with probabilities $p^1_{G,Q}, p^2_{G,Q}, p^3_{G,Q}$. The bias is

$$\beta_Q = \max_G \max_i \big|3 p^i_{G,Q} - 1\big|,$$

and the support of an estimated topology is assumed to equal its probability given $G^*$: $\alpha_{G,Q} + (1 - \alpha_{G,Q})\,p^i_{G,Q}$ if it matches the true topology, $(1 - \alpha_{G,Q})\,p^i_{G,Q}$ otherwise. In the worst case $3p^1 = 1 - \beta_Q$, $3p^2 = 1 + \beta_Q$, $3p^3 = 1$, the estimated-topology distribution (species topology first) is

$$\tfrac13\,\alpha_{G,Q}\,(1 + 2\theta_Q,\ 1 - \theta_Q,\ 1 - \theta_Q) + \tfrac13\,(1 - \alpha_{G,Q})\,(1 - \beta_Q,\ 1 + \beta_Q,\ 1).$$

**Proposition 1.** For each estimated gene tree,

$$\mathbb E\big[\delta_G(ab|cd) - \delta_G(ac|bd)\big] \ge \theta_Q \bar\alpha_Q - \tfrac23 (1 - \bar\alpha_Q)\beta_Q,$$

$$\mathbb E\big[w_G(ab|cd) - w_G(ac|bd)\big] \ge \tfrac19\theta_Q(3 + 2\beta_Q)(\bar\alpha_Q^2 + \sigma_\alpha^2) + \tfrac29(3 - \beta_Q)\,\theta_Q\bar\alpha_Q - \tfrac49(1 - \bar\alpha_Q)\beta_Q,$$

where $w_G$ is the support weight. Consistency of maximizing the (weighted) quartet score requires the corresponding expectation to be positive for every quartet.

**Theorem 1.** Under the MSC+Error+Support model there are parameter values $(\theta_Q, \bar\alpha_Q, \beta_Q)$ for which maximizing the support-weighted score is statistically consistent and maximizing the unweighted score is not, and none for which the reverse holds.

**Length weighting (Proposition 2, Theorem 2).** For true gene-tree topologies whose substitution-unit lengths are coalescent lengths times a constant $\lambda$ (or, Proposition 3, times segment-wise random multipliers $\Lambda_I$ of mean $\lambda$ whose variance is at most the explicit bound of Proposition 3, $\mathrm{Var}(\Lambda_I) \le \varepsilon^2(\lambda, L) = \dfrac{e^{-\lambda L}}{(16 + 32\lambda) + (6 + 32\lambda + 32\lambda^2)L}\Big(\dfrac{20(\lambda + \lambda^2)}{9(1 + 2\lambda)^2}\Big)^3$ for every branch segment $I$, with $L$ the total length of the other branches), let $X_G = w_G(ab|cd) - w_G(ac|bd)$ with the length weight and $Y_G = \delta_G(ab|cd) - \delta_G(ac|bd)$. As the internal branch length $f \to 0$ with $k = \Theta(f^{-2})$ genes, $\mathrm{Var}[X_G] = \Theta(1)$ and $\mathbb E[X_G]/\sqrt{\mathrm{Var}[X_G]}$ exceeds $\mathbb E[Y_G]/\sqrt{\mathrm{Var}[Y_G]} = \sqrt{3/2}\, f + O(f^2)$ by a factor greater than one depending on $\lambda$; consequently

$$\Pr\Big(\sum_G w_G(ab|cd) \le \sum_G w_G(ac|bd)\Big) \le \Pr\Big(\sum_G \delta_G(ab|cd) \le \sum_G \delta_G(ac|bd)\Big),$$

i.e. length weighting has no worse, and asymptotically a constant-factor better, sample complexity than the unweighted score.

## Depends on

- [Support- and length-weighted quartet score](support-and-length-weighted-quartet-score.md)
- [The species quartet maximizes quartet support](../../../../coalescent-theory/multispecies-coalescent/split-01-most-probable.md)

## Expansion

The MSC quartet probabilities give $\mathbb E[Y_{G^*}] = \theta_Q$, and mixing with the error model gives the first bound: the noise term subtracts at most $\tfrac23(1 - \bar\alpha_Q)\beta_Q$. Under support weighting, a gene contributes to the correct topology with weight roughly $\alpha_{G,Q}$ when it is correct, so its contribution scales with $\alpha_{G,Q}^2$; noisy genes are down-weighted relative to informative ones, and the positive term $\tfrac19\theta_Q(3 + 2\beta_Q)\mathbb E[\alpha^2]$ can outweigh adversarial bias in regimes where $\theta_Q\bar\alpha_Q < \tfrac23(1 - \bar\alpha_Q)\beta_Q$, which is where unweighted ASTRAL is positively misleading (long-branch attraction combined with low signal). Comparing the regions where the two right-hand sides are positive (worst case $\sigma_\alpha = 0$) yields Theorem 1. For length weighting the key fact is that, under the coalescent, gene trees discordant with the species tree arise from deep coalescence and therefore have longer terminal paths on average, so the exponential length weight preferentially discounts discordant quartets; the unweighted ratio $\sqrt{3/2}\,f$ follows from $\mathbb E[Y] = \theta$, $\mathrm{Var}[Y] = \tfrac{2 + \theta}{3} - \theta^2 \to \tfrac23$ and $\theta = f + O(f^2)$.

## Sources

- C. Zhang, S. Mirarab, "Weighting by gene tree uncertainty improves accuracy of quartet-based species trees", Molecular Biology and Evolution (2022), Materials and Methods ("Theoretical Results: Improved Consistency and Sample Complexity": MSC+Error+Support model, Proposition 1, Theorem 1; naive and variable-rate models, Propositions 2–3, Theorem 2) and Table 1, <https://doi.org/10.1093/molbev/msac215> (PMC9750496).
