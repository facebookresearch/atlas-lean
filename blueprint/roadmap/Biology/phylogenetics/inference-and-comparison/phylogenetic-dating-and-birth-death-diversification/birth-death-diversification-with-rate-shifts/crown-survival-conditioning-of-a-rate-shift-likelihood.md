# Crown-survival conditioning of a rate-shift likelihood

**Setting.** Let $\tau$ be a reconstructed phylogeny of extant taxa with crown age $t_0$, and let a data-augmented history place regime $R$ with parameters $\theta_R = (\lambda_R, \mu_R)$ at the root and non-root regimes $\theta_1, \dots, \theta_n$ at specified shift points. Let $L(\tau \mid \theta_R, \theta_1, \dots, \theta_n)$ be the product, over branches, of the solutions $D$ of the backward birth–death equations with speciation factors at nodes.

**Conditioned likelihood.** Conditioning on the survival of both crown lineages ($P_S = 1$),

$$L(\tau \mid \theta_R, \theta_1, \dots, \theta_n;\ P_S = 1) = \frac{L(\tau \mid \theta_R, \theta_1, \dots, \theta_n)}{\big(1 - E_R(t_0)\big)^2},$$

where $E_R(t_0)$ is the extinction probability, by the present, of one lineage started at the root with parameters $\theta_R$.

**Proposition (conditioning ignores the augmentation).** In this formula the denominator depends only on $\theta_R$ and $t_0$. Consequently, two augmented histories with the same root regime are compared with the same survival correction, even when one of them places a shift to a regime with high extinction on a crown lineage, which makes survival of that lineage less likely than $1 - E_R(t_0)$.

## Depends on

- [Backward equations for a birth–death process with rate shifts](backward-equations-for-a-rate-shift-birth-death-process.md)

## Expansion

A tree of extant taxa is observed only if both crown lineages leave sampled descendants; under the root regime alone these events are independent, each with probability $1 - E_R(t_0)$, which gives the division by $(1 - E_R(t_0))^2$ (as in the conditioning of Nee et al. 1994). Once shifts are part of the history, the survival probability of each crown lineage depends on the regimes mapped onto it, so dividing by the root-regime survival probability is a different conditioning event from the one the augmented likelihood describes. The source shows that, when extinction is high early in the process, conditioning that uses only current or root parameters can return invalid and potentially unbounded probabilities, and argues that the extinction term must be conditioned on the augmented history, not only on the unobserved shifts of the previous article.

## Sources

- D. L. Rabosky, J. S. Mitchell and J. Chang, *Is BAMM flawed? Theoretical and practical concerns in the analysis of multi-rate diversification models*, Systematic Biology (2017). <https://doi.org/10.1093/sysbio/syx037> (PMCID: PMC5790138). Section "Likelihoods of Rate-Shift Models", Equations (1)–(3), Table 2.
- S. Nee, R. M. May and P. H. Harvey, *The reconstructed evolutionary process*, Philosophical Transactions of the Royal Society B (1994).
