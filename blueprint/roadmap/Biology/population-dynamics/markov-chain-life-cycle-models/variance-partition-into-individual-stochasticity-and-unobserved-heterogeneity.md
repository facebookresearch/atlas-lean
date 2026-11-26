# Variance partition into individual stochasticity and unobserved heterogeneity

**Setting.** A cohort is a finite mixture of $g$ fixed, unobserved heterogeneity (UH) groups. Group $k$ follows a stage-structured absorbing Markov chain with transient matrix $U_k$, and a newborn belongs to group $k$ with probability $\pi_k$ (the mixing distribution $\pi$). The joint stage-by-group chain uses the block-diagonal matrix $\mathbb U = \operatorname{diag}(U_1, \dots, U_g)$, rearranged by a vec-permutation matrix $K$ into stage-major order, $\tilde U = K^{\mathsf T}\mathbb U K$; individuals never change group. Let $\xi$ be a demographic outcome (longevity, lifetime reproductive output, age at first breeding) and $\xi_k$ its value for an individual of group $k$, with group mean $\mathbb E(\xi_k)$ and variance $V(\xi_k)$ computed from the [fundamental matrix](occupancy-times-and-longevity-from-the-fundamental-matrix.md) of $U_k$.

**Proposition.** The inter-individual variance of $\xi$ in the cohort is

$$V(\xi) = \underbrace{\mathbb E_\pi\bigl[V(\xi_k)\bigr]}_{\text{individual stochasticity}} + \underbrace{V_\pi\bigl[\mathbb E(\xi_k)\bigr]}_{\text{unobserved heterogeneity}},$$

where $\mathbb E_\pi$ and $V_\pi$ are the mean and variance over the mixing distribution. The first, within-group term is the variance among individuals sharing identical stage-specific rates; the second, between-group term vanishes in the absence of heterogeneity. In the southern fulmar application, heterogeneity explained only a small share of the variance (about 4% for age at first breeding), the rest being individual stochasticity.

## Depends on

- [Occupancy times and longevity from the fundamental matrix](occupancy-times-and-longevity-from-the-fundamental-matrix.md)

## Expansion

This is the law of total variance with the group label as conditioning variable. Since group membership is fixed for life, each group's outcome distribution is that of its own absorbing chain, so the within-group moments come from $N_k = (I - U_k)^{-1}$, and the mixture moments are $\pi$-weighted sums. Intra-cohort selection (frail groups dying first) changes the group composition with age, so the partition depends on the stage and age at which the cohort is followed.

## Sources

- S. Jenouvrier, L. M. Aubry, C. Barbraud, H. Weimerskirch and H. Caswell, "Interacting effects of unobserved heterogeneity and individual stochasticity in the life history of the southern fulmar", *Journal of Animal Ecology* (2018), Eqs. (11)–(12) and (14) and Table 3. <https://doi.org/10.1111/1365-2656.12752> (PMC5765524)
