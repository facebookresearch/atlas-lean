# Yearly mutation rate under sex-specific generation times

**Setting.** Follow one autosomal neutral site backward along a lineage. At each generation the lineage passes through the father or through the mother, each with probability $1/2$, independently across generations (Mendelian transmission). A paternal transmission takes $G_M > 0$ years (the father's age at conception) and introduces a new mutation at the site with probability $\mu_M(G_M)$; a maternal transmission takes $G_F > 0$ years and introduces one with probability $\mu_F(G_F)$. Let the pairs $(G_M, \mu_M(G_M))$ and $(G_F, \mu_F(G_F))$ be drawn independently in each generation from fixed laws with finite means, and write $\bar G_M = \mathbb E G_M$, $\bar G_F = \mathbb E G_F$, $\bar\mu_M = \mathbb E\,\mu_M(G_M)$, $\bar\mu_F = \mathbb E\,\mu_F(G_F)$.

**Proposition (calendar-time rate).** Let $D(T)$ be the expected number of mutations per base pair accumulated on the lineage during the generations completed in the last $T$ years. Then

$$\lim_{T\to\infty} \frac{D(T)}{T} = \mu_y = \frac{\bar\mu_M + \bar\mu_F}{\bar G_M + \bar G_F}.$$

The per-generation rate seen in parent–offspring trios is the average over the two transmitted genomes, $\mu_G = (\bar\mu_M + \bar\mu_F)/2$, so $\mu_y = \mu_G/\bar G$ with the sex-averaged generation time $\bar G = (\bar G_M + \bar G_F)/2$. The common practice $\hat\mu_y = \hat\mu_G/\bar G$ is therefore correct only when $\hat\mu_G$ was measured at the same paternal and maternal ages as the $\bar G$ it is divided by.

**Corollary (linear parental-age effects).** Suppose $\mu_M(g) = \alpha_M + \beta_M g$ and $\mu_F(g) = \alpha_F + \beta_F g$ with $\beta_M > \beta_F \ge 0$ (a strong paternal age effect, a weaker maternal one). Write $S = \bar G_M + \bar G_F$ and $\rho = \bar G_M / S$ for the male share of the generation interval. Then

$$\mu_y = \frac{\alpha_M + \alpha_F}{S} + \beta_M \rho + \beta_F (1 - \rho).$$

1. At fixed $S$, $\mu_y$ increases strictly with $\rho$, at rate $\beta_M - \beta_F$: a child of an old father and a young mother carries more mutations than a child of a young father and an old mother with the same mean parental age, so the yearly rate depends on the ratio of male to female generation times and not only on their average.
2. At fixed $\rho$, $\mu_y$ decreases in $S$ if and only if $\alpha_M + \alpha_F > 0$, that is, if part of the per-generation mutation load does not grow with parental age (mutations accrued before puberty, or a nonzero intercept). This is the generation-time effect: longer generations give fewer mutations per year, but only through the intercept.
3. Neither the per-generation rate $\mu_G$ nor the yearly rate $\mu_y$ is a constant of the species; both move with ages at puberty and reproduction, so a substitution clock calibrated in one era or lineage need not hold in another.

## Depends on

- [Long-run expected calendar-time rate of neutral substitution](../../long-run-neutral-substitution-rate-law-of-large.md)

## Expansion

Let $X_k$ and $Y_k$ be the mutation probability and the duration in years of the $k$-th generation back. The pairs $(X_k, Y_k)$ are independent and identically distributed, with $\mathbb E X_k = (\bar\mu_M + \bar\mu_F)/2$ and $\mathbb E Y_k = (\bar G_M + \bar G_F)/2$. The number of completed generations in $T$ years is a renewal counting process with interarrival times $Y_k$, and $D(T) = \mathbb E \sum_{k \le N(T)} X_k$; the renewal-reward theorem gives $D(T)/T \to \mathbb E X_1/\mathbb E Y_1$, which is the displayed ratio, the factors of $1/2$ cancelling. Neutral sites fix at the rate they arise per generation (the dependency), so $\mu_y$ is also the long-run yearly substitution rate along the lineage. The corollary is algebra on $(\alpha_M + \alpha_F + \beta_M \bar G_M + \beta_F \bar G_F)/S$ after substituting $\bar G_M = \rho S$ and $\bar G_F = (1-\rho) S$. The paternal slope reflects spermatogonial divisions that continue after puberty, whereas oocytogenesis is complete by the mother's birth, so replication-driven mutations add little maternal age dependence; a maternal slope, where present, points to damage-driven mutation.

## Sources

- P. Moorjani, Z. Gao, M. Przeworski, *Human germline mutation and the erratic evolutionary clock*, PLoS Biology 14 (2016), e2000744, <https://doi.org/10.1371/journal.pbio.2000744>, PMCID PMC5070741. Sections "Step 1: What Exactly Is Being Estimated from Human Pedigrees?" (linear paternal age effect, weaker maternal effect), "Step 2: How to Obtain a Yearly De Novo Mutation Rate?" (the practice $\hat\mu_y = \hat\mu_G/\bar G$ and its implicit assumptions) and "Step 3: How to Relate μ to the Substitution Rate Expected over Evolutionary Time?" (dependence on male and female generation times separately, the generation-time effect). The renewal argument and the linear corollary are derived here from the stated model.
