# Optimal importance-sampling proposal for $\Lambda$-coalescent likelihoods

**Setting.** Loci $L$, alleles $E_l$ at locus $l$, mutation rates $\theta_l$ with total $\theta = \sum_l\theta_l$, mutation transition matrices $P^{(l)}$, haplotypes $\mathcal H = \prod_l E_l$; $S^a_l(h)$ is haplotype $h$ with locus $l$ overwritten by allele $a$. A sample is a count vector $\mathbf n = (n_h)_{h\in\mathcal H}$ from the stationary $\Lambda$-Fleming–Viot process, whose genealogy is the $\Lambda$-coalescent with rates $\lambda_{b,k} = \int_0^1 x^{k-2}(1-x)^{b-k}\Lambda(dx)$ for a given $k$ of $b$ lineages to merge. The likelihood $\mathbb P(H_0)$ of the observed configuration is a sum over ancestral histories $H_0, H_{-1},\dots,H_{-T}$ (single mutation or merger events back to the most recent common ancestor), and importance sampling (IS) draws histories backward from a proposal $\mathbb Q(H_i \mid H_{i+1})$.

Let $\pi(\mathbf m \mid \mathbf n)$ be the conditional sampling distribution (CSD) of the types of $m$ further individuals given a sample $\mathbf n$.

**Theorem.** The optimal (zero-variance) proposal is

$$\mathbb Q^*(H_i \mid H_{i+1}) \propto \begin{cases} (n_{i+1})_h\,\theta_l\,\dfrac{\pi(\mathbf e_{S^a_l(h)} \mid H_{i+1} - \mathbf e_h)}{\pi(\mathbf e_h \mid H_{i+1} - \mathbf e_h)}\,P^{(l)}_{a\,h[l]}, & H_i = H_{i+1} - \mathbf e_h + \mathbf e_{S^a_l(h)},\\[3mm] \dfrac{\binom{(n_{i+1})_h}{k}\,\lambda_{n_{i+1},k}}{\pi\big((k-1)\mathbf e_h \mid H_{i+1} - (k-1)\mathbf e_h\big)}, & H_i = H_{i+1} - (k-1)\mathbf e_h,\end{cases}$$

ranging over all mutations of present haplotypes and all mergers of $k \in \{2,\dots,(n_{i+1})_h\}$ lineages of a common type $h$. Unlike Kingman's coalescent, multiple mergers require the multivariate CSD $\pi((k-1)\mathbf e_h \mid \cdot)$; because its argument contains a single type, it can be factorized into univariate CSDs without breaking exchangeability.

**Approximate CSD.** Let a single extra lineage, traced backward, mutate at locus $l$ at rate $\theta_l$ via $P^{(l)}$ and be absorbed into the fixed *trunk* $\mathbf n$ (a degenerate ancestry with no dynamics) at rate $\frac{1}{n+1}\sum_{k=2}^{n+1}\binom{n+1}{k}\lambda_{n+1,k}$ (where $\lambda_{n+1,2}$ already includes the Kingman atom $\Lambda(\{0\})$), copying a uniformly chosen trunk lineage. Its type law $\hat\pi^K(\mathbf e_h \mid \mathbf n)$ solves the linear system

$$\Big[\theta + \tfrac{1}{n+1}\textstyle\sum_{k=2}^{n+1}\binom{n+1}{k}\lambda_{n+1,k}\Big]\hat\pi^K(\mathbf e_h \mid \mathbf n) = \textstyle\sum_{l}\theta_l\sum_{a\in E_l}P^{(l)}_{a\,h[l]}\hat\pi^K(\mathbf e_{S^a_l(h)} \mid \mathbf n) + \tfrac{n_h}{n(n+1)}\textstyle\sum_{k=2}^{n+1}\binom{n+1}{k}\lambda_{n+1,k},$$

and is the stationary distribution of a Markov chain on $\mathcal H$. Plugging $\hat\pi^K$ into $\mathbb Q^*$ gives an approximately optimal IS proposal; with $\Lambda = \delta_0$ it reduces to the Stephens–Donnelly approximation for Kingman's coalescent.

## Expansion

By Bayes, the optimal backward transition is the forward transition reweighted by the ratio of likelihoods of the configurations before and after the event, and likelihood ratios of configurations differing by a few lineages are CSDs; the forward rates of the $\Lambda$-coalescent with mutation give the combinatorial prefactors. Exact CSDs are intractable, so they are replaced by approximations that mimic the genealogy of one extra lineage: the trunk ancestry freezes the sample, and the absorption rate equals the rate at which a new lineage joins a merger with the $n$ existing ones. These approximations also feed product-of-approximate-conditionals (PAC) likelihoods and extend to $\Xi$-coalescents with simultaneous multiple mergers.

## Sources

- Jere Koskela, Paul A. Jenkins, Dario Spanò, "Computational inference beyond Kingman's coalescent", *Journal of Applied Probability* 52 (2015), 519–537, <https://doi.org/10.1239/jap/1437658613>; preprint arXiv:1311.5699, <https://doi.org/10.48550/arXiv.1311.5699>. Numbering of the arXiv version: Section 2 (model, Theorem 1), Section 3 (Theorem 2, Corollary 1, Definitions 1–3, Proposition 1), Section 5 ($\Xi$-coalescents, Theorem 3).
