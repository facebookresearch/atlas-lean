# Sign of the direct effect under contagion and randomization design

**Setting.** $N$ clusters; cluster $i$ has $n_i$ members, and infection spreads within but not between clusters. Treatment $x_{ij} \in \{0,1\}$ is assigned at time $0$; $Y_{ij}(t) = \mathbf{1}\{T_{ij} < t\}$ is the infection indicator. Infection follows the **structural transmission model**: a susceptible member $j$ has hazard

$$\lambda_{ij}(t) = e^{x_{ij}\beta + \eta_{ij}}\Big(\alpha + \sum_{k \ne j} y_{ik}(t)\, e^{x_{ik}\gamma + \xi_{ik}}\Big),$$

where $\alpha > 0$ is the force of infection from outside the cluster, $\eta_{ij}$ and $\xi_{ik}$ are individual susceptibility and infectiousness coefficients, $\beta$ is the treatment effect on susceptibility and $\gamma$ the treatment effect on infectiousness. The **susceptibility effect** (hazard ratio for $j$ treated versus untreated, holding the treatments and infection histories of all others fixed) is $\mathrm{SHR}_{ij} = e^{\beta}$, so $\beta = 0$ means the treatment does not protect its recipient.

The **individual average direct effect** at a fixed follow-up time $\mathcal{T}$ is $DE_{ij}(\mathcal{T}) = \overline{Y}_{ij}(\mathcal{T}, 1) - \overline{Y}_{ij}(\mathcal{T}, 0)$, where $\overline{Y}_{ij}(\mathcal{T}, x)$ averages the expected infection outcome over the conditional law of the other cluster members' treatments given $X_{ij} = x$. Three designs are considered: **Bernoulli** (independent $\mathrm{Bernoulli}(p)$ treatments), **block** (exactly $m_i = \lfloor p n_i \rfloor \ge 1$ treated, uniformly at random) and **cluster** (all members treated with probability $p$, otherwise none).

**Theorem.** Suppose $\beta = 0$ (no susceptibility effect) and $\mathcal{T} > 0$ (with $\alpha = 0$ or $\mathcal{T} = 0$ nobody is infected and $DE_{ij} = 0$ for every $\gamma$).

1. Under Bernoulli randomization, $DE_{ij}(\mathcal{T}) = 0$.
2. Under block randomization, $\operatorname{sign} DE_{ij}(\mathcal{T}) = -\operatorname{sign}\gamma$: the direct effect is positive when treatment lowers infectiousness ($\gamma < 0$), zero when $\gamma = 0$, and negative when $\gamma > 0$.
3. Under cluster randomization, $\operatorname{sign} DE_{ij}(\mathcal{T}) = \operatorname{sign}\gamma$.

The same signs hold for the cluster-average and population-average direct effects $DE_i(\mathcal{T})$ and $DE(\mathcal{T})$. Consequently, an intervention with no effect on its recipient's susceptibility can show a nonzero direct effect of either sign, and under block or cluster randomization the direct effect need not recover the sign of $\beta$.

## Expansion

When $\beta = 0$, $j$'s own treatment enters its hazard only through the treatments of the others. Under Bernoulli randomization those treatments are independent of $X_{ij}$, so both arms see the same law of cluster-mates' treatments and the contrast vanishes. Under block randomization, conditioning on $X_{ij} = 1$ leaves $m_i - 1$ treated among the other $n_i - 1$ members, versus $m_i$ when $X_{ij} = 0$: a treated subject has fewer treated (hence, if $\gamma < 0$, more infectious) cluster-mates. Cluster randomization reverses this: a treated subject's cluster-mates are all treated. The sign claims follow from a coupling. Lemma: $Y^1$ stochastically dominates $Y^0$ iff there is a coupling with $\tilde Y^1 \ge \tilde Y^0$ almost surely. An explicit algorithm runs the two epidemics on shared exponential clocks, swapping one treated and one untreated cluster-mate between the arms; when $\gamma < 0$ every infection hazard in one arm dominates the other at all times, so the infection indicator of $j$ is ordered pathwise, and taking expectations gives the strict sign.

## Sources

- Daniel J. Eck, Olga Morozova, Forrest W. Crawford, "Randomization for the susceptibility effect of an infectious disease intervention", Journal of Mathematical Biology 85 (2022), 37, <https://doi.org/10.1007/s00285-022-01801-8>. Published version of arXiv:1808.05593, cited next; locators there refer to the arXiv version.
- Daniel J. Eck, Olga Morozova, Forrest W. Crawford, "Randomization for the susceptibility effect of an infectious disease intervention", arXiv (2018). Definitions 1–3, Propositions 1–3, Lemmas 1–2, Corollaries 1–3. <https://doi.org/10.48550/arXiv.1808.05593>
