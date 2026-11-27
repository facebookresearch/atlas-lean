# Quasi-fixation and dust in the genealogy of a varying-size Fleming–Viot process

**Setting.** Let $(N_t, \rho_t)$ be a $(\bm\gamma, \Pi)$-Fleming–Viot process with population size $N$ and type distribution $\rho$ (events kill a fraction $z_d$ of the population and add an offspring mass $z_b$, with $\int \bm z\, d\Pi < \infty$), realised through its lookdown construction: a countable sequence of levels $1, 2, \dots$ whose types are exchangeable with de Finetti measure $\rho_t$. The genealogy is the coalescent obtained by tracing the ancestry of the lowest levels; *fixation* at time $t$ means $\rho_t$ is a Dirac mass, and *quasi-fixation* means that for every $n$ there is an a.s. finite time after which the lowest $n$ levels all descend from level $1$.

**Theorem (quasi-fixation).** Assume the population size process $N$ is ergodic and that the birth marginal $\Pi_b$ of $\Pi$ does not only charge $0$. Then for every $n \ge 2$, after an a.s. finite time the lowest $n$ levels are descendants of the individual on the lowest level. Consequently the frequency $F_t(\kappa) = \rho_t(\{\kappa\})$ of each type converges a.s. to a $\{0,1\}$-valued limit.

**Theorem (the coalescent contains dust).** For every $t > 0$ the probability that the lowest lineage has had no offspring before $t$ is positive. If $\Pi_d$ does not charge $\{1\}$, then at every time $t$ there are a.s. infinitely many ancestral lineages that do not coalesce in $[0,t]$; in particular the genealogy does not come down from infinity and fixation cannot happen in bounded time.

## Expansion

In the lookdown, an event with effective impact $\bar z = z_b/((1-z_d)N + z_b)$ makes each level independently a child of the lowest participating level with probability $\bar z$. Ergodicity of $N$ makes events with impact bounded below recur at a positive long-run rate, so the lowest level eventually overwrites any finite block of levels. Conversely the subordinator condition makes $\int \bar z\, d\Pi$ finite, the analogue of Pitman's dust criterion $\int_0^1 u^{-1}\Lambda(du) < \infty$ for $\Lambda$-coalescents, so a given lineage avoids all events up to time $t$ with positive probability and, by exchangeability, infinitely many do.

## Depends on

- [Fleming–Viot process with intrinsically varying population size](fleming-viot-process-with-intrinsically-varying-population-size.md)

## Sources

- Julian Kern and Bastian Wiederhold, "A Λ-Fleming-Viot type model with intrinsically varying population size", *Electronic Journal of Probability* 29 (2024), 1–28, <https://doi.org/10.1214/24-ejp1185>. Numbering as in the preprint arXiv:2311.06100v1, <https://arxiv.org/abs/2311.06100v1>: Section 2.2 (Theorems 2.7 and 2.8 on quasi-fixation and dust) and Section 7 (fixation, not coming down from infinity).
