# Random-disperser criterion for persistence of source–sink metapopulations

**Model.** Patches $1,\dots,K$ form a weighted directed graph; an individual in patch $i$ has a random number $N_i$ of offspring with mean $m_i$ and $\mathbb E[N_i\log^+N_i] < \infty$, and each offspring independently lands in patch $j$ with probability $d_{ij}$. The numbers $Z^{(i)}_n$ of individuals in each patch form a multitype Galton–Watson process with mean matrix $A = (m_id_{ij})$; assume the dispersal chain $D = (d_{ij})$ is irreducible and aperiodic (so $A$ is primitive) and exclude the degenerate case of exactly one offspring a.s. in patch $1$. Let $(X_n)$ be the **random disperser**, the Markov chain with transition matrix $D$, started at $X_0 = 1$, and $T = \min\{n\ge1 : X_n = 1\}$ its return time to patch $1$.

**Theorem.**

1. (Persistence.) The metapopulation survives with positive probability if and only if

$$m_1\,\mathbb E\Big[\prod_{i=1}^{T-1}m_{X_i}\Big] > 1.$$

2. (One source type, one sink type.) If $M := m_1 > 1 > m := m_2 = \cdots = m_K$, $p = \sum_{j\ge2}d_{1j}$ is the dispersal probability from the source and $S$ is the time the disperser spends in sinks between two consecutive visits to sources, then survival has positive probability if and only if

$$M(1-p) + e\,Mp > 1, \qquad e := \mathbb E[m^S] = \sum_{k\ge1}m^k\,\mathbb P(S = k),$$

where $e$ is the *depleting rate* of the sink habitat.
3. (Two patches, period-two environment.) For a source and a sink with dispersal probabilities $p = d_{12}$, $q = d_{21}$, whose mean offspring numbers alternate between environments $e_1, e_2$ (source: $M_1, M_2$; sink: $m_1, m_2$), the population persists with positive probability if and only if

$$M_1M_2(1-p)^2 + (M_1m_2 + m_1M_2)\,pq + m_1m_2(1-q)^2 > \min\big(2,\ 1 + M_1M_2m_1m_2(1-p-q)^2\big).$$

In particular both patches can be sinks in the absence of dispersal ($M_1M_2 \le 1$, $m_1m_2\le1$) while the dispersing metapopulation persists: with $p = q = \tfrac12$ and $m_1 = m_2 = m$ it suffices that $m(M_1 + M_2) > 4$.

## Depends on

- [Matrix population models](../../matrix-population-models/README.md)

## Expansion

For item 1, consider the descendants of an ancestor in patch $1$ who are the first in their lineage to be back in patch $1$. They form a stopping line, and by the branching property their own such descendants are i.i.d. copies, so the population of patch-$1$ "returners" is a single-type Galton–Watson process whose mean is $\mathbb E[Y] = \sum_n m_1\,\mathbb E[\mathbf 1_{T=n}\,m_{X_1}\cdots m_{X_{n-1}}]$, a many-to-one formula along the random disperser. Survival of the whole population is equivalent to survival of this embedded process, i.e. to $\mathbb E[Y] > 1$. Item 2 splits the excursion from the source into staying put (probability $1-p$, factor $M$) or leaving and spending $S$ generations in sinks (factor $Mp\,m^S$). Item 3 applies the Perron root criterion to the mean matrix of the two-generation process $(Z_{2n})$: the largest eigenvalue of a $2\times2$ matrix exceeds $1$ iff the trace exceeds $\min(2, 1 + \det)$.

## Sources

- Vincent Bansaye, Amaury Lambert, "Past, growth and persistence of source-sink metapopulations", arXiv (2011). Section 1 (model and random disperser), Theorem 2.1, Proposition 2.2, Theorem 4.1 and the remark following it. <https://doi.org/10.48550/arXiv.1111.2535>. Published version: "New approaches to source–sink metapopulations decoupling demography and dispersal", Theoretical Population Biology 88 (2013), 31–46, <https://doi.org/10.1016/j.tpb.2013.06.003>; locators above refer to the arXiv version.
