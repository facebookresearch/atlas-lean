# Reciprocal sign epistasis lower bound on the number of fitness peaks

Let $W : \{0,1\}^n \to \mathbb R$ be a fitness landscape on binary genotypes with no strictly neutral mutations (every genotype differs in fitness from each of its one-mutation neighbours). A **peak** is a genotype fitter than all its neighbours. An **instance of reciprocal sign epistasis** (RSE) is a set of four distinct genotypes $s_1, s_2, s_3, s_4$ such that $s_1$ and $s_4$ are each one mutation away from both $s_2$ and $s_3$ (a two-dimensional face of the hypercube with $s_1, s_4$ opposite) and

$$\max\big(W(s_2), W(s_3)\big) < \min\big(W(s_1), W(s_4)\big).$$

**Theorem.**

$$\#\{\text{RSE instances}\} \ \ge\ \#\{\text{peaks}\} - 1.$$

In particular two peaks force at least one RSE instance (the qualitative necessity result), and three peaks force at least two.

## Depends on

- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](epistasis-and-landscape-structure.md)

## Expansion

Build a graph $G$ on $V = \{0,1\}^n$ with two kinds of edges. $E_1$: each non-peak genotype is joined to one of its fittest beneficial neighbours, so following $E_1$ is steepest ascent; since an edge is chosen only by its lower endpoint, $|E_1| = |V| - p$, where $p$ is the number of peaks, and $(V, E_1)$ is a forest whose components each contain exactly one peak. $E_2$: join $u, v$ at Hamming distance two when both intermediate genotypes are less fit than $u$ and $v$; each such edge is a distinct RSE instance. The key claim is that $G$ is connected. Otherwise take, among single-mutation paths joining peaks in different components, one whose minimum fitness is largest, and let $v_m$ be its minimum. Vertices before $v_m$ lie in one component and those after in another (else a path with a higher minimum would exist), and the two vertices adjacent to $v_m$ on the path, $u_1$ and $u_2$, are at distance two with both intermediates no fitter than $v_m$ (else one could bypass $v_m$), so $\{u_1, u_2\} \in E_2$ joins the components, a contradiction. A connected graph on $|V|$ vertices has at least $|V| - 1$ edges, so $|E_2| \ge |V| - 1 - |E_1| = p - 1$. The original proof phrases the final count through Forman's strong Morse inequality $m_1 - m_0 \ge b_1 - b_0$ for a discrete Morse function equal to $-W$ on vertices, with $E_2$ edges as the critical edges and peaks as the critical vertices.

## Sources

- R. Saona, F. A. Kondrashov, K. A. Khudiakova, "Relation between the number of peaks and the number of reciprocal sign epistatic interactions", Bulletin of Mathematical Biology 84(8) (2022) 74 (with a published correction, Bulletin of Mathematical Biology 85(3) (2023) 17), Theorem 1, Theorem 2 (strong Morse inequality), Definitions 1–3 and the proof of Theorem 1, <https://doi.org/10.1007/s11538-022-01029-z>, PMCID PMC9205815.
