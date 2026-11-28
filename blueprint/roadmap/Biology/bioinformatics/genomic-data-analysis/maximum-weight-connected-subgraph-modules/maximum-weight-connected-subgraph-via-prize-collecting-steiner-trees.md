# Maximum-weight connected subgraph via prize-collecting Steiner trees

**Problems.**

- *Maximum-weight connected subgraph (MWCS).* Given a connected undirected graph $G = (V, E)$ with vertex weights $w : V \to \mathbb R$, find a connected subgraph $T = (V_T, E_T)$ maximizing $w(T) = \sum_{v \in V_T} w(v)$.
- *Prize-collecting Steiner tree (PCST).* Given a connected undirected graph with vertex profits $p : V \to \mathbb R_{\ge 0}$ and edge costs $c : E \to \mathbb R_{\ge 0}$, find a connected subgraph $T$ maximizing $p(T) = \sum_{v \in V_T} p(v) - \sum_{e \in E_T} c(e)$.

Every optimal solution of either problem can be taken to be a tree (for MWCS, any spanning tree of an optimal subgraph has the same weight; for PCST, deleting cycle edges only lowers cost). If all weights are positive, MWCS is solved by the whole graph; with weights of both signs it is NP-hard.

**Reduction.** Let $w' = \min_{v \in V} w(v)$ and assume $w' < 0$. Define $p(v) = w(v) - w'$ for $v \in V$ and $c(e) = -w'$ for $e \in E$; both are nonnegative.

**Theorem 1.** Every tree $T$ of $G$, viewed as a connected subgraph, satisfies $p(T) = w(T) - w' = w(T) + |w'|$; in particular a PCST solution in the transformed instance is a connected subgraph of $(G, w)$ whose weight differs from its profit by the constant $|w'|$.

**Corollary 1.** A maximum-weight connected subgraph of $(G, w)$ is (the vertex set of) an optimal prize-collecting Steiner tree of $(G, p, c)$, and conversely.

Conversely, PCST reduces to MWCS by subdividing each edge $e$ with a new vertex of weight $-c(e)$; since PCST is NP-hard this gives another proof that MWCS is NP-hard. The optimal module is then computed exactly by an integer linear program on a rooted directed version of the PCST instance (Steiner arborescence with exponentially many cut constraints added on demand, inside branch-and-cut).

## Depends on

- [Beta-uniform mixture log-likelihood-ratio node score](beta-uniform-mixture-log-likelihood-ratio-node-score.md)

## Expansion

For a tree $T$ with $|V_T|$ vertices, $|E_T| = |V_T| - 1$, so

$$p(T) = \sum_{v \in V_T}(w(v) - w') - (|V_T| - 1)(-w') = w(T) - |V_T| w' + |V_T| w' - w' = w(T) - w',$$

so the two objectives differ on trees by the constant $-w' = |w'|$ and have the same maximizers, which is Corollary 1. (The theorem appears in the source as $w(T) = p(T) - w'$; the source's own worked example, quoted next, confirms the sign $p(T) = w(T) - w'$.) The edge cost charges each extra vertex exactly the amount $-w'$ added to its profit, so including a vertex pays off in PCST precisely when it pays off in MWCS. The source's example: an MWCS instance with minimum weight $-15$ and optimum $36$ maps to a PCST optimum of profit $126 - 75 = 51 = 36 + 15$.

## Sources

- M. T. Dittrich, G. W. Klau, A. Rosenwald, T. Dandekar, T. Müller, "Identifying functional modules in protein–protein interaction networks: an integrated exact approach", Bioinformatics (2008), Section 3.2 (Problems 1–2, transformation, Theorem 1, Corollary 1, Fig. 3, branch-and-cut algorithm), <https://doi.org/10.1093/bioinformatics/btn161> (PMC2718639).
