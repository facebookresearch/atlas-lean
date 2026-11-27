# Generalized NNI distance on node-labeled trees

A **1-labeled tree** on a label set $L$ with $|L| = n$ is a tree with $n$ nodes, each carrying a distinct label (internal nodes included, as in mutation trees where every clone carries mutations). A **generalized nearest-neighbour interchange** (gNNI) on an edge $e = (a,b)$ chooses subsets $C_a$, $C_b$ of the other edges at $a$ and at $b$ and reattaches each $(a,x) \in C_a$ to $b$ and each $(b,y) \in C_b$ to $a$; unlike the classical NNI it applies to every edge, including pendant ones. Every 1-labeled tree on $L$ can be transformed into every other by gNNIs; let $d_{\mathrm{gnni}}$ be the minimum number needed.

Each edge $(u,v)$ induces the bipartition $P(e) = \{P_u, P_v\}$ of $L$ into labels closer to $u$ and labels closer to $v$; let $\mathcal{P}(T)$ be the set of these bipartitions and $\mathrm{RF}(S,T) = |\mathcal{P}(S) \,\triangle\, \mathcal{P}(T)|$.

**Proposition.** For 1-labeled trees $S, T$ on the same label set,

$$\tfrac12\, \mathrm{RF}(S,T) \ \le\ d_{\mathrm{gnni}}(S,T) \ \le\ \mathrm{RF}(S,T),$$

with strict inequality on the right when $S \ne T$.

## Depends on

- [Robinson–Foulds distance](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

A gNNI on $e$ destroys exactly the bipartition $P(e)$ and creates exactly one new one, so each move changes $\mathcal{P}$ by a symmetric difference of size two, and the triangle inequality for $\triangle$ gives the lower bound. For the upper bound, cutting the $m$ shared edges splits both trees into $m+1$ pairs of subtrees on the same label sets; a two-node pair needs one gNNI, and a pair with $o_j \ge 3$ nodes is turned into a star around a common internal label and then into the target with at most $2o_j - 5$ moves. Summing, using $|\mathcal{P}(S)\triangle\mathcal{P}(T)| + 2m = 2n - 2$, gives at most $2n - 2m - 2 - m_2 - 3m_3 \le \mathrm{RF}(S,T)$ moves, where $m_2, m_3$ count the two-node and larger pairs.

## Sources

- K. Jahn, N. Beerenwinkel and L. Zhang, "The Bourque distances for mutation trees of cancers", Algorithms for Molecular Biology 16 (2021), Definition 1 and the gNNI–RF proposition, <https://doi.org/10.1186/s13015-021-00188-3>, PMCID: PMC8193869.
