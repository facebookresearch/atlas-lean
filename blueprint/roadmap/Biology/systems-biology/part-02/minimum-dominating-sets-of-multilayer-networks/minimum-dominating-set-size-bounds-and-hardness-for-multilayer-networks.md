# Size bounds and hardness of minimum dominating sets for multilayer networks

**Definitions.** For a graph $G = (V,E)$, $U \subseteq V$ is a dominating set if every $v \in V$ is in $U$ or adjacent to a vertex of $U$; a minimum dominating set (MDS) has least cardinality, the domination number $S_{\mathrm{MDS}}(G)$ of $G$. For a multiset $\mathcal G = \{G_i = (V_i, E_i) : i = 1,\dots,N\}$ of undirected graphs (layers) with $V = \bigcup_i V_i$, a set $U \subseteq V$ is a *dominating set for multilayer networks* (DSM) if

$$\forall i\ \forall v \in V_i:\quad v \in U \ \text{ or }\ \exists u \in U,\ \{u,v\} \in E_i .$$

A DSM of least cardinality is an MDSM, of size $S_{\mathrm{MDSM}}(\mathcal G)$. Choosing an MDSM as driver nodes, each able to control its links independently, makes every layer structurally controllable in the dominating-set framework.

**Proposition (bounds).**

$$\max_{i} S_{\mathrm{MDS}}(G_i) \ \le\ S_{\mathrm{MDSM}}(\mathcal G)\ \le\ \sum_{i=1}^N S_{\mathrm{MDS}}(G_i).$$

Both are attained: the lower bound when all layers are identical, the upper bound when the $V_i$ are pairwise disjoint.

**Proposition (many layers).** Let all layers share the node set $V$ with $|V| = n \ge d_{\min} + 1$, and suppose that for every node $v$ and every set $S$ of $d_{\min}$ other nodes some layer has $N(v) = S$. Then $S_{\mathrm{MDSM}}(\mathcal G) \ge n - d_{\min}$. (The source states this for "sufficiently many" layers of minimum degree $d_{\min}$ and large $n$; its proof uses exactly the hypothesis above, and without it the bound can fail, since a set $V \setminus W$ with $|W| = d_{\min} + 1$ dominates most graphs of minimum degree $d_{\min}$.)

**Theorem (hardness).** Computing an MDSM is NP-hard for two-layer networks even if each layer consists of cycles and at most one star, and for three-layer networks even if no layer contains a cycle. (For a single forest an MDS is computable in polynomial time, so adding layers turns easy cases hard.)

## Depends on

- [Dominating set](../../../../GraphTheory/independence-and-domination/dominating-sets/is-dominating.md)
- [Domination number](../../../../GraphTheory/independence-and-domination/dominating-sets/domination-number.md)

## Expansion

An MDSM dominates each layer, so it is at least as large as each single-layer MDS; conversely, the union of one MDS per layer dominates every layer. If the layers are equal the two notions coincide, and if their node sets are disjoint no node can serve two layers. For $k$-regular random layers a recursive probabilistic (mean-field type) estimate, generalizing the single-graph analysis, predicts MDSM sizes far below the sum bound, and on 70 genome-scale metabolic networks the MDSM of several species is not much larger than a single-species MDS. The hardness proofs reduce from 3-SAT restricted to instances in which each variable occurs at most three times, at least once positively and once negatively, encoding the clauses in the layers, since each layer alone is easy.

## Sources

- J. C. Nacher, M. Ishitsuka, S. Miyazaki, T. Akutsu, "Finding and analysing the minimum set of driver nodes required to control multilayer networks", Scientific Reports 9 (2019), Propositions 1–2 and Theorems 3–4 (proofs in the Supplementary Information), <https://doi.org/10.1038/s41598-018-37046-z>, PMCID PMC6345816.
