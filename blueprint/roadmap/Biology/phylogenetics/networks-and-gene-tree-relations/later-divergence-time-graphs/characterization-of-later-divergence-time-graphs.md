# Characterization of later-divergence-time graphs

**Relaxed scenarios.** A relaxed scenario $\mathcal{S} = (T, S, \sigma, \mu, \tau_T, \tau_S)$ consists of a planted gene tree $T$ with leaf set $L$, a planted species tree $S$ with leaf set $M$, a coloring $\sigma : L \to M$ assigning each gene to its species, a reconciliation map $\mu$ from $T$ into $S$ (leaves to leaves, compatible with $\sigma$), and time maps $\tau_T, \tau_S$ that decrease from root to leaves, agree on leaves ($\tau_T(x) = \tau_S(\sigma(x))$), and are time-consistent with $\mu$. This framework contains the usual duplication–transfer–loss scenarios. For genes $a, b$ let their divergence time be $\tau_T(\mathrm{lca}_T(a,b))$ and the divergence time of their species $\tau_S(\mathrm{lca}_S(\sigma(a), \sigma(b)))$.

**LDT graph.** The **later-divergence-time graph** $G_<(\mathcal{S})$ has vertex set $L$ and an edge $ab$ whenever

$$\tau_T(\mathrm{lca}_T(a,b)) < \tau_S(\mathrm{lca}_S(\sigma(a), \sigma(b))),$$

i.e. the two genes diverged after their species did. A vertex-colored graph $(G, \sigma)$ is an LDT graph if $G = G_<(\mathcal{S})$ for some relaxed scenario.

For a colored graph $(G = (L,E), \sigma)$ define the **color triple set**

$$\mathcal{S}(G,\sigma) = \{\sigma(x)\sigma(y) \,|\, \sigma(z) : \sigma(x), \sigma(y), \sigma(z) \text{ pairwise distinct},\ xz, yz \in E,\ xy \notin E\}.$$

A set of rooted triples is **compatible** if some tree displays all of them. A **cograph** is a graph with no induced path on four vertices.

**Theorem.** A vertex-colored graph $(G, \sigma)$ is an LDT graph if and only if it is a properly colored cograph and $\mathcal{S}(G, \sigma)$ is compatible.

**Corollaries.**
1. LDT graphs can be recognized in polynomial time, and an explaining relaxed scenario can be constructed in polynomial time.
2. Being an LDT graph is hereditary: every vertex-induced subgraph of an LDT graph is an LDT graph.
3. If $(G, \sigma)$ is an LDT graph, then for every planted species tree $S$ on $M$ that displays $\mathcal{S}(G, \sigma)$ there is a relaxed scenario with species tree $S$ explaining $(G, \sigma)$; every explaining species tree displays $\mathcal{S}(G,\sigma)$, and every explaining gene tree displays the triples $xy|z$ with $xy \in E$, $xz, yz \notin E$.

## Expansion

Genes of the same species diverge no later than their species (a leaf), so there are no monochromatic edges and the coloring is proper. If $xz, yz \in E$ but $xy \notin E$ for three distinct species, the species of $x$ and $y$ must be closer to each other than to that of $z$, which forces the color triple into every explaining species tree; incompatible triples therefore rule out LDT graphs. Induced $P_4$s are excluded because the relation "diverged later than the species" is determined by comparing two ultrametric-like time functions along the two trees, which yields a cotree structure. For sufficiency, a recursive construction (Algorithm 1) builds the gene tree from the cotree of $G$ and the species tree from a tree displaying $\mathcal{S}(G,\sigma)$, then chooses time maps so that exactly the edges of $G$ satisfy the later-divergence inequality.

## Sources

- D. Schaller, M. Lafond, P. F. Stadler, N. Wieseke, M. Hellmuth, "Indirect identification of horizontal gene transfer", Journal of Mathematical Biology (2021), Definitions 8 and 10, Theorem 1, Proposition 3, Lemmas 6–8, Theorems 2–3 and Corollaries 2–4, <https://doi.org/10.1007/s00285-021-01631-0>, PMCID PMC8254804.
