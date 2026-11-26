# LDT edges certify horizontal transfer, and rs-Fitch graphs

**Relaxed scenarios.** A relaxed scenario $\mathcal{S} = (T, S, \sigma, \mu, \tau_T, \tau_S)$ consists of a planted gene tree $T$ with leaf set $L$, a planted species tree $S$ with leaf set $M$, a coloring $\sigma : L \to M$ assigning each gene to its species, a reconciliation map $\mu$ from $T$ into $S$ (leaves to leaves, compatible with $\sigma$), and time maps $\tau_T, \tau_S$ that decrease from root to leaves, agree on leaves ($\tau_T(x) = \tau_S(\sigma(x))$), and are time-consistent with $\mu$. This framework contains the usual duplication–transfer–loss scenarios. For genes $a, b$ let their divergence time be $\tau_T(\mathrm{lca}_T(a,b))$ and the divergence time of their species $\tau_S(\mathrm{lca}_S(\sigma(a), \sigma(b)))$.

**LDT graph.** The **later-divergence-time graph** $G_<(\mathcal{S})$ has vertex set $L$ and an edge $ab$ whenever

$$\tau_T(\mathrm{lca}_T(a,b)) < \tau_S(\mathrm{lca}_S(\sigma(a), \sigma(b))),$$

i.e. the two genes diverged after their species did. A vertex-colored graph $(G, \sigma)$ is an LDT graph if $G = G_<(\mathcal{S})$ for some relaxed scenario.

An edge of $T$ is a **transfer edge** if $\mu$ maps its endpoints to incomparable parts of $S$ (a horizontal transfer). The **Fitch graph** $\digamma(\mathcal{S})$ has vertex set $L$ and an edge $xy$ whenever the path between $x$ and $y$ in $T$ contains a transfer edge, i.e. $x$ and $y$ are xenologs. A colored graph is an **rs-Fitch graph** if it equals $\digamma(\mathcal{S})$ for some relaxed scenario.

**Theorem (LDT edges imply transfer).** If $(G, \sigma)$ is an LDT graph, then $G \subseteq \digamma(\mathcal{S})$ for every relaxed scenario $\mathcal{S}$ that explains $(G,\sigma)$. In particular a relaxed scenario without transfer edges has an edgeless LDT graph.

**Theorem (rs-Fitch graphs).** A colored graph $(G, \sigma)$ is an rs-Fitch graph if and only if (i) $G$ is complete multipartite with independent sets $\mathcal{I} = \{I_1, \dots, I_k\}$, and (ii) if $k > 1$, there is $I' \in \mathcal{I}$ such that the auxiliary graph $A_\digamma(\sigma, \mathcal{I} \setminus \{I'\})$ on the colors is disconnected. Hence rs-Fitch graphs are recognizable in polynomial time and form a hereditary class.

**Theorem (when LDT and Fitch coincide).** The following are equivalent: $(G, \sigma)$ is a properly colored complete multipartite graph; there is a relaxed scenario with $G = G_<(\mathcal{S}) = \digamma(\mathcal{S})$; $(G, \sigma)$ is complete multipartite and an LDT graph; $(G, \sigma)$ is properly colored and an rs-Fitch graph.

## Expansion

If genes $a, b$ diverged strictly after their species, then the gene lineages leading to $a$ and $b$ cannot both have followed the species tree vertically from $\mathrm{lca}_T(a,b)$, because vertical descent would place $\mathrm{lca}_T(a,b)$ at or above $\mathrm{lca}_S(\sigma(a),\sigma(b))$ in time; some lineage on the path must jump between incomparable species branches. This is the formal justification for indirect HGT inference from anomalously small gene distances, valid regardless of duplications and losses. The converse fails: transfers between closely related lineages or followed by losses can leave no LDT edge, so LDT graphs capture only part of the xenology relation, which is fully described by rs-Fitch graphs. Simulations show that greedy cograph editing of estimated LDT graphs recovers a substantial fraction of transfer events.

## Depends on

- [Characterization of later-divergence-time graphs](characterization-of-later-divergence-time-graphs.md)

## Sources

- D. Schaller, M. Lafond, P. F. Stadler, N. Wieseke, M. Hellmuth, "Indirect identification of horizontal gene transfer", Journal of Mathematical Biology (2021), Section 5 (Theorem 4, Corollary 6, Theorem 5) and Section 6 (Theorem 6, Corollaries 9 and 14), <https://doi.org/10.1007/s00285-021-01631-0>, PMCID PMC8254804.
