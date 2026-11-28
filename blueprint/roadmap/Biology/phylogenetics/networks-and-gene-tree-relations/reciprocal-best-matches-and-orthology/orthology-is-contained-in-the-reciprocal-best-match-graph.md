# Orthology is contained in the reciprocal best match graph

**Setting.** Let $S = (W, F)$ (species tree) and $T = (V, E)$ (gene tree) be planted phylogenetic trees with leaf sets $L(S)$ and $L(T)$, and let $\sigma : L(T) \to L(S)$ be surjective, assigning each gene to its species. A **reconciliation** from $(T, \sigma)$ to $S$ is a map $\mu : V \to W \cup F$ such that (R0) $\mu(x)$ is the planted root $0_S$ iff $x = 0_T$; (R1) $\mu(x) = \sigma(x)$ for leaves $x$; (R2) $x \prec_T y$ implies $\mu(x) \preceq_S \mu(y)$; and (R3) whenever $\mu(x)$ is an inner vertex of $S$, (i) $\mu(x) = \mathrm{lca}_S(\mu(v'), \mu(v''))$ for at least two distinct children $v', v''$ of $x$, and (ii) $\mu(v')$, $\mu(v'')$ are incomparable in $S$ for any two distinct children of $x$. The induced event labeling $t_\mu$ marks an inner vertex $x$ of $T$ as a speciation ($t_\mu(x) = \bullet$) if $\mu(x)$ is an inner vertex of $S$ and as a duplication ($t_\mu(x) = \square$) if $\mu(x)$ lies on an edge of $S$. Two genes $x, y$ are **orthologs**, $xy \in \Theta(T, t_\mu)$, iff $t_\mu(\mathrm{lca}_T(x, y)) = \bullet$.

For genes $x, y$ with $\sigma(x) \ne \sigma(y)$, $y$ is a **best match** of $x$ if $\mathrm{lca}_T(x, y) \preceq_T \mathrm{lca}_T(x, y')$ for every $y'$ with $\sigma(y') = \sigma(y)$; $x$ and $y$ are **reciprocal best matches** if each is a best match of the other. The **reciprocal best match graph** (RBMG) $G(T, \sigma)$ has vertex set $L(T)$ and an edge for every reciprocal best match pair.

**Theorem 2.** If $xy \in \Theta(T, t_\mu)$ for some reconciliation $\mu$ of $(T, \sigma)$ to $S$, then $x$ and $y$ are reciprocal best matches in $(T, \sigma)$. Hence the orthology graph $\Theta(T, t_\mu)$ is a spanning subgraph of the RBMG, and in duplication/loss scenarios reciprocal best matches produce no false-negative orthology assignments.

**Theorem 4 (no losses).** If moreover $(T, t_\mu, \sigma)$ contains no gene losses, then the RBMG $G(T, \sigma)$ equals the colored orthology cograph $(\Theta(T, t_\mu), \sigma)$, and the unique discriminating cotree of this cograph explains the RBMG.

## Expansion

If $v = \mathrm{lca}_T(x, y)$ is a speciation, the speciation constraint (R3) sends the children of $v$ containing $x$ and $y$ to incomparable subtrees of $S$, so no gene of species $\sigma(y)$ can sit in the child subtree containing $x$ (and symmetrically); every competitor $y'$ of the color of $y$ therefore satisfies $\mathrm{lca}_T(x, y') \succeq v$, which is the best-match condition in both directions. Without losses, every duplication vertex has both child subtrees covering the same species set, so for an RBMG edge $ab$ whose lca were a duplication there would be a same-colored competitor strictly below the lca, a contradiction; thus every RBMG edge is an orthology edge. Orthology relations of reconciled gene trees are cographs (no induced $P_4$), which gives the cotree statement.

## Sources

- M. Geiß, M. E. González Laffitte, A. López Sánchez, D. I. Valdivia, M. Hellmuth, M. Hernández Rosales, P. F. Stadler, "Best match graphs and reconciliation of gene trees with species trees", Journal of Mathematical Biology (2020), Definition 3, Theorems 2 and 4, Observation 1, <https://doi.org/10.1007/s00285-020-01469-y> (PMC7052050).
