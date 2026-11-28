# Reconciliation maps for event-labeled gene trees

**Setting.** Let $T=(V,E)$ be a rooted phylogenetic gene tree on a gene set $G$, $S=(W,F)$ a rooted species tree on a species set, and $\sigma:G\to$ species the assignment of genes to the species they reside in. An event labeling $t:V\cup E\to\{\bullet,\square,\triangle,\odot\}\cup\{0,1\}$ marks each inner vertex as a speciation ($\bullet$), duplication ($\square$) or horizontal gene transfer ($\triangle$), each leaf by $\odot$, and each edge as a transfer edge ($t(e)=1$) or not ($t(e)=0$). As in the source, $S$ is augmented by a new root $\rho_S$ and the edge $(\rho_S,\operatorname{lca}_S(S))$, so $F$ contains this edge; $\preceq_S$ is extended to $W\cup F$ by $x\prec_S(u,v)$ iff $x\preceq_S v$, $(u,v)\prec_S x$ iff $u\preceq_S x$, and $(u,v)\preceq_S(a,b)$ iff $v\preceq_S b$. Write $T_{\bar E}$ for the forest obtained by deleting all transfer edges, and $\sigma_{T_{\bar E}}(v)$ for the set of species of the leaves below $v$ in $T_{\bar E}$.

**Definition.** A map $\mu:V\to W\cup F$ is a reconciliation map from $(T;t,\sigma)$ to $S$ if for all $v\in V$:

- (M1) if $t(v)=\odot$ then $\mu(v)=\sigma(v)$;
- (M2) (i) if $t(v)=\bullet$ then $\mu(v)=\operatorname{lca}_S(\sigma_{T_{\bar E}}(v))$; (ii) if $t(v)\in\{\square,\triangle\}$ then $\mu(v)\in F$ is an edge of $S$; (iii) if $t(v)=\triangle$ and $(v,w)\in E$ is a transfer edge then $\mu(v)$ and $\mu(w)$ are incomparable in $S$;
- (M3) for $v\prec_{T_{\bar E}} w$: if $t(v),t(w)\in\{\square,\triangle\}$ then $\mu(v)\preceq_S\mu(w)$, and otherwise $\mu(v)\prec_S\mu(w)$.

$S$ is called a species tree for $(T;t,\sigma)$ if such a $\mu$ exists.

**Theorem.** For a binary gene tree $(T;t,\sigma)$ and a binary species tree $S$, a duplication–transfer–loss (DTL) scenario exists if and only if a reconciliation map in the above sense exists.

## Expansion

Speciation vertices are pinned to the lca of the species they cover once transfer edges are cut, while duplications and transfers sit on edges of $S$, and the ancestor constraint keeps the vertical (non-transfer) descent of $T$ inside the ancestor order of $S$. Condition (M2.iii) is what makes a transfer move a lineage sideways into an incomparable branch. In the binary case these axioms are a case-by-case reformulation of the usual DTL-scenario map $\gamma:V\to W$ (vertices sent to the head of their image edge); the axioms also admit biologically plausible non-binary reconciliations that no DTL scenario represents. Nothing in the axioms prevents a transfer from landing in a branch that ends before the donor branch began; that is the separate question of time-consistency.

## Sources

- N. Nøjgaard, M. Geiß, D. Merkle, P. F. Stadler, N. Wieseke, M. Hellmuth, "Time-consistent reconciliation maps and forbidden time travel", *Algorithms for Molecular Biology* 13:2 (2018), Definition 2 and Theorem 1, <https://doi.org/10.1186/s13015-018-0121-8>, PMCID: PMC5800358.
