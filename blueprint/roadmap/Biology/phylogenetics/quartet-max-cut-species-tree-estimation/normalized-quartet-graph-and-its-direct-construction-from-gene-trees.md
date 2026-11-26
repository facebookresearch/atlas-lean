# Normalized quartet graph and its direct construction from gene trees

**Quartet graph.** Let $\mathcal T$ be a set of $k$ unrooted gene trees on $n$ species. A quartet $A,B|C,D$ is displayed by a tree if its restriction to those four leaves has that topology; $w_{\mathcal T}(q)$ is the number of gene trees displaying $q$. For a taxon set $\mathcal X$ (a subproblem), the *quartet graph* consists of two complete weighted graphs $\mathcal B$ (bad edges) and $\mathcal G$ (good edges) on vertices in bijection with $\mathcal X$. Each quartet $A,B|C,D$ adds its weight to the bad edges $(A,B), (C,D)$ joining siblings and to the four good edges $(A,C), (A,D), (B,C), (B,D)$. A bipartition of $\mathcal X$ is chosen as a cut $\mathcal C$ maximizing

$$\sum_{(X,Y) \in \mathcal C} \bigl(\mathcal G[X,Y] - \alpha\, \mathcal B[X,Y]\bigr),$$

with $\alpha > 0$ tuned by binary search; recursing on both sides (each side gaining an *artificial taxon* standing for the other) yields the species tree.

**Normalization.** An artificial taxon $M$ represents a set of species, and a quartet on taxa $M, N, O, P$ is weighted by

$$f(M,N|O,P) = \sum_{m \in M,\, n \in N,\, o \in O,\, p \in P} I(m)I(n)I(o)I(p)\, w_{\mathcal T}(m,n|o,p),$$

with species importance values summing to one within each taxon, so that each gene tree casts one vote per subset of four taxa. In the hierarchical scheme, if $T_Z$ is the rooted tree recording how the species of $Z$ were successively merged into artificial taxa, then $I(z) = \prod_{v \in \mathrm{path}(T_Z, z)} 1/\mathrm{outdeg}(v)$, down-weighting species each time they are relabeled.

**Result.** The normalized good and bad edge weights can be computed directly from the gene trees by dynamic programming over each tree, without enumerating the $\Theta(n^4)$ quartets; for example, the total weight of taxon pairs below a vertex $u$, $\sum_{z \ne w \in L(u)} I(z) I(w)$, is a single dynamic-programming quantity $g_0[u]$, and for singletons $X, Y$ the sum $\mathcal G[X,Y] + \mathcal B[X,Y]$ is a closed form in root quantities. With a perfectly balanced subproblem decomposition the whole method runs in $O(n^3 k)$ time.

## Expansion

Siblings in a displayed quartet should stay on the same side of the split and non-siblings should be separated, which is what the cut objective rewards. Without normalization, quartets involving artificial taxa receive inflated weights from a single gene tree, which distorts later splits; normalized weights restore one vote per gene tree and improved accuracy in simulations. Graph construction dominates the cost of each subproblem, so the direct construction controls the overall running time.

## Sources

- Y. Han and E. K. Molloy, "Improving quartet graph construction for scalable and accurate species tree estimation from gene trees", *Genome Research* (2023), Review of wQMC, Eqs. (1)–(5), Lemmas 1–2 (Eqs. 14–15) and the complexity statements referring to Theorems 1–3 of its Supplemental Materials. <https://doi.org/10.1101/gr.277629.122> (PMC10538498)
