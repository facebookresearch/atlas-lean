# Modal logics of topological relations

The modal logic of the RCC8 relations over a class of region structures has one box for each of the eight Egenhofer–Franzosa relations between regions (disconnected, externally connected, partial overlap, equal, and the four proper-part relations); a formula is valid if it is true at every region of every model.

**Regions and relations.** For a topological space $\mathfrak{T} = (U, \mathbb{I})$ with interior operator $\mathbb{I}$ and closure $\mathbb{C}$, a set $s \subseteq U$ is *regular closed* if $\mathbb{C}\mathbb{I}(s) = s$. Standard choices of regions are $\mathfrak{T}_{\mathrm{reg}}$, all nonempty regular closed subsets; $\mathbb{R}^n_{\mathrm{conv}}$, the nonempty convex regular closed subsets of $\mathbb{R}^n$; and $\mathbb{R}^n_{\mathrm{rect}}$, the closed hyper-rectangles $\prod_{i=1}^n C_i$ with each $C_i$ a non-singleton closed interval. On a set $W$ of regions the RCC8 relations are: $\mathrm{dc}$ iff $s \cap t = \varnothing$; $\mathrm{ec}$ iff $\mathbb{I}(s) \cap \mathbb{I}(t) = \varnothing \neq s \cap t$; $\mathrm{po}$ iff $\mathbb{I}(s) \cap \mathbb{I}(t) \neq \varnothing$, $s \not\subseteq t$ and $t \not\subseteq s$; $\mathrm{eq}$ iff $s = t$; $\mathrm{tpp}$ iff $s \subseteq t$, $s \not\subseteq \mathbb{I}(t)$ and $s \neq t$; $\mathrm{ntpp}$ iff $s \subseteq \mathbb{I}(t)$ and $s \neq t$; and $\mathrm{tppi}$, $\mathrm{ntppi}$ are the inverses. The *full concrete region structure* $\mathfrak{R}(\mathfrak{T}, W)$ is $W$ with these eight relations.

**Language and logics.** $\mathcal{L}_{\mathrm{RCC8}}$ extends propositional logic by boxes $[\mathrm{r}]$ for the eight relations, interpreted in the usual Kripke way over region models (a region structure with a valuation of the variables as sets of regions). For a class $\mathcal{S}$ of region structures, $L_{\mathrm{RCC8}}(\mathcal{S})$ is the set of formulas true at every region of every model on a structure of $\mathcal{S}$. The logics of full concrete structures studied are $L_{\mathrm{RCC8}}(\mathcal{TOP})$, over all $\mathfrak{R}(\mathfrak{T}, \mathfrak{T}_{\mathrm{reg}})$ for topological spaces $\mathfrak{T}$, and $L_{\mathrm{RCC8}}(\mathbb{R}^n, \mathbb{R}^n_{\mathrm{x}})$ for $\mathrm{x} \in \{\mathrm{reg}, \mathrm{conv}, \mathrm{rect}\}$ and $n \geq 1$.

## Depends on

- [Kripke model](../../kripke-semantics/kripke-model.md)
- [Topological space](../../../../Topology/topological-spaces/topological-space.md)
- [Interior of a subset](../../../../Topology/topological-spaces/open-and-closed-sets/interior-of-subset.md)
- [Closure of a subset](../../../../Topology/topological-spaces/open-and-closed-sets/closure-of-subset.md)
- [Convex set](../../../../Geometry/convex-geometry/convex-set.md)
## Proof depends on

None.

## Expansion

Since the eight relations are jointly exhaustive and pairwise disjoint, the language defines the difference modality $\bigwedge_{\mathrm{r} \neq \mathrm{eq}}[\mathrm{r}]$, hence the universal modality and nominals (formulas true at exactly one region). Variants restrict to bounded regions or to substructures of concrete region structures; the source also treats logics of all abstract region structures and of finite region structures.

## Sources

- C. Lutz and F. Wolter, "Modal logics of topological relations", *Logical Methods in Computer Science* 2(2), Paper 5, 2006, doi:10.2168/LMCS-2(2:5)2006; read as arXiv:cs/0605064v2, <https://arxiv.org/abs/cs/0605064v2>: Section 2 (topological spaces, regions and the RCC8 relations), Section 3 (the language and the definable difference and universal modalities) and Section 4 (the logics).
