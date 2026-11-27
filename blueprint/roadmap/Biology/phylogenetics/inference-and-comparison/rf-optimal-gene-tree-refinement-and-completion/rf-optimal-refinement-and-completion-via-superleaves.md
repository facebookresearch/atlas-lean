# RF-optimal refinement and completion via superleaves

**Problem (RF-OTRC).** Given a binary reference (species) tree $T$ on $S$ and an unrooted singly-labelled gene tree $t$ on $R\subseteq S$, possibly non-binary and missing taxa, find a binary tree $T'$ on $S$ with $T'|_R$ refining $t$ that minimizes $\mathrm{RF}(T',T)$.

**Superleaves.** The backbone of $T$ with respect to $t$ is the set of edges on paths between leaves of $R$. Deleting it splits $T$ into pieces; those containing taxa of $S\setminus R$ are superleaves. A superleaf is of **Type I** if the backbone edge it hangs from is shared by $T|_R$ and $t$, and of **Type II** otherwise. For binary $t$, the minimum RF distance achievable by adding the missing taxa is

$$\mathrm{RF}(T,T')=\mathrm{RF}(T|_R,t)+2m,\qquad m=\#\text{Type II superleaves}\quad\text{(Equation 1)}.$$

**Lemma 1 / Theorem 3 (TRACTION).** First refine $t$ to a binary $t^*$ containing every bipartition of $T|_R$ compatible with $t$ (RF-optimal refinement); then add the missing taxa with any exact RF-optimal completion method. The result solves RF-OTRC, in $O(n^{1.5}\log n)$ time with a linear-time completion step or $O(n^2)$ with the quadratic one, where $n=|S|$.

**Theorem 4 (multi-labelled gene trees).** For a gene-family MUL-tree $R$ and a singly-labelled species tree $T$, replace each leaf $s$ of $T$ by a star with as many copies of $s$ as $R$ has (the extension $\mathrm{Ext}(T,R)$), relabel the copies consistently in both trees, apply the refinement step and drop the indices. This returns a binary refinement of $R$ of minimum RF distance to $\mathrm{Ext}(T,R)$ in $O(|R|^{1.5}\log|R|)$ time.

## Depends on

- [RF-optimal refinement adds all compatible bipartitions](rf-optimal-refinement-adds-all-compatible-bipartitions.md)
- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

Equation 1 splits the completed distance into the restricted disagreement and a penalty of two per Type II superleaf. The refinement step minimizes the first term; it also minimizes the second, because a Type II superleaf can only become Type I when refinement creates a new shared edge at its attachment point, and all potentially shared edges are mutually compatible and are added together. The running time is dominated by $O(|R|^{0.5}\log|R|)$-time compatibility tests for each of the $O(|R|)$ edges of $T|_R$. For MUL-trees, consistent full differentiation preserves RF distance, which reduces the problem to the singly-labelled case.

## Sources

- S. Christensen, E. K. Molloy, P. Vachaspati, A. Yammanuru, T. Warnow, "Non-parametric correction of estimated gene trees using TRACTION", Algorithms for Molecular Biology 15:1 (2020), Equation 1, Definition 1, Theorem 2 (restating the completion result), Lemma 1, Theorem 3, Definitions 2–3 and Theorem 4, <https://doi.org/10.1186/s13015-019-0161-8>, PMCID: PMC6942343.
