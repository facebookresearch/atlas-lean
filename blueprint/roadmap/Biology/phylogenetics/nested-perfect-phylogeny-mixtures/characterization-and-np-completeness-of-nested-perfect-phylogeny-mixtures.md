# Characterization and NP-completeness of nested perfect phylogeny mixtures

**Setting.** Let $F \in [0,1]^{n \times m}$ give, for each of $n$ cells, the fraction $f_{i,j}$ of its mitochondrial genomes carrying mitochondrial mutation $j$. Mitochondrial mutations obey the infinite-sites assumption; each cell carries several mitochondrial clones; a clone, once it arises in a cell, is never lost and is inherited by both daughters at division. Then a factorization $F = UB$ into a mixture matrix $U$ (clone proportions per cell, rows summing to $1$) and a clone matrix $B$ (a perfect phylogeny matrix for a **mitochondrial clone tree** $S$) must satisfy two further constraints: the binarization $U'$ of $U$ ($u'_{i,\ell} = 1$ iff $u_{i,\ell} > 0$) is itself a perfect phylogeny matrix, defining a **cell lineage tree** $T$ whose edges are labelled by the clones arising on them; and $T$ and $S$ are **concordant**, i.e. the partial order on clones induced by $T$ extends the one induced by $S$ (a clone can only arise in a cell already containing its parent clone). The **exact nested perfect phylogeny mixture (ENPPM) problem** asks for such a factorization.

Let $G$ be the ancestry graph of $F$ (vertices $0,\dots,m$; edge $(j,j')$ iff $j = 0$ or $f_{i,j} \ge f_{i,j'}$ for all $i$) and $\delta^+_H(j)$ the children of $j$ in an arborescence $H$.

1. **Characterization.** $F$ admits a solution to the ENPPM problem if and only if (i) the binarization $F'$ of $F$ is a perfect phylogeny matrix, and (ii) $G$ has a spanning arborescence $H$ rooted at $0$ such that for all cells $i$ and clones $j$,

$$f_{i,j} > \sum_{j' \in \delta^+_H(j)} f_{i,j'} \ \text{ if } f_{i,j} > 0, \qquad \sum_{j' \in \delta^+_H(j)} f_{i,j'} = 0 \ \text{ if } f_{i,j} = 0.$$

2. **Complexity.** The ENPPM problem is NP-complete, even with $n = 2$ cells.

Condition (i) can be checked in polynomial time, so the hardness lies in finding an arborescence meeting the strict sum condition (ii).

## Depends on

- [Perfect phylogeny mixture and the sum condition](perfect-phylogeny-mixture-and-the-sum-condition.md)

## Expansion

Compared with the plain perfect phylogeny mixture condition $f_{i,j} \ge \sum_{\delta^+_H(j)} f_{i,j'}$, nesting forces every mutation present in a cell to be carried by a clone with positive proportion in that cell ($u_{i,j} > 0$ whenever $f_{i,j} > 0$), which turns the sum condition strict; it also forces the support pattern of $U$, hence of $F$, to be laminar, which is condition (i). Concordance follows because the clone present in a cell, together with all its ancestors, appears along the cell's lineage. Membership in NP is immediate (a candidate $H$ is checked in polynomial time); NP-hardness is proved by a reduction from Subset Sum, the strict sum condition making the choice of children for a vertex behave like the choice of a subset with a prescribed total. The structure parallels gene trees nested in species trees under the multispecies coalescent, with mitochondrial clones playing the role of alleles and cells the role of species. Noisy data are handled by minimizing $\|F - UB\|_1$ under the same constraints with a mixed integer linear program.

## Sources

- P. Sashittal, V. Chen, A. Pasarkar, B. J. Raphael, "Joint inference of cell lineage and mitochondrial evolution from single-cell sequencing data", *Bioinformatics* (2024), Sections 2–4 (Definition 1, Problems 2.2–2.3, Theorems 2–3), <https://doi.org/10.1093/bioinformatics/btae231> (PMC11211840).
