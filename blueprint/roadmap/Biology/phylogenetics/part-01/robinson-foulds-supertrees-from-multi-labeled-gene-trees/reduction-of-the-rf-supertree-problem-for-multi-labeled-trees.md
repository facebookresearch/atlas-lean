# Reduction of the Robinson–Foulds supertree problem for multi-labeled trees

**Definitions.** A multi-labeled tree (multree) $M$ is an unrooted tree whose leaves are labeled by species from a set $S$, a label possibly appearing on several leaves (gene copies). An edge of $M$ *induces a bipartition* of its label set when no label occurs on both sides of it; $C(M)$ is the set of induced bipartitions. For a singly-labeled tree $T$ on $S$ and a singly-labeled tree $T'$ on $R \subseteq S$, the [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md) is $RF(T, T') = |C(T|_R) \,\triangle\, C(T')|$, where $T|_R$ is $T$ restricted to $R$. For a multree, $RF(T, M)$ is the contraction–refinement edit distance between $M$ and the extension $\mathrm{Ext}(T, M)$ of $T$ that replaces each leaf by as many copies as $M$ has. Given a profile $\mathcal{P}$ of multrees, the *RFS-multree problem* asks for a binary tree $T$ bijectively labeled by $S$ minimizing $\sum_{M \in \mathcal{P}} RF(\mathrm{Ext}(T, M), M)$.

**Reduction.** For $M \in \mathcal{P}$, let $X(M)$ collapse every internal edge of $M$ that has some label on both sides, and let $M_X = R(X(M))$ delete all but one leaf of each label; $M_X$ is a (possibly non-binary) singly-labeled tree on the labels $S_M$ of $M$. Put $\mathcal{P}_X = \{M_X : M \in \mathcal{P}\}$.

**Theorem.** A binary singly-labeled tree $T$ on $S$ is an optimal RFS-multree supertree for $\mathcal{P}$ if and only if it is an optimal Robinson–Foulds supertree for $\mathcal{P}_X$; equivalently, if and only if $T$ maximizes

$$\sum_{M \in \mathcal{P}} \bigl| C(T|_{S_M}) \cap C(M) \bigr|.$$

Consequently any exact or heuristic RF-supertree method applies to gene-family trees with duplications after this linear-size preprocessing; $\mathcal{P}_X$ can be computed in $O(mnk)$ time for $k$ multrees with at most $m$ leaves on $n$ species.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

An edge of $M$ with a label on both sides cannot match any edge of $\mathrm{Ext}(T, M)$ for any singly-labeled $T$, since every non-trivial edge of the extension separates whole label classes; such edges contribute the same constant to every candidate's score and can be collapsed. After collapsing, all copies of a label sit on the same side of every remaining edge, so keeping one copy changes neither $C(M)$ nor the matching. Terminal edges of the extension exist for every candidate. What remains depends on $T$ only through the shared bipartitions $|C(T|_{S_M}) \cap C(M)|$, which gives the equivalence.

## Sources

- E. K. Molloy and T. Warnow, "FastMulRFS: fast and accurate species tree estimation under generic gene duplication and loss models", Bioinformatics 36 (Suppl. 1) (2020), i57–i65, Sections 2.2–2.4, Definition 1 and Theorem 2 (with Lemma 13 of its appendix). <https://doi.org/10.1093/bioinformatics/btaa444> PMCID: PMC7355287.
- R. Chaudhary and others, "Inferring species trees from incongruent multi-copy gene trees using the Robinson-Foulds distance", Algorithms for Molecular Biology 8 (2013), 28.
