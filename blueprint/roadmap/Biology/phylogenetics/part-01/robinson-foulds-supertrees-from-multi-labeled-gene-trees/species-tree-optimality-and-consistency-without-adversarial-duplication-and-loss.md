# Species-tree optimality and consistency without adversarial duplication and loss

**Setting.** Gene families evolve inside a rooted binary species tree $T^*$ on species set $S$ under a *generic* gene duplication and loss (GDL) model: each gene has its own duplication and loss probabilities on each species-tree edge, all strictly less than $1$, and genes need not be identically distributed. A bipartition $A|B$ of a subset $S_0 \subseteq S$ is *compatible* with $T^*$ if some bipartition $A'|B'$ of $T^*$ satisfies $A \subseteq A'$ and $B \subseteq B'$. *Adversarial GDL* occurs when some gene-family tree (a multree) induces a bipartition incompatible with $T^*$; for example, a duplication followed by complementary losses in the two copies can leave a singly-labeled gene tree with a wrong split.

**Results.**

1. (Loss only.) If genes evolve with losses but no duplications, every bipartition induced by a gene-family tree is compatible with $T^*$.
2. (Duplication only.) If genes evolve with duplications but no losses, then $C(M) \subseteq C(T^*)$ for every gene-family tree $M$: an internal edge is collapsed in forming $M_X$ exactly when it lies below a duplication node of the rooted gene tree, and every edge with no duplication above it reproduces a species-tree bipartition.
3. (Optimality.) If no adversarial GDL occurs in the input profile $\mathcal{P}$, then $T^*$ is an optimal solution of the [RFS-multree problem](reduction-of-the-rf-supertree-problem-for-multi-labeled-trees.md) for $\mathcal{P}$.
4. (Consistency.) FastMulRFS, which solves the RF supertree problem for $\mathcal{P}_X$ exactly within the space of trees whose bipartitions lie in a set $\Sigma$ of bipartitions drawn from the input trees, is statistically consistent under any generic GDL model in which adversarial GDL has probability zero: as the number of gene families grows, it returns $T^*$ with probability tending to $1$.

The source conjectures (Conjecture 7) that consistency persists when adversarial GDL has sufficiently small positive probability.

## Depends on

- [Reduction of the Robinson–Foulds supertree problem for multi-labeled trees](reduction-of-the-rf-supertree-problem-for-multi-labeled-trees.md)

## Expansion

By the reduction, a candidate's score is the number of input bipartitions it displays. Without adversarial GDL every input bipartition is compatible with $T^*$, so $T^*$ displays all of them and attains the maximum possible score. For consistency, each gene independently has positive probability of undergoing no duplication or loss on any edge, in which case its tree equals $T^*$; with many genes, $\Sigma$ therefore contains $C(T^*)$ with probability tending to $1$, and the constrained dynamic program over $\Sigma$ recovers an optimal tree. Loss-only evolution never creates multiple copies, so gene trees are restrictions of $T^*$; duplication-only evolution keeps every species below a duplication on both sides of the edges beneath it, so those edges are collapsed.

## Sources

- E. K. Molloy and T. Warnow, "FastMulRFS: fast and accurate species tree estimation under generic gene duplication and loss models", Bioinformatics 36 (Suppl. 1) (2020), i57–i65, Section 3, Lemmas 3 and 4, Theorems 5 and 6 and Conjecture 7. <https://doi.org/10.1093/bioinformatics/btaa444> PMCID: PMC7355287.
