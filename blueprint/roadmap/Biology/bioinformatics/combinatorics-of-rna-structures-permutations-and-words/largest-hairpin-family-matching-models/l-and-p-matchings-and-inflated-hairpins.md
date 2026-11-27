# L & P matchings as models of pseudoknotted RNA secondary structures

**Matchings.** An RNA secondary structure on a backbone of $2n$ bonded nucleotides is modelled by a complete matching $M$ on the points $1,\ldots,2n$ of a line; $\mathcal M(n)$ is the set of complete matchings with $n$ edges. Label the edges $1,\ldots,n$ by increasing left endpoint and write $i=(i_1,i_2)$ with $i_1<i_2$. Edges $i,j$ are *nested* if $i_1<j_1<j_2<i_2$ and *crossing* if $i_1<j_1<i_2<j_2$; $ne(M)$ and $cr(M)$ count nested and crossing pairs. A *hairpin* is a pair of edges with $j_1=i_1+1$, $j_2=i_2+1$, and a *ladder* is a sequence of pairwise nested edges. Matchings with $cr(M)=0$ are *noncrossing*; there are $C_n=\frac{1}{n+1}\binom{2n}{n}$ of them. The *LR-sequence* of $M$ records, left to right, whether each point is a left (L) or right (R) endpoint; $nc(M)$ is the unique noncrossing matching with the same LR-sequence.

**L & P matchings.** The class $\mathcal{LP}_n$, the most restrictive member of the Largest Hairpin Family of pseudoknot models, consists of the matchings built inductively from a single edge or a hairpin by (a) inflating an edge into a ladder or (b) inserting a noncrossing matching. An L & P matching either is noncrossing or contains a *maximal inflated hairpin*: two edge sets $A=\{a_1,\ldots,a_k\}$ (left side) and $B=\{b_1,\ldots,b_\ell\}$ such that edges within $A$, and within $B$, are pairwise nested, every edge of $A$ crosses every edge of $B$, and every crossing of $M$ is between $A$ and $B$. All other edges form noncrossing matchings inserted below the hairpin.

**Enumeration.**

$$|\mathcal{LP}_n| = 2\cdot 4^{n-1} - \frac{3n-1}{2n+2}\binom{2n}{n},$$

giving $1, 3, 12, 51, 218, \ldots$ for $n=1,2,3,\ldots$

**Lemma (rearranging an inflated hairpin).** If $M\in\mathcal{LP}_n$ contains the inflated hairpin $(A,B)$, the right endpoints of its edges appear in the order $a_k,\ldots,a_1,b_\ell,\ldots,b_1$, and permuting them to $b_\ell,\ldots,b_1,a_k,\ldots,a_1$ yields $nc(M)$, in which every pair of edges of $A\cup B$ is nested.

## Depends on

- [RNA secondary structure](../../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)

## Expansion

The inductive grammar forces all crossings to live in one inflated hairpin, which is why the class is so constrained: removing the crossings by reordering the right endpoints of the hairpin lands in a noncrossing matching with the same LR-sequence (a Dyck path), and the hairpin is recovered from the two largest labels $\max A$, $\max B$. This is the first half of the bijection with nesting-similarity classes.

## Sources

- Megan A. Martinez, Manda Riehl, "A bijection between the set of nesting-similarity classes and L & P matchings", Discrete Mathematics & Theoretical Computer Science 19(2) (2018), <https://doi.org/10.23638/dmtcs-19-2-1>. Published version of arXiv:1704.07902, cited next; locators there refer to the arXiv version.
- Megan A. Martinez and Manda Riehl, "A bijection between the set of nesting-similarity classes and L & P matchings", arXiv:1704.07902 (2017), Section 1 (definitions and enumeration), Section 2 (Definition 1, Lemma 1, Theorem 1), Section 3 (Lemmas 2-4, Theorems 2 and 3, Corollary 1), <https://doi.org/10.48550/arXiv.1704.07902>.
