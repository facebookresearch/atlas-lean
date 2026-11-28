# The $A_2$-alignment of a binary tree has that tree as its unique maximum parsimony tree

**Setting.** Let $X=\{1,\ldots,n\}$ and let $T$ be an unrooted binary phylogenetic $X$-tree (all inner vertices of degree 3), with split set $\Sigma(T)$, $|\Sigma(T)| = 2n-3$. A binary character is a map $f: X \to \{a,b\}$; a character and its complement are identified (they induce the same $X$-split). The parsimony score $l(f,T)$ is the minimum number of edges $\{u,v\}$ with $g(u)\neq g(v)$ over all extensions $g$ of $f$ to the vertices of $T$, and for an alignment (set of characters) $A$ we put $l(A,T)=\sum_{f\in A} l(f,T)$. A maximum parsimony (MP) tree of $A$ is a binary phylogenetic $X$-tree minimizing $l(A,\cdot)$.

The **$A_k$-alignment** of $T$ is the set $A_k(T)$ of all binary characters with $l(f,T)=k$. Thus $A_0$ is the constant character, $A_1(T)$ is the set of characters induced by the edges of $T$ (so $|A_1(T)|=2n-3$), and in general

$$|A_k(T)| = \frac{2n-3k}{k}\binom{n-k-1}{k-1}\, 2^{k-1},$$

which does not depend on the shape of $T$; in particular $|A_2(T)| = 2(n-3)^2$.

**Buneman's theorem (classic, $k=1$).** Two binary phylogenetic $X$-trees are equal if and only if they have the same split set. Consequently $T$ is the unique MP tree of $A_1(T)$.

**Theorem ($k=2$).** If $n \ge 9$, then $T$ is the unique MP tree of $A_2(T)$: for every binary phylogenetic $X$-tree $\widetilde T \neq T$,

$$l\big(A_2(T),\widetilde T\big) > l\big(A_2(T),T\big) = 2\,|A_2(T)| = 4(n-3)^2.$$

**Necessary condition (all $n$).** If $T \neq \widetilde T$ are binary phylogenetic $X$-trees, then $A_2(T) \neq A_2(\widetilde T)$.

**Mixed alignments.** For $n \ge 9$, $T$ is also the unique MP tree of each of the concatenations $A_0.A_1(T)$, $A_0.A_2(T)$, $A_1(T).A_2(T)$ and $A_0.A_1(T).A_2(T)$ (see [concatenation of alignments](concatenation-preserves-a-unique-maximum-parsimony-tree.md)).

**Conjecture.** For $k < n/4$, $T$ is the unique MP tree of $A_k(T)$; the theorem above settles the case $k=2$, since $n \ge 9$ gives $2 < n/4$.

## Depends on

- [Pairwise compatible splits determine a unique unrooted X-tree](../../../neighbor-joining/pairwise-compatible-splits-determine-a-unique-un.md)
- [Fitch's algorithm](../../../small-parsimony-problem/fitch.md)
- [Concatenation preserves a unique maximum parsimony tree](concatenation-preserves-a-unique-maximum-parsimony-tree.md)

## Expansion

*Necessary condition.* If $T \neq \widetilde T$, Buneman's theorem and $|\Sigma(T)| = |\Sigma(\widetilde T)|$ give a split $\sigma = A|B \in \Sigma(T)\setminus\Sigma(\widetilde T)$ of minimum size, with $|A|\ge 2$. Its two pending sub-splits lie in $\Sigma(T)\cap\Sigma(\widetilde T)$ by minimality, so the character $f$ induced by $\sigma$ has $l(f,T)=1$ but $l(f,\widetilde T)=2$; hence $f\in A_2(\widetilde T)\setminus A_2(T)$.

*Theorem.* Induction on $n$, with base case $n = 9$ settled by exhaustive search over all binary trees on nine leaves. For $n+1 \ge 10$ leaves, pick a cherry $[1,n+1]$ and let $T^n$ be the tree with that cherry collapsed to leaf 1. Split $A_2(T^{n+1})$ into Part A (leaves $1$ and $n+1$ in the same state), which is a copy of $A_2(T^n)$ with taxon $n+1$ duplicating taxon $1$, and Part B (different states), which reduces to two copies of an $A_1$-alignment of a smaller tree. The induction hypothesis makes $T^{n+1}$ the unique MP tree of Part A, Buneman's theorem makes it an MP tree of Part B, and the concatenation lemma combines the two.

The threshold matters: equal $A_2$-alignments are already excluded for every $n$, yet the source exhibits an 8-taxon tree for which this necessary condition does not suffice for uniqueness of the MP tree. The discussion also records that for $k \ge 3$ and $n = 2k$ there are distinct trees with $A_k(T_1)=A_k(T_2)$, so some lower bound on $n$ in terms of $k$ is unavoidable.

## Sources

- Mareike Fischer, "On the uniqueness of the maximum parsimony tree for data with up to two substitutions: An extension of the classic Buneman theorem in phylogenetics", Molecular Phylogenetics and Evolution 137 (2019), 127–137, <https://doi.org/10.1016/j.ympev.2019.03.013>. Published version of arXiv:1808.07098, cited next; locators there refer to the arXiv version.
- Mareike Fischer, "On the uniqueness of the maximum parsimony tree for data with up to two substitutions: an extension of the classic Buneman theorem in phylogenetics", arXiv:1808.07098 (2018), Section 2.2 (Theorems 1 and 2, Corollary 1, Lemma 1, Conjecture 1) and Section 3 (Theorem 3, Proposition 1, Lemma 2, Corollary 2), <https://doi.org/10.48550/arXiv.1808.07098>.
