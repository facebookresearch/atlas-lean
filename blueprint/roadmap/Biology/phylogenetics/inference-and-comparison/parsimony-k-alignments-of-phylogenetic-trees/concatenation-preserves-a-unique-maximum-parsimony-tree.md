# Concatenation preserves a unique maximum parsimony tree

**Statement.** Let $X$ be a finite taxon set, and let $A$ and $B$ be alignments (finite sets of characters on $X$) with concatenation $A.B$ (their union as character sets). For a binary phylogenetic $X$-tree $T$ write $l(A,T)=\sum_{f \in A} l(f,T)$ for the parsimony score. Suppose $T$ is a maximum parsimony tree of both $A$ and $B$, and is the *unique* maximum parsimony tree of at least one of them. Then $T$ is the unique maximum parsimony tree of $A.B$.

**Application.** With the constant character $A_0$ (score $0$ on every tree), the edge characters $A_1(T)$ (unique MP tree $T$ by Buneman's theorem) and, for $n=|X|\ge 9$, the alignment $A_2(T)$ of characters of score $2$ on $T$ (unique MP tree $T$), the lemma shows that $T$ is the unique maximum parsimony tree of $A_0.A_1(T)$, $A_0.A_2(T)$, $A_1(T).A_2(T)$ and $A_0.A_1(T).A_2(T)$, i.e. of the alignment of all binary characters of score at most $2$ on $T$.

## Expansion

Parsimony scores are additive over characters, so $l(A.B,\widetilde T) = l(A,\widetilde T) + l(B,\widetilde T)$. If $T$ is the unique MP tree of $A$ and an MP tree of $B$, then for every $\widetilde T \neq T$,

$$l(A.B,\widetilde T) = l(A,\widetilde T) + l(B,\widetilde T) > l(A,T) + l(B,T) = l(A.B,T).$$

The constant character contributes $0$ to every tree, which is why appending $A_0$ never changes the MP tree.

## Sources

- Mareike Fischer, "On the uniqueness of the maximum parsimony tree for data with up to two substitutions: An extension of the classic Buneman theorem in phylogenetics", Molecular Phylogenetics and Evolution 137 (2019), 127–137, <https://doi.org/10.1016/j.ympev.2019.03.013>. Published version of arXiv:1808.07098, cited next; locators there refer to the arXiv version.
- Mareike Fischer, "On the uniqueness of the maximum parsimony tree for data with up to two substitutions: an extension of the classic Buneman theorem in phylogenetics", arXiv:1808.07098 (2018), Section 2.2 (Theorems 1 and 2, Corollary 1, Lemma 1, Conjecture 1) and Section 3 (Theorem 3, Proposition 1, Lemma 2, Corollary 2), <https://doi.org/10.48550/arXiv.1808.07098>.
