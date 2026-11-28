# Chain logic of the binary tree with MSO on tree levels is undecidable

The chain theory of the binary tree with the equal-level relation, extended by monadic second-order quantification over subsets of a single tree level, is undecidable, although the chain theory with the equal-level relation alone is decidable.

**Theorem (Spelten, Thomas and Winter).** Let $\mathcal{M}_2 = (\{0,1\}, \{0\}, \{1\})$, so that $\mathcal{M}^\#_{2,E}$ is the binary tree with the [equal-level relation](../tree-iterations-with-the-equal-level-relation.md). The chain theory of $\mathcal{M}^\#_{2,E}$ with MSO on tree levels is undecidable (Theorem 14).

Here set quantifiers range over chains (subsets of paths), and in addition over arbitrary subsets of one level $\{v \in \{0,1\}^* : |v| = n\}$. With MSO only on siblings instead of whole levels the theory is decidable (Theorem 12).

## Depends on

- [Tree iterations with the equal-level relation](../tree-iterations-with-the-equal-level-relation.md)
- [Monadic second-order logic of two successors](../../../../TheoryOfComputation/omega-automata-and-games/automata-on-infinite-trees/monadic-second-order-logic-of-two-successors.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Following an idea of Potthoff and Thomas, finite sets of nodes above a level $L$ are coded by subsets of level $L$: a node $v$ before level $L$ is mapped to the unique node $v'$ of level $L$ in $v10^*$, the leftmost descendant of the right child of $v$. This map is injective and first-order definable given $L$, and the left and right successor relations translate to first-order definable relations on level $L$. Hence an existential quantifier over finite sets is simulated by one over subsets of a level beyond all elements of the set, and the weak monadic second-order theory of the binary tree with $E$, which is undecidable (Thomas), is interpretable in the first-order theory of $(\{0,1\}^*, S_0, S_1, \preceq, E)$ with MSO restricted to levels.

## Sources

- Alex Spelten, Wolfgang Thomas and Sarah Winter, "Trees over infinite structures and path logics with synchronization", in *Proceedings 13th International Workshop on Verification of Infinite-State Systems (INFINITY 2011)*, Electronic Proceedings in Theoretical Computer Science 73, 2011, pp. 20–34, doi:10.4204/EPTCS.73.5; read as arXiv:1111.3107v1, <https://arxiv.org/abs/1111.3107v1>: Theorems 12 and 14 and Section 5 of arXiv:1111.3107v1.
