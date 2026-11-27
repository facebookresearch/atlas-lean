# The first-order theory of the strong tree iteration of the successor structure is undecidable

For the successor structure of the natural numbers, the first-order theory of its strong tree iteration with the equal-level relation, with first-order quantifiers on siblings, is undecidable; so the decidability of chain logic over weak iterations does not transfer to strong ones.

**Theorem (Spelten, Thomas and Winter).** Let $\mathcal{S} = (\mathbb{N}, \mathrm{Suc})$, and let $\mathcal{S}^*_E$ be its [strong tree iteration with the equal-level relation](tree-iterations-with-the-equal-level-relation.md). The first-order theory of $\mathcal{S}^*_E$ with FO on siblings is undecidable (Theorem 13). Consequently its chain theory is undecidable too.

By contrast, for the weak iteration $\mathcal{S}^\#_E$ the chain theory with FO on siblings is decidable, since the first-order theory of $\mathcal{S}$ is decidable (Theorem 12).

## Depends on

- [Tree iterations with the equal-level relation](tree-iterations-with-the-equal-level-relation.md)
- [Complete theory of a first-order structure](../../first-order-logic/theory-of-structure.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the termination problem of 2-counter machines started in configuration $(1,0,0)$ (Minsky). A computation $(\ell_0,m_0,n_0), \dots, (\ell_r,m_r,n_r)$ is coded by three finite paths of the same length, carrying the instruction numbers, the values of the first counter and the values of the second counter as their successive letters; each path is determined by its last node $x_0$, $x_1$, $x_2$, and $E(x_0,x_1) \wedge E(x_1,x_2)$ makes them equally long. A first-order sentence with FO on siblings states the initial condition at the children of the root, the update condition at every level (for instance, for "$3$ Inc$(X_2)$": the next instruction node is the number $4$, the next first-counter node is the clone of the current one, and the next second-counter node is the $\mathrm{Suc}$-successor of the clone of the current one), and that $x_0$ is the stop instruction. Then $M$ terminates iff the sentence holds in $\mathcal{S}^*_E$.

## Sources

- Alex Spelten, Wolfgang Thomas and Sarah Winter, "Trees over infinite structures and path logics with synchronization", in *Proceedings 13th International Workshop on Verification of Infinite-State Systems (INFINITY 2011)*, Electronic Proceedings in Theoretical Computer Science 73, 2011, pp. 20–34, doi:10.4204/EPTCS.73.5; read as arXiv:1111.3107v1, <https://arxiv.org/abs/1111.3107v1>: Theorems 12 and 13 and Section 5 of arXiv:1111.3107v1.
