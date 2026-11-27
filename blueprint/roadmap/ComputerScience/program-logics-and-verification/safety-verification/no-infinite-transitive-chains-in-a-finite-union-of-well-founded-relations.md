# No infinite transitive chains in a finite union of well-founded relations

Call a binary relation $T$ on a set $S$ *well-founded* if there is no infinite sequence $s_0, s_1, s_2, \dots$ with $(s_i, s_{i+1}) \in T$ for all $i$. Let $T_1, \dots, T_k$ be well-founded relations on $S$ and $T = T_1 \cup \dots \cup T_k$. Then there is no infinite sequence $s_0, s_1, s_2, \dots$ in $S$ with $(s_i, s_j) \in T$ for all $i < j$.

The proof colours each pair $\{i, j\}$, $i < j$, by the least $l$ with $(s_i, s_j) \in T_l$ and applies the infinite Ramsey theorem for pairs: an infinite monochromatic set $i_0 < i_1 < \cdots$ of colour $l$ gives an infinite $T_l$-chain $s_{i_0}, s_{i_1}, \dots$. This is the step that turns a disjunctively well-founded transition invariant into a termination proof.

## Proof depends on

- [Infinite Ramsey theorem](../../../Combinatorics/ramsey-theory/structural-ramsey/infinite-ramsey-theorem.md)

## Sources

- S. Berardi, P. Oliva and S. Steila, "Proving termination of programs having transition invariants of height ω", *Proceedings of the 15th Italian Conference on Theoretical Computer Science (ICTCS 2014)*, CEUR Workshop Proceedings 1231, 2014, pp. 237–240, <https://ceur-ws.org/Vol-1231/short1.pdf>, Section 3 (the Termination Theorem of Podelski and Rybalchenko is proved classically from Ramsey's theorem); the Ramsey step is Theorem 9.1.2 of Diestel below, applied to the colouring by the least index.
- R. Diestel, *Graph Theory*, 5th edition, Graduate Texts in Mathematics 173, Springer, 2017, Section 9.1, Theorem 9.1.2.
