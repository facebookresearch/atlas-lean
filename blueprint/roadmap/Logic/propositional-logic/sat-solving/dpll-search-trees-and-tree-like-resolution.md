# DPLL search trees and tree-like resolution simulate each other

Let $F$ be an unsatisfiable CNF formula with $n$ variables. Use failing DPLL search trees from
[failing DPLL search trees give tree-like resolution refutations](failing-dpll-search-trees-give-tree-like.md), and tree-like resolution
refutations with weakening and size measured as the number of nodes.

- A failing DPLL search tree with $s$ leaves yields a tree-like refutation of size $O(s \cdot n)$.
- A tree-like refutation of size $s$ yields a failing DPLL search tree that only branches, with at most $s$ leaves.

So the minimum number of leaves of a failing DPLL search tree for $F$ and the minimum size of a tree-like refutation of $F$ are within a
factor $O(n)$ of each other.

Proof of the second item: walk the refutation from the empty clause, keeping an assignment that falsifies the current clause. At a
weakening of $C$ to $E \supseteq C$, $C$ is also falsified. At a resolvent $R$ of $C \ni x$ and $D \ni \neg x$, branch on $x$ if it is unassigned: with
$x = \mathrm{false}$ the clause $C$ is falsified, since $C \setminus \{x\} \subseteq R$, and with $x = \mathrm{true}$ the clause $D$ is; if $x$ is already assigned,
follow the falsified premise. Each leaf of the search tree reaches a clause of $F$, a leaf of the refutation, so there are at most $s$ leaves.

## Depends on

- [Failing DPLL search trees give tree-like resolution refutations](failing-dpll-search-trees-give-tree-like.md)
- [Tree-like resolution derivation](../resolution-size-and-width/resolution-tree.md)

## Proof depends on

- [Failing DPLL search trees give tree-like resolution refutations](failing-dpll-search-trees-give-tree-like.md)

## Sources

- J. Nordström, "On the interplay between proof complexity and SAT solving", *ACM SIGLOG News* 2(3):19–44, 2015, <https://jakobnordstrom.se/docs/publications/InterplayProofCplxSAT.pdf>: Section 3 (DPLL search trees as tree-like refutations).
- P. Beame, H. Kautz and A. Sabharwal, "Towards understanding and harnessing the potential of clause learning", *Journal of Artificial Intelligence Research* 22:319–351, 2004, <https://arxiv.org/abs/1107.0044>: Section 2.2 (tree-like resolution is equivalent to an optimal DPLL procedure). The converse construction is derived on this page.
