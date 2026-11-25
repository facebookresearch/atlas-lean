# Failing DPLL search trees give tree-like resolution refutations

Let $F$ be an unsatisfiable CNF formula with $n$ variables. A *failing DPLL search tree* for $F$ is a finite binary tree whose nodes carry
partial assignments, the root the empty one. An inner node either branches on an unassigned variable $x$, with children extending
its assignment by $x = \mathrm{true}$ and $x = \mathrm{false}$, or performs unit propagation, with one child extending its assignment by the
literal that makes a unit clause true. Every leaf's assignment falsifies a clause of $F$.

If such a tree has $s$ leaves, then $F$ has a tree-like resolution refutation, with weakening, of size $O(s \cdot n)$.

Proof: count each unit propagation as a branch whose second child, setting the literal false, falsifies the unit clause at once.
Each root-to-leaf path has at most $n$ inner nodes, so the expanded tree has at most $s(n+1)$ leaves. Working from the leaves up, label
each node by a clause falsified by its assignment: a leaf by a clause of $F$ it falsifies; a node branching on $x$ by the clause of a child
when that clause does not mention $x$, and otherwise by the resolvent on $x$ of its two children's clauses, which then contain $\neg x$
and $x$ respectively. The root gets the empty
clause, and the labels form a tree-like refutation with fewer nodes than the expanded tree, at most $2s(n+1) - 1$.

## Depends on

- [Tree-like resolution derivation](../resolution-size-and-width/resolution-tree.md)

## Sources

- J. Nordström, "On the interplay between proof complexity and SAT solving", *ACM SIGLOG News* 2(3):19–44, 2015, <https://jakobnordstrom.se/docs/publications/InterplayProofCplxSAT.pdf>: Section 3 (the DPLL method, unit propagation, and the search tree read as a tree-like resolution refutation).
- P. Beame, H. Kautz and A. Sabharwal, "Towards understanding and harnessing the potential of clause learning", *Journal of Artificial Intelligence Research* 22:319–351, 2004, <https://arxiv.org/abs/1107.0044>: Section 1 (a DPLL trace converts to a tree-like resolution proof of the same size). The labelling argument and the bound are derived on this page.
