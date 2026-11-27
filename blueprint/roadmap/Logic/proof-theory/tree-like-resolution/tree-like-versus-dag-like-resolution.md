# Tree-like derivations versus line-based resolution proofs

Every tree-like resolution derivation with $s$ nodes yields a line-based resolution proof of the same conclusion with at most $s$ lines, and every line-based proof unfolds into a tree-like derivation, possibly exponentially larger since a line used several times is copied. A tree-like refutation of $\varphi$ is the same as a decision tree that queries variables and whose leaves are labelled by clauses of $\varphi$ falsified on the path, of the same size.

## Proof sketch

List the nodes of the tree in post-order to get a line-based proof; conversely unfold a proof from its last line. A tree-like refutation read from the root queries the resolved variable at each node; a falsified axiom labels each leaf.

## Depends on

- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)
- [Resolution derivation](../../propositional-logic/resolution-size-and-width/is-resolution-derivation.md)

## Proof depends on

- [DPLL search trees and tree-like resolution simulate each other](../../propositional-logic/sat-solving/dpll-search-trees-and-tree-like-resolution.md)

## Sources

- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021.
- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-Like Resolution by Asymmetric Prover–Delayer Games", Information Processing Letters 110(23), 1074–1077, 2010: Section 2 (decision-tree view, size = number of nodes).
- K. Iwama and S. Miyazaki, "Tree-Like Resolution Is Superpolynomially Slower Than DAG-Like Resolution for the Pigeonhole Principle", Algorithms and Computation (ISAAC), 1999.
