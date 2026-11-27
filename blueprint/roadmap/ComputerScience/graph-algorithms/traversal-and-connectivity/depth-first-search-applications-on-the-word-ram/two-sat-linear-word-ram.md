# Linear-time 2-SAT with witness construction on the word RAM

There is a deterministic word-RAM program that, given a CNF formula $\varphi$ over $n$ variables with clauses of at most two literals, decides satisfiability and on satisfiable inputs outputs a satisfying assignment, in $O(n + |\varphi|)$ instructions: it validates clause widths, assembles the implication graph in compressed sparse row form, computes the strongly connected components by Kosaraju's algorithm, and reads off the assignment from the component order.

## Depends on

- [Compressed-sparse-row encoding of a directed graph](../../../sorting-and-searching/word-ram-integer-algorithms/compressed-sparse-row-graph-encoding.md)
- [Implication graph as a finite directed graph](../../../../Logic/propositional-logic/2-satisfiability/implication-graph.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Topological sort and Kosaraju SCC in O(n + m) word-RAM time](linear-time-dfs-word-ram.md)
- [Satisfying assignments of 2-CNF formulas from SCC order](two-sat-witness-from-scc-order.md)
- [Correctness of the SCC-based 2-SAT procedure](../../../../Logic/propositional-logic/2-satisfiability/decide2-sat-eq-true-iff.md)

## Sources

- B. Aspvall, M. F. Plass and R. E. Tarjan, "A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas", Information Processing Letters 8(3), 1979.
