# Counting and deciding finite-domain CSPs over bounded treewidth

Let $F$ be a constraint satisfaction problem over a domain of size $q \ge 1$ with variable set $V$, and let $(T, B)$ be a nice tree decomposition of width $w$ whose bags cover the scope of every constraint (for instance a decomposition of the primal graph of $F$). The bottom-up dynamic program that stores, for every node $t$ and every assignment $\alpha$ of $B_t$, the number of assignments of the variables forgotten below $t$ that extend $\alpha$ and satisfy all constraints whose scopes lie below $t$, computes the exact number of solutions of $F$ and decides satisfiability. On the word RAM it runs within $C \cdot (\Sigma + 1) + 1$ instructions, where $\Sigma = O\big(|T| \cdot q^{w+1} \cdot (w + 1) \cdot |F|\big)$ is the step bound of the node handlers, at word sizes large enough to hold counts up to $q^{|V|}$.

## Proof sketch

Leaf: one empty assignment. Introduce: check the constraints whose scope contains the new variable and lies in the bag. Forget: sum over the forgotten variable's values. Join: multiply the two children's entries. The root entry counts all solutions.

## Depends on

- [Nice tree decompositions](nice-tree-decomposition.md)
- [Solution of a binary CSP within given domains](../../heuristic-search-and-planning/ac-3-algorithm/is-solution.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
- R. Dechter, "Bucket Elimination: A Unifying Framework for Reasoning", Artificial Intelligence 113(1-2), 1999.
