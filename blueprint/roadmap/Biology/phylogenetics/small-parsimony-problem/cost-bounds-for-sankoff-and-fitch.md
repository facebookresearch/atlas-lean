# Cost bounds for Sankoff and Fitch

This node collects the correctness and cost contracts of the two small-parsimony algorithms on a
fixed rooted binary tree with $n$ nodes, for one character with $k$ states; for $m$ independent
characters each algorithm runs once per character and the costs add.

## Expansion

A sound expansion has separate pages for:

1. **Fitch.** The postorder recursion that sets the state set of a node to the intersection of its
   children's sets when nonempty, and otherwise to their union with cost one, computes the minimum
   number of state changes; the preorder pass reconstructs an optimal labelling. With state sets
   represented so that intersection and union cost $O(k)$, each pass costs $O(nk)$.
2. **Sankoff.** For a cost matrix $C$ with entries in $\mathbb{N} \cup \{\infty\}$ (the cost model of the linked
   correctness page; real or negative costs need a separate extension of that statement), the recursion $S_t(v) = \sum_{w \text{ child of } v}
   \min_i \bigl(C_{t,i} + S_i(w)\bigr)$ computes the minimum weighted cost; its correctness is the separate page listed under the proof
   dependencies, and this item adds only the cost bound. Computing all $k$ values at a node by direct minimization costs $O(k^2)$ per
   child, so the recursion costs $O(nk^2)$ under unit-cost arithmetic and comparisons, and the
   traceback costs $O(nk)$. One cited set of notes states $O(nk)$ per character for Sankoff by
   counting the per-node work as $O(k)$; the cost page must fix its counting convention and not adopt
   that figure for general cost matrices.
3. The cost model (unit-cost arithmetic on costs, and the representation of state sets) as its own
   statement.

- Statement prerequisite: the unit-cost model for arithmetic and comparisons on costs, and the representation of state sets.

## Proof depends on

- [Sankoff's algorithm computes the small-parsimony cost](sankoff-eq-inf.md)

## Sources

- R. Shamir (ed.), *Algorithms for Molecular Biology*, lecture notes, Tel Aviv University, 2000,
  Lecture 8, sections "Small Parsimony" (Fitch's algorithm, $O(k)$ work per node and $O(nk)$ per
  character) and "Weighted Parsimony" (Sankoff's algorithm).
  <https://www.cs.tau.ac.il/~rshamir/algmb/00/scribe00/html/lec08/node7.html>
- CPSC 536A lecture notes, University of British Columbia, 6 February 2001: Fitch's recursion on a
  fixed tree. <https://www.cs.ubc.ca/labs/algorithms/Courses/CPSC536A-01/Class10/class10-notes.html>
