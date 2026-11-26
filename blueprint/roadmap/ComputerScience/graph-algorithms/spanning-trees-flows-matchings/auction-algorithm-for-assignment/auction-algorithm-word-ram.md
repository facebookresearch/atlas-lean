# The auction algorithm on the word RAM

There are deterministic word-RAM programs that, given an $n \times n$ signed integer cost matrix with entries of absolute value at most $M$, run the $\varepsilon$-auction (returning an assignment within $n\varepsilon$ of optimal) and the scaled auction (returning an optimal assignment and its cost), each bid costing at most $4n + 6$ memory operations plus initialization $O(n^2)$; with the bid bound this gives $O\big(n^2 + n \cdot \tfrac{n(C+\varepsilon)}{\varepsilon}\big)$ instructions, where $C \le 2M$ (scaled by $n+1$ in the scaled version), at word sizes holding the scaled prices.

## Depends on

- [Bertsekas's Gauss-Seidel auction algorithm](gauss-seidel-auction-algorithm.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Termination and near-optimality of the auction algorithm](auction-algorithm-correctness.md)

## Sources

- D. P. Bertsekas, "The Auction Algorithm: A Distributed Relaxation Method for the Assignment Problem", Annals of Operations Research 14, 1988.
