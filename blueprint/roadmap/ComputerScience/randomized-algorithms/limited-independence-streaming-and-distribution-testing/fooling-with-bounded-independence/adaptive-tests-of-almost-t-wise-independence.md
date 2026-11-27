# Adaptive bit tests of almost t-wise independent distributions

Let $Z$ be a distribution on $\{0,1\}^n$ with $n \ge t$ such that every marginal on $t$ coordinates is within statistical distance $\varepsilon$ of uniform. Then every randomized adaptive test that reads at most $t$ distinct positions on each input (using finitely many random-coin outcomes) has distinguishing gap at most $2^t\varepsilon$ between $Z$ and the uniform distribution.

## Proof sketch

Each subcube fixing at most $t$ coordinates has probability within $\varepsilon$ under $Z$ and uniform (it is an event of a $t$-marginal). The subcube transfer with $C = 1$ gives $2^t\varepsilon$ for each tree, and averaging over coins preserves it.

## Depends on

- [Subcube bounds transfer to adaptive decision-tree tests](subcube-bounds-transfer-to-decision-trees.md)
- [Total variation distance of functions on a finite set](../../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
