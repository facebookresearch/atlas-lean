# Stoer-Wagner in O(n^3) word-RAM time

There is a deterministic word-RAM program that, given an $n$-vertex weighted multigraph by its symmetric weight matrix, outputs the global minimum cut value and a vertex set attaining it within $C (n+1)^3$ instructions, at every word size holding the total weight; the program does not read the word size.

## Depends on

- [Correctness of the Stoer-Wagner minimum cut algorithm](stoer-wagner-correctness.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Correctness of the Stoer-Wagner minimum cut algorithm](stoer-wagner-correctness.md)

## Sources

- M. Stoer and F. Wagner, "A Simple Min-Cut Algorithm", Journal of the ACM 44(4), 1997.
