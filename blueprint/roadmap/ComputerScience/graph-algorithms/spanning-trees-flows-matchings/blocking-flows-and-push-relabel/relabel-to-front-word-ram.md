# Relabel-to-front maximum flow in O(|V|^3) word-RAM time

There is a deterministic word-RAM program that, given an $n$-vertex network by its capacity matrix with integer capacities, a source and a sink, computes a maximum flow (as a flow matrix) and its value within $O(n^3)$ instructions, at every word size large enough for the total capacity and for addresses of size $O(n^2)$; the program never reads the word size and uses no randomness.

## Depends on

- [Preflows, valid labelings, push and relabel](preflows-and-valid-labelings.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Relabel-to-front performs O(|V|^3) operations](relabel-to-front-bounds.md)

## Sources

- A. V. Goldberg and R. E. Tarjan, "A New Approach to the Maximum-Flow Problem", Journal of the ACM 35(4), 1988.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
