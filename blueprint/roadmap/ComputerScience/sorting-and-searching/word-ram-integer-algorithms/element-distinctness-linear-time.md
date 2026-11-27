# Element distinctness in linear time for a bounded universe

There is a deterministic word-RAM program that, given $n$ natural numbers $a_1, \dots, a_n$ with every $a_i < n$, decides whether they are pairwise distinct using $O(n + 1)$ instructions and $n$ extra memory words, at every word size with $n < 2^w$.

This contrasts with the comparison model, where deciding distinctness of $n$ keys requires $\Omega(n \log n)$ comparisons: on the word RAM a key bounded by $n$ is also an address.

## Proof sketch

Zero a table of $n$ flags, scan the input, and for each $a_i$ test and set flag $a_i$; a flag that is already set witnesses a repetition. Each element costs a constant number of instructions.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Randomized word RAM](randomized-word-ram.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
