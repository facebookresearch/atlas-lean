# In-place randomized three-way quicksort with an explicit range stack

There is a randomized word-RAM program that sorts an array of $n$ words in place, using an explicit stack of at most $2n$ words for pending subranges and $O(1)$ registers, with three-way (Dutch national flag) partitioning around a pivot drawn uniformly from the active subrange. Every run produces the sorted permutation of the input, and the expected number of instructions is $O\big((n+1)\log(n+2)\big)$.

## Proof sketch

The expected cost satisfies the quicksort recurrence $T(n) \le cn + \frac{1}{n}\sum_{i}(T(i) + T(n-1-i))$ restricted to strictly smaller parts; three-way partitioning only removes equal keys, so the classical $O(n \log n)$ solution applies.

## Depends on

- [Randomized word RAM](randomized-word-ram.md)
- [Quicksort](../quicksort/quick-sort.md)

## Proof depends on

- [Expected comparisons of quicksort on a random permutation](../quicksort/quick-sort-expected-time-uniform-permuta.md)

## Sources

- C. A. R. Hoare, "Quicksort", The Computer Journal 5(1), 1962.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
