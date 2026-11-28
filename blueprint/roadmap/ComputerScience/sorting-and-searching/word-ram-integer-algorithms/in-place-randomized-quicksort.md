# In-place randomized three-way quicksort with an explicit range stack

There is a randomized word-RAM program that sorts an array of $n$ words in place, keeping the pending subranges on an auxiliary stack and using $O(1)$ further registers, with three-way (Dutch national flag) partitioning around a pivot drawn uniformly from the active subrange. Every run produces the sorted permutation of the input, and the expected number of instructions is $O\big((n+1)\log(n+2)\big)$.

## Proof sketch

The expected cost satisfies the quicksort recurrence $T(n) \le cn + \frac{1}{n}\sum_{i}(T(i) + T(n-1-i))$ restricted to strictly smaller parts; three-way partitioning only removes equal keys, so the classical $O(n \log n)$ solution applies. The stack needs at most $2n$ words: the pending subranges are pairwise disjoint and nonempty, so there are at most $n$ of them, each stored as two words.

## Depends on

- [Randomized word RAM](randomized-word-ram.md)
- [Quicksort](../quicksort/quick-sort.md)

## Proof depends on

- [Expected comparisons of quicksort on a random permutation](../quicksort/quick-sort-expected-time-uniform-permuta.md)

## Sources

- C. A. R. Hoare, "Quicksort", The Computer Journal 5(1), 1962.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- R. Sedgewick and K. Wayne, "Algorithms", 4th ed., booksite §2.3 "Quicksort": in place with "only a small auxiliary stack", Dijkstra's 3-way partitioning, the ~2 N ln N compares proposition and entropy-optimality of 3-way quicksort. <https://algs4.cs.princeton.edu/23quicksort/>
- D. Karger, MIT 6.856 Randomized Algorithms (Spring 2017), notes 1: the expected $2nH_n$ comparison bound for every input. <https://courses.csail.mit.edu/6.856/17/Notes/n1-intro.html>
- UIUC CS 473 Fundamental Algorithms (Fall 2014), Lecture 14 "Randomized Algorithms: QuickSort and QuickSelect" (slides): expected comparisons $\le 2nH_n = O(n \log n)$. <https://courses.grainger.illinois.edu/cs473/fa2014/public/14.pdf>
