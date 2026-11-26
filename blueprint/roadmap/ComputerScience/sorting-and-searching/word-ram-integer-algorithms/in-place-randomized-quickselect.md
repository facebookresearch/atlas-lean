# In-place randomized three-way quickselect

There is a randomized word-RAM program that, given an array $a[0..n-1]$ of words in place and a rank $0 \le k < n$, rearranges $a$ and returns the element of rank $k$ of $a$ (the $k$-th entry of the sorted array, counting from $0$), using $O(1)$ registers and no memory beyond the array. It partitions the active subarray three ways (smaller, equal, larger) around a uniformly random pivot and recurses iteratively into the part containing rank $k$. Its output is correct on every run, and its expected number of instructions is $O(n + 1)$; on out-of-range ranks it halts with a failure value.

## Proof sketch

Correctness is the three-way partition invariant. For the expected cost, a uniform pivot shrinks the active subarray by a constant factor with constant probability, so the expected total partition work is a geometric series in $n$.

## Depends on

- [Randomized word RAM](randomized-word-ram.md)
- [Quickselect](../quickselect/quickselect.md)

## Proof depends on

- [Expected comparisons of quickselect](../selection-bounds/expected-comparisons-of-quickselect.md)

## Sources

- C. A. R. Hoare, "Quicksort", The Computer Journal 5(1), 1962.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
