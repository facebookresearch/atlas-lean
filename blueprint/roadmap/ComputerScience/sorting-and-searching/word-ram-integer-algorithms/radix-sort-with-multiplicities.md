# Radix sorting with multiplicity extraction in linear time

Fix a constant $\kappa$. There is a deterministic word-RAM program that, given $n$ natural numbers each below $(n+2)^\kappa$, outputs their run-length multiplicity encoding using $O_\kappa(n + 1)$ instructions at every word size $w \ge c_\kappa \log_2 (n+2)$.

## Proof sketch

Sort stably by least significant digit first in base $\Theta(n)$ (counting sort per digit, $O(\kappa)$ passes), then one left-to-right scan over the sorted array emits each maximal run of equal keys with its length.

## Depends on

- [Run-length multiplicity encoding of a multiset](run-length-multiplicity-encoding.md)
- [Counting sort](../counting-sort/counting-sort.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Correctness of radix sort](../radix-sort/radix-sort-correct.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley, 1998.
