# Union of Fibonacci heaps

The union of Fibonacci heaps $H_1$ and $H_2$ is their meld: the
heap whose trees are those of $H_1$ followed by those of $H_2$, and whose cached minimum is the
smaller of the two cached minima (the one that exists if a heap is empty, none if both are).

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 19.2 (FIB-HEAP-UNION).
