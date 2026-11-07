# Union of Fibonacci heaps

The union of Fibonacci heaps $H_1$ and $H_2$ is their meld: the
heap whose trees are those of $H_1$ followed by those of $H_2$, and whose cached minimum is the
smaller of the two cached minima (the one that exists if a heap is empty, none if both are).

CLRS calls this operation union.
