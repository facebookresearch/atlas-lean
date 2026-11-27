# Sort key of a subset

For a subset $A$ of $\{0, \dots, n-1\}$, the sort key of $A$ is
the natural number $(n - |A|) \cdot 2^n + b(A)$, where $b(A) = \sum_{i \in A} 2^i$ is the
binary code of $A$.

Since $b(A) < 2^n$, comparing sort keys as numbers agrees with the set order: larger sets come
first, and sets of the same size are ordered by binary code.
