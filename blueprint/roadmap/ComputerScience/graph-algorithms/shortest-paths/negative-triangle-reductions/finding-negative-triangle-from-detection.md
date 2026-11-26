# Finding a negative triangle from a detector

Let $\mathrm{det}$ be a procedure deciding negative triangle detection on tripartite graphs with three parts of size $m$, at cost at most $\tau(m)$ with $\tau \ge 0$. Then a negative triangle in a tripartite graph with parts of size $2^L$ can be found (or its absence reported) at cost at most

$$
\tau(1) + \sum_{l < L} 8\, \tau(2^l).
$$

## Proof sketch

Halve each part and run the detector on the eight induced subgraphs; recurse into one that contains a negative triangle. The recursion has depth $L$ with eight detector calls per level.

## Depends on

- [Negative triangles in tripartite weighted graphs](negative-triangle.md)
- [Fine-grained reductions](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/fine-grained-reductions.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
