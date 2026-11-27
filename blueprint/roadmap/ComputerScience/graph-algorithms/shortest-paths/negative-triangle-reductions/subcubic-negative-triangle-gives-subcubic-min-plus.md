# A truly subcubic negative triangle detector gives a truly subcubic (min,+) product

Suppose negative triangle detection on tripartite graphs with $m$ vertices per part can be performed at cost at most $c\, m^{3 - \delta}$ for some constants $c \ge 0$ and $0 < \delta \le 2$. Then the $(\min,+)$ product of two $n \times n$ matrices with entries in $\{-W, \dots, W\} \cup \{+\infty\}$ can be computed at cost at most

$$
544\, c\, \lceil \log_2(4W + 2) \rceil\, n^{3 - \delta/3}.
$$

Combined with the converse reduction, negative triangle detection, the $(\min,+)$ product and all-pairs shortest paths are equivalent under subcubic reductions for polynomially bounded weights.

## Proof sketch

Compose the three steps: finding by halving, APNT by blocking with block size $s = n^{1/3}$, and simultaneous binary search. With $t = n/s$ blocks, APNT costs $O((t^3 + n^2) s^{3-\delta})$, which is $O(n^{3 - \delta/3})$.

## Depends on

- [Negative triangles in tripartite weighted graphs](negative-triangle.md)
- [Min-plus matrix powers give shortest path weights with at most $r$ edges](../all-pairs-shortest-paths-by-min-plus-products/matrix-pow-edge-bounded.md)
- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Fine-grained reductions](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [Finding a negative triangle from a detector](finding-negative-triangle-from-detection.md)
- [All pairs negative triangles by blocking](all-pairs-negative-triangles-by-blocking.md)
- [The (min,+) product by simultaneous binary search over APNT](min-plus-product-via-apnt.md)
- [Negative triangle detection with one (min,+) product](negative-triangle-via-min-plus.md)
- [The (min,+) product as shortest distances in a layered graph](min-plus-product-as-layered-shortest-paths.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
