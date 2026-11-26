# Sparse query bound for contributing leaves

With $D = 4^m$ inner dimension, $L = 19m$ levels and a set of queried outputs $W$ with $|W| \cdot 2^m \le N^2$, the total number of contributing leaves over all queried outputs is at most $N^2 \cdot \sigma(D)$ times an explicit polynomial factor in $m$, where $\sigma(D) = D^{-1/18}$ is the **saving factor**: the counts $\beta_t$ decay geometrically in $t$ when $L = 19m$, and the counts $\alpha_t$ of small orders are bounded by the sparsity of $W$.

## Proof sketch

Split by order: high-order leaves are few because $2^t \beta_t$ is bounded at $L = 19m$, low-order contributions are few because each queried output has few contributing low-order leaves; summing the two order-wise minima gives the saving.

## Depends on

- [Leaves of the tensor power and their order](tensor-power-leaves-and-order.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
