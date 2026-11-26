# The box preprocessing/query trade-off and the exponent 0.064

At block parameters $m = 9k$, $L = 189k$ and threshold $\lceil m/9 \rceil = k$, both the number of retained box values over all tiles and the number of low-order query contributions are at most $N^2$ times a polynomial in $k$ times $(9/20)^k$, provided $D^{18} \le N$ and $Q \cdot 2^m \le N^2$. Since $9^{125} \cdot 4^{72} \le 20^{125}$, $(9/20)^k \le D^{-8/125} = D^{-0.064}$ for $D = 4^m$, improving the saving exponent from $1/18$ to $0.064$.

## Proof sketch

The retained boxes form a geometric tail of the completed-leaf counts and the low-order contributions a weighted binomial prefix of the query counts; at the ninth-block threshold both decay with ratio $9/20$. The integer inequality converts the rational decay into a power of $D$.

## Depends on

- [Boxes of tensor leaves](boxes-of-tensor-leaves.md)

## Proof depends on

- [Disjoint box decomposition of high-order leaves](box-decomposition-of-high-order-leaves.md)
- [Sparse query bound for contributing leaves](sparse-leaf-bound.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
