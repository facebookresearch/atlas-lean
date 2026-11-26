# Boxes of tensor leaves

Fix a threshold $t \le m$. A **box** is a symbol string over $\{\text{terms}\} \cup \{\ast\}$ in which at most $m - t$ positions are stars or fixed $P_0$ terms and every star precedes every fixed $P_0$ position; it denotes the set of leaves obtained by replacing each star by any of the ten terms. Its **value** sums the products of the two leaf encodings over its leaves and satisfies the recurrence that replaces the highest star by each of the ten terms.

## Depends on

- [Leaves of the tensor power and their order](tensor-power-leaves-and-order.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
