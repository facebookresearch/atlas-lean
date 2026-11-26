# The (min,+) product by simultaneous binary search over APNT

Let $A, B$ be $n \times n$ matrices with entries in $\{-W, \dots, W\} \cup \{+\infty\}$. The $(\min,+)$ product $(A \star B)_{ij} = \min_k (A_{ik} + B_{kj})$ can be computed with $\lceil \log_2(4W + 2) \rceil$ calls to an APNT procedure (each entry is one of the $4W + 2$ values in $\{-2W, \dots, 2W\} \cup \{+\infty\}$): maintain for each pair $(i,j)$ an interval known to contain $(A \star B)_{ij}$, and in each round set $C_{ij}$ to minus the midpoint of its interval; the APNT answer for $(i,j)$ tells whether $(A \star B)_{ij}$ is below the midpoint.

## Proof sketch

$(i,j)$ lies on a negative triangle with $C_{ij} = -c$ exactly when $\min_k(A_{ik} + B_{kj}) < c$. Every round halves every interval, and all pairs are searched in parallel by one APNT call.

## Depends on

- [Negative triangles in tripartite weighted graphs](negative-triangle.md)
- [Min-plus matrix powers give shortest path weights with at most $r$ edges](../all-pairs-shortest-paths-by-min-plus-products/matrix-pow-edge-bounded.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
