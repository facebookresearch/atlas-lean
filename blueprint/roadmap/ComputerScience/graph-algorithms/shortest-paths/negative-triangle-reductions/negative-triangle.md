# Negative triangles in tripartite weighted graphs

A **weighted tripartite graph** with parts $I, J, K$ is given by matrices $A \in (\mathbb{Z} \cup \{+\infty\})^{I \times K}$, $B \in (\mathbb{Z} \cup \{+\infty\})^{K \times J}$ and $C \in (\mathbb{Z} \cup \{+\infty\})^{I \times J}$, where $+\infty$ means that the edge is absent. A triple $(i, j, k) \in I \times J \times K$ is a **negative triangle** if

$$
A_{ik} + B_{kj} + C_{ij} < 0 .
$$

**Negative triangle detection** asks whether a negative triangle exists; **all pairs negative triangles (APNT)** asks, for every pair $(i,j) \in I \times J$, whether some $k$ makes $(i,j,k)$ a negative triangle.

## Depends on

- [Negative cycles](../floyd-warshall-algorithm/is-negative-cycle.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
