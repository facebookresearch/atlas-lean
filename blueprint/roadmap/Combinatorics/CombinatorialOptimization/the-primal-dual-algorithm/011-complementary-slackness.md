---
article_id: af_b8053b5429666d67a357ac84
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: complementary_slackness
---

# Theorem 1 (complementary slackness)

For the standard primal-dual pair (P) $\max\{c^\top x \mid Ax \leq b,\; x \geq 0\}$ and (D) $\min\{b^\top y \mid A^\top y \geq c,\; y \geq 0\}$, suppose $x$ and $y$ are feasible solutions to (P) and (D). Then $x$ and $y$ are simultaneously optimal if and only if the complementary slackness conditions hold: for all $i$, $(b_i - \sum_j a_{ij} x_j)\, y_i = 0$; and for all $j$, $(\sum_i a_{ij} y_i - c_j)\, x_j = 0$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 4 (Strong duality)](../the-simplex-algorithm/035-strong-duality.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), The Primal-dual Algorithm, Oct 28](../../../../sources/v1/CombinatorialOptimization.md)
