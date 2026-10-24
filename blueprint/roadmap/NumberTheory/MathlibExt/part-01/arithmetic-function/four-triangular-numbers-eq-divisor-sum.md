---
article_id: af_4cda84bb9afbc9d225e8c192
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.four_triangular_numbers_eq_divisor_sum
---

# Four Triangular Numbers

Legendre: `t_4(j) = σ(2*j+1)`, where `t_4(j)` counts ordered writes of `j`
as a sum of 4 triangular numbers and `σ` is the divisor sum.

The source gives an alternate proof via its triangular recurrence
(equation triangular) and Melfi's convolution identities, citing further
proofs in Berndt, Hahn, HOSW, and ORW. The subtype counts ordered
4-tuples of indices (zeros allowed, so `T_0 = 0` contributes); the right
side sums `Nat.divisors (2*j+1)`. Verified computationally at `j = 0..8`
(e.g. `t_4(4) = 13 = σ(9)`).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.FourTriangularNumbers](../../../../../sources/v2/MathlibExt.md)
- Hartosh Singh Bal and Gaurav Bhatnagar, "Glaisher's Divisors and Infinite Products," Journal of Integer Sequences 27 (2024), Article 24.1.6, Proposition [Legendre] (equation nttriangle-b), lines 738–740, https://cs.uwaterloo.ca/journals/JIS/VOL27/Bhatnagar/bhat4.tex
