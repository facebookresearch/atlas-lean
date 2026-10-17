---
article_id: af_e2496548d8fb8be7a66b410e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.ThueSiegelRothWanted.thue_siegel_roth
---

# Thue Siegel Roth

For irrational real algebraic `α : ℝ` and any `ε > 0`, only finitely many `q : ℚ` satisfy `|α - q|
< 1 / (q.den : ℝ) ^ (2+ε)` via `Real.rpow`. Source: K. F. Roth, Rational approximations to
algebraic numbers, Mathematika 2 (1955) 1–20; predecessors Thue 1909 and Siegel 1921; textbook in
Schmidt, Diophantine Approximation

Proof: The proof constructs Siegel's auxiliary polynomial, bounds its index at rational
approximation points by a Taylor estimate, and contradicts the inductive Roth lemma.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Roth Auxiliary](../part-10/finite-of-divisible-approximations.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ThueSiegelRoth](../../../../sources/v2/MathlibExt.md)
