---
article_id: af_d4dbfb111397bb8d9ff7d4f1
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Algebra.SolvableByRadicalsWanted.Algebra.solvable_iff_solvableByRad
---

# Solvable extensions ↔ solvable groups

**Solvable extensions ↔ solvable groups.** For a field `F` of
characteristic zero and a nonzero `p : F[X]`, every root of `p` in
`AlgebraicClosure F` lies in `solvableByRad F (AlgebraicClosure F)`
iff `p.Gal` is solvable.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Algebra.SolvableByRadicalsWanted](../../../sources/v2/WantedExt.md)
- É. Galois (1832); the iff appears in standard texts such as Stewart, *Galois Theory* (Theorem 18.10); Lang, *Algebra* (VI §7); Rotman, *Galois Theory* (Theorem 73). Listed as §58 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `solvable_by_radicals_converse`.
