---
article_id: af_86d1682a66bf5312e6f80c84
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Algebra.Module.QuillenSuslinWanted.quillen_suslin
---

# Quillen Suslin

If `k` is a field and `M` is a finitely generated projective module over `MvPolynomial (Fin n) k`,
then `M` is free. Source: Serre's conjecture proved by D. Quillen, Invent. Math. 36 (1976) and A.
A. Suslin, Dokl. Akad. Nauk SSSR 229 (1976); Lam, Serre's Problem; Lean states field case over
`MvPolynomial (Fin n) k` with PID generalization existing.

Proof: The argument follows Quillen's induction and patching route, using Roberts'
idempotent-matrix proof of local Horrocks; see Quillen (1976), Lam, Lang, and Dicks.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Algebra.Module.QuillenSuslin](../../../../sources/v2/MathlibExt.md)
