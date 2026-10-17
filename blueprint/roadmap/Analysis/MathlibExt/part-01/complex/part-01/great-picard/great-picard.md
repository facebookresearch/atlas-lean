---
article_id: af_06128463e10d282c4870242d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.GreatPicardWanted.greatPicard
---

# Great Picard

If `f` has an essential isolated singularity at `c`, then the set of `w : ℂ` whose fiber over some
punctured `ball c r \ {c}` is finite is a subsingleton: at most one value is taken only finitely
often near `c`. Source: Great Picard theorem, E. Picard 1879; see Ahlfors, Complex Analysis; Lean
is essential isolated singularity version with finite-fiber exceptional set subsingleton, at most
one value finitely often near c.

## Depends on

- [Is Essential Isolated Singularity At](is-essential-isolated-singularity-at.md)

## Proof depends on

- [Bloch](../bloch.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.GreatPicard](../../../../../../../sources/v2/MathlibExt.md)
