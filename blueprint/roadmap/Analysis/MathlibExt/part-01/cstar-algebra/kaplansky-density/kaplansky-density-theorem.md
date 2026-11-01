---
article_id: af_1eb43bae48eefd757538883f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.CStarAlgebra.KaplanskyDensityWanted.kaplansky_density_theorem
---

# Kaplansky density theorem

For a complex Hilbert space `H` and unital `∗`-subalgebra `S ⊆ B(H)`, the SOT-closure of its
operator-norm unit ball equals the unit ball of its SOT-closure, with norm and membership read via
`toBounded` and closure taken in `H →Lₚₜ[ℂ] H`. Source: Kaplansky density theorem, I. Kaplansky,
Pacific J. Math. 1 (1951), 227–232; see Takesaki, Theory of Operator Algebras I, Density Theorem
and Kadison–Ringrose Vol I; Lean is SOT-closure equality of unit balls via toBounded conversion,
full infinite-dimensional form.

## Depends on

- [To Bounded](to-bounded.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.CStarAlgebra.KaplanskyDensity](../../../../../../sources/v2/MathlibExt.md)
