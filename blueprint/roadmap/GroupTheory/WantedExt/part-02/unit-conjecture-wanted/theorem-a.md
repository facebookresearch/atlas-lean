---
article_id: af_76feaaa83caf6266c6a8cb29
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.GroupTheory.UnitConjectureWanted.UnitConjecture.theorem_A
---

# Theorem A

Statement of Theorem A:

Let P be the torsion-free group defined by the presentation
`⟨a,b | b⁻¹a²b = a⁻², a⁻¹b²a = b⁻²⟩`, and set `x = a²`, `y = b²`, `z = (ab)²`. Set
`p = (1 + x)(1 + y)(1 + z⁻¹)`, `q = x⁻¹y⁻¹ + x + y⁻¹z + z`,
`r = 1 + x + y⁻¹z + xyz`, `s = 1 + (x + x⁻¹ + y + y⁻¹)z⁻¹`.
Then `p + qa + rb + sab` is a non-trivial unit in the group ring `𝔽₂[P]`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.GroupTheory.UnitConjectureWanted](../../../../../sources/v2/WantedExt.md)
- G. Gardam, `A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_unit_conjecture`.
