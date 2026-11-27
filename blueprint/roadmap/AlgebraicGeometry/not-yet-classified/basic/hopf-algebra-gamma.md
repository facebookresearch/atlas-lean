# Hopf Algebra Gamma

The global sections of an affine group scheme `φ : G ⟶ Spec R` are a commutative `R`-Hopf
algebra. This is the `Γ`-direction endpoint of the dictionary between affine group schemes and
commutative Hopf algebras, stated for an arbitrary structure morphism `φ` with the group structure
carried by the object `Over.mk φ` of schemes over `Spec R` — a statement Mathlib's
`Scheme.Over`-instance form cannot express directly. Not an instance, because `φ` is data that
instance search cannot recover from the goal.
