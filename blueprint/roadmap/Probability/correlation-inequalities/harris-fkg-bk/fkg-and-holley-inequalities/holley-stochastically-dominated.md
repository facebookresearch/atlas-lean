# Holley's inequality

If `μ₁, μ₂ ≥ 0` on `{0,1}^E` have equal total mass and satisfy
the Holley lattice condition `μ₁(a) μ₂(b) ≤ μ₁(a ∧ b) μ₂(a ∨ b)`, then `measOfMass μ₁` is
stochastically dominated by `measOfMass μ₂`. Strict positivity, assumed in Holley's paper, is not
needed. See R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974); the
real-valued form is `StatMech.holley_dominates`, from Mathlib's `holley`.
