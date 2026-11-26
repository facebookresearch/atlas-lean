/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

Deicyde/diophantine-z-q (https://github.com/Deicyde/diophantine-z-q), commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`:

* the statements `AxSenTate` and `TateTwistInvariants` of Tate's two theorems over finite
  extensions of `ℚ_p`, the comparison `galois_smul_eq_cpAct` of two constructions of the Galois
  action on `ℂ_p`, and the passage `eigenvector_of_twisted_fixed` from twisted invariants to
  eigenvectors of the cyclotomic character:
  Copyright 2026 the contributors to Deicyde/diophantine-z-q.
  Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
* the closedness `isClosed_range_fieldToCp` of a finite extension of `ℚ_p` in `ℂ_p`:
  Copyright 2026 the contributors to Deicyde/diophantine-z-q.
  Copyright (c) 2026 Jack McCarthy. All rights reserved.
  Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
  Authors: Jack McCarthy (AI-assisted)

Changes made here: ported to Lean 4.36.0 and Mathlib v4.36.0, restated over `completionGalois`
and `cyclotomicScalar` of `MathlibExt.AlgebraicGeometry.HodgeTateComparison`, with the proofs
reduced to `MathlibExt.NumberTheory.Padics.CyclotomicEigenspaceVanishing`.
-/

module

public import MathlibExt.AlgebraicGeometry.HodgeTateComparison
public import MathlibExt.NumberTheory.Padics.CyclotomicEigenspaceVanishing
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Galois invariants of `ℂ_p` and of its Tate twists

Let `K` be a finite extension of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`, and let `ℂ_p` be the
completion of `ℚ̄_p`. The group `Gal(ℚ̄_p / ℚ_p)` acts on `ℂ_p` by
`MathlibExt.AlgebraicGeometry.HodgeTateComparison.completionGalois`, and on the Tate twist
`ℂ_p(i)` by `x ↦ χ(σ) ^ i • σ x`, where `χ(σ) = cyclotomicScalar p σ` is the `p`-adic cyclotomic
character. We prove

* `ℂ_p ^ Gal(ℚ̄_p / K) = K` (the Ax–Sen–Tate theorem), and
* `ℂ_p(i) ^ Gal(ℚ̄_p / K) = 0` for `i ≠ 0`.

These are the statements about `H⁰` in J. Tate, *p-divisible groups*, Proc. Conf. Local Fields
(Driebergen 1966), Springer 1967, §3.3: `H⁰(𝒢, C) = K` in Theorem 1, and `H⁰(𝒢, C(χ^i)) = 0` in
Theorem 2 applied to the character `χ^i`, both for `K` finite over `ℚ_p`.
The statements of these theorems about `H¹` are not treated here. See also S. Sen, *On
automorphisms of local fields*, Ann. of Math. 90 (1969), 33–46, and J. Ax, *Zeros of
polynomials over local fields — The Galois action*, J. Algebra 15 (1970), 417–428.

## Main results

* `MathlibExt.AlgebraicGeometry.HodgeTateComparison.completionGalois_apply_eq_smul`: the
  completed action agrees with the action `PadicComplex.mulSemiringAction` of
  `MathlibExt.NumberTheory.Padics.CyclotomicEigenspaceVanishing`.
* `MathlibExt.AlgebraicGeometry.HodgeTateComparison.cyclotomicScalar_zpow`: the powers of
  `cyclotomicScalar p σ` are the images in `ℚ_p` of the powers of the cyclotomic character.
* `PadicComplex.fixedPoints_eq_range`: `ℂ_p ^ Gal(ℚ̄_p / K) = K`.
* `PadicComplex.fixedPoints_twist_eq_singleton_zero`: `ℂ_p(i) ^ Gal(ℚ̄_p / K) = 0` for `i ≠ 0`.

## Proof

Both actions on `ℂ_p` are continuous and extend the action on `ℚ̄_p`, so they agree. The closure
form of the Ax–Sen–Tate theorem and the vanishing of the cyclotomic eigenspaces over `K` are
`PadicComplex.forall_smul_eq_self_iff_mem_closure` and
`PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul`; a finite
extension of `ℚ_p` is closed in `ℂ_p`, and an invariant of `ℂ_p(i)` is an eigenvector with
eigencharacter `χ ^ (-i)`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HodgeTateComparison

variable (p : ℕ) [Fact p.Prime]

/-- The completed Galois action `completionGalois p σ` on `ℂ_p` is the action `σ • x` of
`PadicComplex.mulSemiringAction`: both are continuous and extend the action of `σ` on `ℚ̄_p`. -/
theorem completionGalois_apply_eq_smul (σ : Galois p) (x : ℂ_[p]) :
    completionGalois p σ x = σ • x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_completionGalois p σ) (PadicComplex.continuous_smul_left p σ)
  | ih a => exact (completionGalois_coe p σ a).trans (PadicComplex.smul_coe p σ a).symm

/-- `cyclotomicScalar p σ` is the image in `ℚ_p` of the `p`-adic cyclotomic character of `σ`. -/
theorem cyclotomicScalar_eq_coe (σ : Galois p) :
    cyclotomicScalar p σ =
      ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) :=
  rfl

/-- The `i`-th power of `cyclotomicScalar p σ` is the image in `ℚ_p` of the `i`-th power of the
`p`-adic cyclotomic character of `σ`. -/
theorem cyclotomicScalar_zpow (σ : Galois p) (i : ℤ) :
    cyclotomicScalar p σ ^ i =
      ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) := by
  have h := congrArg (fun u : ℚ_[p]ˣ => (u : ℚ_[p]))
    (map_zpow (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom)
      (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv) i)
  simp only [Units.val_zpow_eq_zpow_val, Units.coe_map] at h
  exact h.symm

end MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace PadicComplex

open MathlibExt.AlgebraicGeometry.HodgeTateComparison

variable (p : ℕ) [Fact p.Prime]

/-- A finite extension of `ℚ_p` inside `ℚ̄_p` is closed in `ℂ_p`. -/
private theorem isClosed_range_coe_of_finiteDimensional (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    IsClosed (Set.range fun y : K => ((y : PadicAlgCl p) : ℂ_[p])) :=
  (LinearMap.range ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp
    K.val).toLinearMap).isClosed_of_finiteDimensional

/-- **The Ax–Sen–Tate theorem**, elementwise: for `K` finite over `ℚ_p` inside `ℚ̄_p`, an element
`x ∈ ℂ_p` satisfies `completionGalois p σ x = x` for all `σ ∈ Gal(ℚ̄_p / K)` if and only if `x` is
the image of an element of `K`. -/
theorem forall_completionGalois_eq_self_iff_mem_range
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (x : ℂ_[p]) :
    (∀ σ ∈ K.fixingSubgroup, completionGalois p σ x = x) ↔
      x ∈ Set.range fun y : K => ((y : PadicAlgCl p) : ℂ_[p]) := by
  simp only [completionGalois_apply_eq_smul]
  rw [← (isClosed_range_coe_of_finiteDimensional p K).closure_eq]
  exact forall_smul_eq_self_iff_mem_closure p K x

/-- **The Ax–Sen–Tate theorem**: `ℂ_p ^ Gal(ℚ̄_p / K) = K` for `K` finite over `ℚ_p` inside
`ℚ̄_p`. The elements of `ℂ_p` fixed by every `σ ∈ Gal(ℚ̄_p / K)`, acting by
`completionGalois p σ`, are exactly the images of the elements of `K`. This is the statement
`H⁰(𝒢, C) = K` of J. Tate, *p-divisible groups*, 1967, §3.3, Theorem 1, for such `K`. -/
theorem fixedPoints_eq_range
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    {x : ℂ_[p] | ∀ σ ∈ K.fixingSubgroup, completionGalois p σ x = x} =
      Set.range fun y : K => ((y : PadicAlgCl p) : ℂ_[p]) :=
  Set.ext (forall_completionGalois_eq_self_iff_mem_range p K)

/-- **Tate's theorem on the twists of `ℂ_p`**, elementwise: for `K` finite over `ℚ_p` inside
`ℚ̄_p` and `i ≠ 0`, if `x ∈ ℂ_p` satisfies `cyclotomicScalar p σ ^ i • completionGalois p σ x = x`
for every `σ ∈ Gal(ℚ̄_p / K)`, then `x = 0`. -/
theorem eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {i : ℤ} (hi : i ≠ 0)
    {x : ℂ_[p]}
    (hx : ∀ σ ∈ K.fixingSubgroup, cyclotomicScalar p σ ^ i • completionGalois p σ x = x) :
    x = 0 := by
  refine eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul p K (-i)
    (neg_ne_zero.mpr hi) x fun σ hσ => ?_
  rw [← completionGalois_apply_eq_smul, ← cyclotomicScalar_eq_coe]
  set a := algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ)
  have ha : a ≠ 0 := (map_ne_zero _).mpr (cyclotomicScalar_ne_zero p σ)
  have h1 : a ^ i * completionGalois p σ x = x := by
    rw [← map_zpow₀, ← Algebra.smul_def]
    exact hx σ hσ
  calc completionGalois p σ x = a ^ (-i) * (a ^ i * completionGalois p σ x) := by
        rw [← mul_assoc, ← zpow_add₀ ha, neg_add_cancel, zpow_zero, one_mul]
    _ = a ^ (-i) * x := by rw [h1]

/-- **Tate's theorem on the twists of `ℂ_p`**: `ℂ_p(i) ^ Gal(ℚ̄_p / K) = 0` for `i ≠ 0` and `K`
finite over `ℚ_p` inside `ℚ̄_p`. Here `σ ∈ Gal(ℚ̄_p / K)` acts on `ℂ_p(i)` by
`x ↦ χ(σ) ^ i • σ x`, with `σ x = completionGalois p σ x` and `χ(σ) = cyclotomicScalar p σ` the
`p`-adic cyclotomic character. This is the statement `H⁰(𝒢, C(χ^i)) = 0` of J. Tate,
*p-divisible groups*, 1967, §3.3, Theorem 2, applied to the character `χ^i`, for such `K`. -/
theorem fixedPoints_twist_eq_singleton_zero
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {i : ℤ}
    (hi : i ≠ 0) :
    {x : ℂ_[p] | ∀ σ ∈ K.fixingSubgroup, cyclotomicScalar p σ ^ i • completionGalois p σ x = x} =
      {0} := by
  ext x
  refine ⟨fun hx =>
    eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self p K
      hi hx, ?_⟩
  rintro rfl σ -
  rw [map_zero, smul_zero]

end PadicComplex
