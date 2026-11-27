/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.ComplexInvariants

/-!
# Tests for the Galois invariants of `ℂ_p` and of its Tate twists

The completed Galois action is Mathlib's extension of `σ` to the completion, and agrees with the
action of `PadicComplex.mulSemiringAction`. Both theorems are restated with Mathlib's completion
map and the coerced powers of `cyclotomicCharacter` only. The fixed points of `Gal(ℚ̄_p / ℚ_p)` in
`ℂ_p` are `ℚ_p`, those of `Gal(ℚ̄_p / ℚ_p(α))` contain `α`, and the twists `ℂ_p(1)`, `ℂ_p(-1)` and
the twists `ℂ_p(-i)` of the Hodge–Tate comparison have no nonzero invariants.
-/

open MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- `completionGalois p σ` is Mathlib's extension of `σ` to the completion `ℂ_p` of `ℚ̄_p`. -/
example (σ : Galois p) (x : ℂ_[p]) :
    completionGalois p σ x =
      UniformSpace.Completion.mapRingHom σ.toAlgHom.toRingHom (closure_isometry p σ).continuous x :=
  rfl

/-- The two constructions of the Galois action on `ℂ_p` agree. -/
example (σ : Galois p) (x : ℂ_[p]) : completionGalois p σ x = σ • x :=
  completionGalois_apply_eq_smul p σ x

/-- Theorem 1 stated with Mathlib's completion map. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (x : ℂ_[p])
    (hx : ∀ σ ∈ K.fixingSubgroup, UniformSpace.Completion.mapRingHom σ.toAlgHom.toRingHom
      (closure_isometry p σ).continuous x = x) :
    ∃ y : K, x = ((y : PadicAlgCl p) : ℂ_[p]) := by
  obtain ⟨y, hy⟩ := (PadicComplex.forall_completionGalois_eq_self_iff_mem_range p K x).1 hx
  exact ⟨y, hy.symm⟩

/-- Theorem 2 stated with Mathlib's completion map and the powers of `cyclotomicCharacter`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (i : ℤ)
    (hi : i ≠ 0) (x : ℂ_[p])
    (hx : ∀ σ ∈ K.fixingSubgroup,
      (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) •
        UniformSpace.Completion.mapRingHom σ.toAlgHom.toRingHom
          (closure_isometry p σ).continuous x = x) :
    x = 0 :=
  eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self
    p K hi fun σ hσ => by rw [cyclotomicScalar_zpow]; exact hx σ hσ

/-- `ℂ_p ^ Gal(ℚ̄_p / ℚ_p) = ℚ_p`. -/
example (x : ℂ_[p]) (hx : ∀ σ : Galois p, completionGalois p σ x = x) :
    ∃ q : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] q := by
  obtain ⟨y, rfl⟩ :=
    (PadicComplex.forall_completionGalois_eq_self_iff_mem_range p ⊥ x).1 fun σ _ => hx σ
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 y.2
  refine ⟨q, ?_⟩
  change ((y : PadicAlgCl p) : ℂ_[p]) = _
  rw [← hq, PadicComplex.coe_eq, ← IsScalarTower.algebraMap_apply]

/-- An element `α ∈ ℚ̄_p` is fixed in `ℂ_p` by `Gal(ℚ̄_p / ℚ_p(α))`. -/
example (α : PadicAlgCl p) (σ : Galois p)
    (hσ : σ ∈ (IntermediateField.adjoin ℚ_[p] {α}).fixingSubgroup) :
    completionGalois p σ (α : ℂ_[p]) = α := by
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {α}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  exact (PadicComplex.forall_completionGalois_eq_self_iff_mem_range p _ _).2
    ⟨⟨α, IntermediateField.mem_adjoin_simple_self ℚ_[p] α⟩, rfl⟩ σ hσ

/-- `ℂ_p(1)` has no nonzero `Gal(ℚ̄_p / K)`-invariants. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (x : ℂ_[p])
    (hx : ∀ σ ∈ K.fixingSubgroup, cyclotomicScalar p σ • completionGalois p σ x = x) : x = 0 :=
  eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self
    p K one_ne_zero (by simpa only [zpow_one] using hx)

/-- The twists `ℂ_p(-i)`, `i > 0`, of the Hodge–Tate comparison have no nonzero invariants. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {i : ℕ}
    (hi : i ≠ 0) (x : ℂ_[p])
    (hx : ∀ σ ∈ K.fixingSubgroup, tateScalar p σ i • completionGalois p σ x = x) : x = 0 :=
  eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self
    p K (i := -(i : ℤ)) (by simpa using hi) hx

/-- `ℂ_p(-1) ^ Gal(ℚ̄_p / K) = 0`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    {x : ℂ_[p] | ∀ σ ∈ K.fixingSubgroup,
      cyclotomicScalar p σ ^ (-1 : ℤ) • completionGalois p σ x = x} = {0} :=
  PadicComplex.fixedPoints_twist_eq_singleton_zero p K (by norm_num)
