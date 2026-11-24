/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.Product
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The mixed-degree filtration of exterior powers of a product

For modules over a commutative ring, the exterior-product decomposition
gives complementary tensor degrees. Its component projections define a
descending filtration by the number of factors from the first summand.
Each successive quotient is the tensor product of the complementary
exterior powers.

The construction includes degree zero and both extreme weights, without
freeness or flatness assumptions.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum

universe u v w

namespace exteriorPower.ProductFiltration

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/-- Native tensor module groups keep their existing tensor monoid parent.
This supplies the group required by the native quotient-kernel equivalence. -/
local instance tensor_addCommGroup {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] : AddCommGroup (A ⊗[R] B) :=
  Module.addCommMonoidToAddCommGroup R

/-- The literal finite complementary-weight index, including both zero weights. -/
abbrev Index (m : ℕ) := {p : ℕ × ℕ // p.1 + p.2 = m}

abbrev Piece (m : ℕ) (p : Index m) := (⋀[R]^p.val.1 M) ⊗[R] (⋀[R]^p.val.2 N)

/-- The actual component of the existing exterior-product equivalence. -/
def coordinate (m : ℕ) (p : Index m) :
    (⋀[R]^m (M × N)) →ₗ[R] Piece R M N m p :=
  (DirectSum.component R (Index m) (Piece R M N m) p).comp
    (exteriorPower.productEquiv R M N m).toLinearMap

/-- The actual mixed-tensor injection, using the inverse original exterior-product map. -/
def injection (m : ℕ) (p : Index m) :
    Piece R M N m p →ₗ[R] (⋀[R]^m (M × N)) :=
  (exteriorPower.productEquiv R M N m).symm.toLinearMap.comp
    (DirectSum.lof R (Index m) (Piece R M N m) p)

theorem coordinate_injection_same (m : ℕ) (p : Index m) (z : Piece R M N m p) :
    coordinate R M N m p (injection R M N m p z) = z := by
  simp only [coordinate, injection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]

theorem coordinate_injection_ne (m : ℕ) (p p' : Index m) (h : p ≠ p')
    (z : Piece R M N m p') :
    coordinate R M N m p (injection R M N m p' z) = 0 := by
  simp only [coordinate, injection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, DirectSum.component.of,
    dif_neg (Ne.symm h)]

/-- At stage q, actual mixed coordinates of first degree smaller than q vanish. -/
def filtration (m q : ℕ) : Submodule R (⋀[R]^m (M × N)) where
  carrier := {z | ∀ p : Index m, p.val.1 < q → coordinate R M N m p z = 0}
  zero_mem' := by intro p _; exact map_zero _
  add_mem' := by
    intro x y hx hy p hp
    rw [map_add, hx p hp, hy p hp, add_zero]
  smul_mem' := by
    intro r z hz p hp
    rw [map_smul, hz p hp, smul_zero]

/-- Use the native group construction from the unchanged stage monoid and R-action.
Its parent monoid is exactly the one used by the native submodule maps. -/
local instance filtration_addCommGroup (m q : ℕ) :
    AddCommGroup (filtration R M N m q) := Module.addCommMonoidToAddCommGroup R

theorem filtration_antitone (m : ℕ) {q q' : ℕ} (h : q ≤ q') :
    filtration R M N m q' ≤ filtration R M N m q := by
  intro z hz p hp
  exact hz p (lt_of_lt_of_le hp h)

theorem filtration_zero (m : ℕ) : filtration R M N m 0 = ⊤ := by
  ext z
  change (∀ p : Index m, p.val.1 < 0 → coordinate R M N m p z = 0) ↔ True
  simp only [Nat.not_lt_zero, false_implies, implies_true]

/-- This is a finite filtration in the actual total exterior degree. -/
theorem filtration_eq_bot (m q : ℕ) (h : m < q) :
    filtration R M N m q = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  apply (exteriorPower.productEquiv R M N m).injective
  rw [map_zero]
  apply DirectSum.ext_component R
  intro p
  change coordinate R M N m p z = 0
  exact hz p (by have hp := p.property; omega)

/-- The actual mixed component in the qth successive grade. -/
def index (m q : ℕ) (hq : q ≤ m) : Index m := ⟨(q, m - q), by omega⟩

/-- Projection from the actual filtration stage onto its new mixed tensor component. -/
def gradeProjection (m q : ℕ) (hq : q ≤ m) :
    filtration R M N m q →ₗ[R] Piece R M N m (index m q hq) :=
  (coordinate R M N m (index m q hq)).comp (filtration R M N m q).subtype

/-- The original mixed injection lands in the actual filtration stage. -/
def gradeSection (m q : ℕ) (hq : q ≤ m) :
    Piece R M N m (index m q hq) →ₗ[R] filtration R M N m q :=
  (injection R M N m (index m q hq)).codRestrict (filtration R M N m q) (by
    intro z p hp
    apply coordinate_injection_ne
    intro h
    have hfirst := congrArg (fun p : Index m => p.val.1) h
    change p.val.1 = q at hfirst
    omega)

theorem gradeProjection_section (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) :
    gradeProjection R M N m q hq (gradeSection R M N m q hq z) = z :=
  coordinate_injection_same R M N m (index m q hq) z

theorem gradeProjection_surjective (m q : ℕ) (hq : q ≤ m) :
    Function.Surjective (gradeProjection R M N m q hq) :=
  fun z => ⟨gradeSection R M N m q hq z, gradeProjection_section R M N m q hq z⟩

/-- The next stage viewed as a submodule of the current stage. -/
def nextStage (m q : ℕ) : Submodule R (filtration R M N m q) :=
  (filtration R M N m (q + 1)).comap (filtration R M N m q).subtype

/-- The component projection has precisely the original next-stage kernel. -/
theorem gradeProjection_ker (m q : ℕ) (hq : q ≤ m) :
    (gradeProjection R M N m q hq).ker = nextStage R M N m q := by
  ext z
  change coordinate R M N m (index m q hq) z.val = 0 ↔
    ∀ p : Index m, p.val.1 < q + 1 → coordinate R M N m p z.val = 0
  constructor
  · intro hz p hp
    by_cases hpq : p.val.1 < q
    · exact z.property p hpq
    · have heq : p = index m q hq := by
        apply Subtype.ext
        apply Prod.ext <;> have hsum := p.property <;> dsimp [index] <;> omega
      subst p
      exact hz
  · intro hz
    exact hz (index m q hq) (by dsimp [index]; omega)

/-- The actual associated graded module is the quotient of adjacent original stages. -/
abbrev associatedGraded (m q : ℕ) :=
  filtration R M N m q ⧸ nextStage R M N m q

/-- Every actual filtration quotient is the original complementary exterior tensor. -/
def associatedGradedEquiv (m q : ℕ) (hq : q ≤ m) :
    associatedGraded R M N m q ≃ₗ[R]
      (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) :=
  by
    let eQ := Submodule.quotEquivOfEq (nextStage R M N m q)
      (gradeProjection R M N m q hq).ker (gradeProjection_ker R M N m q hq).symm
    let eP := (gradeProjection R M N m q hq).quotKerEquivOfSurjective
      (gradeProjection_surjective R M N m q hq)
    let e := eQ.trans eP
    exact
      { toFun := fun x => e x
        invFun := fun x => e.symm x
        left_inv := fun x => e.symm_apply_apply x
        right_inv := fun x => e.apply_symm_apply x
        map_add' := fun x y => e.map_add x y
        map_smul' := fun r x => e.map_smul r x }

/-- On an original stage representative, the grade map is the actual component. -/
theorem associatedGradedEquiv_mk (m q : ℕ) (hq : q ≤ m)
    (z : filtration R M N m q) :
    associatedGradedEquiv R M N m q hq (Submodule.Quotient.mk z) =
      coordinate R M N m (index m q hq) z.val := by
  let eQ := Submodule.quotEquivOfEq (nextStage R M N m q)
    (gradeProjection R M N m q hq).ker (gradeProjection_ker R M N m q hq).symm
  let eP := (gradeProjection R M N m q hq).quotKerEquivOfSurjective
    (gradeProjection_surjective R M N m q hq)
  have hQ : eQ (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    Submodule.quotEquivOfEq_mk (nextStage R M N m q)
      (gradeProjection R M N m q hq).ker (gradeProjection_ker R M N m q hq).symm z
  have hP : eP (Submodule.Quotient.mk z) = gradeProjection R M N m q hq z :=
    LinearMap.quotKerEquivOfSurjective_apply_mk (gradeProjection R M N m q hq)
      (gradeProjection_surjective R M N m q hq) z
  change eP (eQ (Submodule.Quotient.mk z)) = gradeProjection R M N m q hq z
  exact (congrArg eP hQ).trans hP

section Transport

universe z

variable {W : Type z} [AddCommGroup W] [Module R W] (e : W ≃ₗ[R] M × N)

/-- Transport the actual product filtration through a module decomposition. -/
def transportedFiltration (m q : ℕ) : Submodule R (⋀[R]^m W) :=
  (filtration R M N m q).comap (exteriorPower.mapEquiv R W m e).toLinearMap

/-- The transported stage uses the same native monoid-to-group construction. -/
local instance transportedFiltration_addCommGroup (m q : ℕ) :
    AddCommGroup (transportedFiltration R M N e m q) := Module.addCommMonoidToAddCommGroup R

theorem transportedFiltration_zero (m : ℕ) : transportedFiltration R M N e m 0 = ⊤ := by
  rw [transportedFiltration, filtration_zero, Submodule.comap_top]

theorem transportedFiltration_eq_bot (m q : ℕ) (h : m < q) :
    transportedFiltration R M N e m q = ⊥ := by
  rw [transportedFiltration, filtration_eq_bot R M N m q h, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr (exteriorPower.mapEquiv R W m e).injective

/-- The native submodule preimage equivalence, preserving the original carrier. -/
def transportedStageEquiv (m q : ℕ) :
    transportedFiltration R M N e m q ≃ₗ[R] filtration R M N m q :=
  (exteriorPower.mapEquiv R W m e).ofSubmodule' (filtration R M N m q)

def transportedNextStage (m q : ℕ) : Submodule R (transportedFiltration R M N e m q) :=
  (transportedFiltration R M N e m (q + 1)).comap
    (transportedFiltration R M N e m q).subtype

/-- The actual mixed projection after the original module decomposition. -/
def transportedGradeProjection (m q : ℕ) (hq : q ≤ m) :
    transportedFiltration R M N e m q →ₗ[R] Piece R M N m (index m q hq) :=
  (gradeProjection R M N m q hq).comp (transportedStageEquiv R M N e m q).toLinearMap

theorem transportedGradeProjection_surjective (m q : ℕ) (hq : q ≤ m) :
    Function.Surjective (transportedGradeProjection R M N e m q hq) :=
  (gradeProjection_surjective R M N m q hq).comp
    (transportedStageEquiv R M N e m q).surjective

/-- Transport preserves the actual adjacent-stage kernel, not just a named grade object. -/
theorem transportedGradeProjection_ker (m q : ℕ) (hq : q ≤ m) :
    (transportedGradeProjection R M N e m q hq).ker =
      transportedNextStage R M N e m q := by
  rw [transportedGradeProjection, LinearMap.ker_comp, gradeProjection_ker]
  ext x
  change ((transportedStageEquiv R M N e m q x : filtration R M N m q) :
      ⋀[R]^m (M × N)) ∈ filtration R M N m (q + 1) ↔
    exteriorPower.mapEquiv R W m e x.val ∈ filtration R M N m (q + 1)
  rfl

abbrev transportedAssociatedGraded (m q : ℕ) :=
  transportedFiltration R M N e m q ⧸ transportedNextStage R M N e m q

/-- The quotient of the original transported stages has the actual mixed tensor coordinate. -/
def transportedAssociatedGradedEquiv (m q : ℕ) (hq : q ≤ m) :
    transportedAssociatedGraded R M N e m q ≃ₗ[R]
      (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) :=
  by
    let eQ := Submodule.quotEquivOfEq (transportedNextStage R M N e m q)
      (transportedGradeProjection R M N e m q hq).ker
      (transportedGradeProjection_ker R M N e m q hq).symm
    let eP := (transportedGradeProjection R M N e m q hq).quotKerEquivOfSurjective
      (transportedGradeProjection_surjective R M N e m q hq)
    let eG := eQ.trans eP
    exact
      { toFun := fun x => eG x
        invFun := fun x => eG.symm x
        left_inv := fun x => eG.symm_apply_apply x
        right_inv := fun x => eG.apply_symm_apply x
        map_add' := fun x y => eG.map_add x y
        map_smul' := fun r x => eG.map_smul r x }

/-- The original grade class of a mixed tensor, through the native stage section. -/
def transportedMixedClass (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) : transportedAssociatedGraded R M N e m q :=
  Submodule.Quotient.mk
    ((transportedStageEquiv R M N e m q).symm (gradeSection R M N m q hq z))

theorem transportedAssociatedGradedEquiv_mk (m q : ℕ) (hq : q ≤ m)
    (z : transportedFiltration R M N e m q) :
    transportedAssociatedGradedEquiv R M N e m q hq (Submodule.Quotient.mk z) =
      transportedGradeProjection R M N e m q hq z := by
  let eQ := Submodule.quotEquivOfEq (transportedNextStage R M N e m q)
    (transportedGradeProjection R M N e m q hq).ker
    (transportedGradeProjection_ker R M N e m q hq).symm
  let eP := (transportedGradeProjection R M N e m q hq).quotKerEquivOfSurjective
    (transportedGradeProjection_surjective R M N e m q hq)
  have hQ : eQ (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    Submodule.quotEquivOfEq_mk (transportedNextStage R M N e m q)
      (transportedGradeProjection R M N e m q hq).ker
      (transportedGradeProjection_ker R M N e m q hq).symm z
  have hP : eP (Submodule.Quotient.mk z) = transportedGradeProjection R M N e m q hq z :=
    LinearMap.quotKerEquivOfSurjective_apply_mk (transportedGradeProjection R M N e m q hq)
      (transportedGradeProjection_surjective R M N e m q hq) z
  change eP (eQ (Submodule.Quotient.mk z)) = transportedGradeProjection R M N e m q hq z
  exact (congrArg eP hQ).trans hP

/-- The actual quotient grade coordinate recovers that original mixed tensor exactly. -/
theorem transportedMixedClass_equiv (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) :
    transportedAssociatedGradedEquiv R M N e m q hq
        (transportedMixedClass R M N e m q hq z) = z := by
  rw [transportedMixedClass, transportedAssociatedGradedEquiv_mk]
  change gradeProjection R M N m q hq
    ((transportedStageEquiv R M N e m q)
      ((transportedStageEquiv R M N e m q).symm (gradeSection R M N m q hq z))) = z
  rw [LinearEquiv.apply_symm_apply, gradeProjection_section]

theorem transportedMixedClass_ne_zero (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) (hz : z ≠ 0) :
    transportedMixedClass R M N e m q hq z ≠ 0 := by
  intro h
  have h' := transportedMixedClass_equiv R M N e m q hq z
  rw [h, map_zero] at h'
  exact hz h'.symm

end Transport

end exteriorPower.ProductFiltration

end
