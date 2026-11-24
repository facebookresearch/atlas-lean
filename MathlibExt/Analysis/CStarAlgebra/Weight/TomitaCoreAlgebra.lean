/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreTomita
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# The original algebra on the actual weighted GNS core

The source two-square-finite star algebra is identified with its literal
image in the actual weight Hilbert completion. Its original product and
star transport through that existing linear equivalence. The image keeps
its original weighted addition, complex scalar action, inner product and
norm. The resulting nonunital ring and star structures have exactly the
original source multiplication and star values.

Only algebraic structures are transported. Boundedness or continuity of
star and a normed-ring product estimate are not supplied. The original
left-Hilbert-algebra density, star closability, associated algebra/weight
and modular polar source conclusions remain separate obligations.
Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the
original Aφ paragraph, preserved OCR 14358--14386.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The actual weighted core product is the original ambient algebra product under its fixed image map. -/
def Weight.tomitaCoreProduct (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ η : φ.tomitaCore) : φ.tomitaCore :=
  φ.tomitaCoreEquiv hφ ((φ.tomitaCoreEquiv hφ).symm ξ * (φ.tomitaCoreEquiv hφ).symm η)

/-- Inverse image of the weighted product is exactly the original two-square algebra product. -/
theorem Weight.tomitaCoreProduct_inverse (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ η : φ.tomitaCore) :
    (φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreProduct hφ ξ η) =
      (φ.tomitaCoreEquiv hφ).symm ξ * (φ.tomitaCoreEquiv hφ).symm η := by
  exact (φ.tomitaCoreEquiv hφ).symm_apply_apply _

/-- Original source elements retain their actual original multiplication in the weighted image. -/
theorem Weight.tomitaCoreProduct_original (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x y : φ.finiteStarSquareSubalgebra) :
    φ.tomitaCoreProduct hφ (φ.tomitaCoreEquiv hφ x) (φ.tomitaCoreEquiv hφ y) =
      φ.tomitaCoreEquiv hφ (x * y) := by
  change φ.tomitaCoreEquiv hφ
    ((φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreEquiv hφ x) *
      (φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreEquiv hφ y)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- The original algebraic ring laws use the existing weighted image addition and scalar structures. -/
@[instance_reducible]
def Weight.tomitaCoreNonUnitalRing (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    NonUnitalRing φ.tomitaCore := by
  letI : Mul φ.tomitaCore := ⟨φ.tomitaCoreProduct hφ⟩
  let e := (φ.tomitaCoreEquiv hφ).symm
  exact Function.Injective.nonUnitalRing e e.injective
    (map_zero e) (fun ξ η => map_add e ξ η)
    (fun ξ η => φ.tomitaCoreProduct_inverse hφ ξ η)
    (fun ξ => map_neg e ξ) (fun ξ η => map_sub e ξ η)
    (fun n ξ => map_nsmul e n ξ) (fun n ξ => map_zsmul e n ξ)

/-- The transported ring keeps exactly the additive group underlying the existing weighted norm. -/
theorem Weight.tomitaCoreNonUnitalRing_addGroup (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    (φ.tomitaCoreNonUnitalRing hφ).toAddCommGroup =
      (inferInstance : AddCommGroup φ.tomitaCore) :=
  rfl

/-- The original weighted core star is its already constructed pre-Tomita involution. -/
@[instance_reducible]
def Weight.tomitaCoreStar (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) : Star φ.tomitaCore where
  star := φ.preTomitaCore hφ

/-- Inverse image of the weighted star is the original source algebra star. -/
theorem Weight.preTomitaCore_inverse (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore) :
    (φ.tomitaCoreEquiv hφ).symm (φ.preTomitaCore hφ ξ) =
      star ((φ.tomitaCoreEquiv hφ).symm ξ) := by
  change (φ.tomitaCoreEquiv hφ).symm
    (φ.tomitaCoreEquiv hφ (star ((φ.tomitaCoreEquiv hφ).symm ξ))) = _
  exact (φ.tomitaCoreEquiv hφ).symm_apply_apply _

/-- Original star-ring laws hold on the actual weighted algebra with its original addition. -/
@[instance_reducible]
def Weight.tomitaCoreStarRing (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    StarRing φ.tomitaCore := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  let e := (φ.tomitaCoreEquiv hφ).symm
  exact Function.Injective.starRing e e.injective
    (fun ξ => φ.preTomitaCore_inverse hφ ξ)
    (fun ξ η => map_add e ξ η)
    (fun ξ η => φ.tomitaCoreProduct_inverse hφ ξ η)

/-- The weighted source star has its original conjugate complex-scalar compatibility. -/
theorem Weight.tomitaCoreStarModule (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreStar hφ;
    StarModule ℂ φ.tomitaCore := by
  let := φ.tomitaCoreStar hφ
  let e := (φ.tomitaCoreEquiv hφ).symm
  exact Function.Injective.starModule e ℂ e.injective
    (fun ξ => φ.preTomitaCore_inverse hφ ξ)
    (fun c ξ => e.map_smul c ξ)

/-- The same existing complex scalar action is compatible with original product in its first factor. -/
theorem Weight.tomitaCoreProduct_smul_left (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (c : ℂ) (ξ η : φ.tomitaCore) :
    φ.tomitaCoreProduct hφ (c • ξ) η = c • φ.tomitaCoreProduct hφ ξ η := by
  apply (φ.tomitaCoreEquiv hφ).symm.injective
  simpa only [φ.tomitaCoreProduct_inverse, map_smul] using
    smul_mul_assoc c ((φ.tomitaCoreEquiv hφ).symm ξ) ((φ.tomitaCoreEquiv hφ).symm η)

/-- The same existing complex scalar action is compatible with original product in its second factor. -/
theorem Weight.tomitaCoreProduct_smul_right (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (c : ℂ) (ξ η : φ.tomitaCore) :
    φ.tomitaCoreProduct hφ ξ (c • η) = c • φ.tomitaCoreProduct hφ ξ η := by
  apply (φ.tomitaCoreEquiv hφ).symm.injective
  simpa only [φ.tomitaCoreProduct_inverse, map_smul] using
    mul_smul_comm c ((φ.tomitaCoreEquiv hφ).symm ξ) ((φ.tomitaCoreEquiv hφ).symm η)

/-- The original source algebra maps as the same actual nonunital star algebra into its weighted image. -/
def Weight.toTomitaCoreStarAlgHom (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.finiteStarSquareSubalgebra →⋆ₙₐ[ℂ] φ.tomitaCore := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  refine
    { toFun := φ.tomitaCoreEquiv hφ
      map_zero' := map_zero (φ.tomitaCoreEquiv hφ)
      map_add' := fun x y => map_add (φ.tomitaCoreEquiv hφ) x y
      map_mul' := fun x y => (φ.tomitaCoreProduct_original hφ x y).symm
      map_smul' := fun c x => (φ.tomitaCoreEquiv hφ).map_smul c x
      map_star' := fun x => (φ.preTomitaCore_apply hφ x).symm }

/-- The actual inverse weighted-core identification retains the original nonunital algebra and star. -/
def Weight.fromTomitaCoreStarAlgHom (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCore →⋆ₙₐ[ℂ] φ.finiteStarSquareSubalgebra := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  refine
    { toFun := (φ.tomitaCoreEquiv hφ).symm
      map_zero' := map_zero (φ.tomitaCoreEquiv hφ).symm
      map_add' := fun ξ η => map_add (φ.tomitaCoreEquiv hφ).symm ξ η
      map_mul' := fun ξ η => φ.tomitaCoreProduct_inverse hφ ξ η
      map_smul' := fun c ξ => (φ.tomitaCoreEquiv hφ).symm.map_smul c ξ
      map_star' := fun ξ => φ.preTomitaCore_inverse hφ ξ }

end

end CStarAlgebra.ScalarWeight
