/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeneralArcTopology
import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Arc covers by finite families

The two components `Spec A → Spec (A × A)` jointly cover `Spec (A × A)` in the arc topology,
although for nonzero `A` neither does alone: a point with values in a valuation ring factors
through one of them, because a domain has no idempotents other than `0` and `1`. The empty family covers the empty
scheme, which has no valuation points.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
open MathlibExt.AlgebraicGeometry.GeneralArcTopology

namespace MathlibExtTest.GeneralArcTopology

variable (A : Type) [CommRing A]

/-- The two projections `A × A → A`. -/
def projection : Bool → (A × A →+* A)
  | true => RingHom.fst A A
  | false => RingHom.snd A A

/-- The two components `Spec A → Spec (A × A)`. -/
noncomputable def component (b : Bool) : affine (.of A) ⟶ affine (.of (A × A)) :=
  Spec.map (CommRingCat.ofHom (projection A b))

/-- `a ↦ φ (a, 0)`, a ring map when `φ (1, 0) = 1`. -/
def leftPart {V : Type} [CommRing V] (φ : A × A →+* V) (h : φ (1, 0) = 1) : A →+* V where
  toFun a := φ (a, 0)
  map_one' := h
  map_mul' a b := by
    change φ (a * b, 0) = φ (a, 0) * φ (b, 0)
    rw [← map_mul, Prod.mk_mul_mk, zero_mul]
  map_zero' := by
    change φ (0, 0) = 0
    rw [Prod.mk_zero_zero, map_zero]
  map_add' a b := by
    change φ (a + b, 0) = φ (a, 0) + φ (b, 0)
    rw [← map_add, Prod.mk_add_mk, add_zero]

/-- `a ↦ φ (0, a)`, a ring map when `φ (0, 1) = 1`. -/
def rightPart {V : Type} [CommRing V] (φ : A × A →+* V) (h : φ (0, 1) = 1) : A →+* V where
  toFun a := φ (0, a)
  map_one' := h
  map_mul' a b := by
    change φ (0, a * b) = φ (0, a) * φ (0, b)
    rw [← map_mul, Prod.mk_mul_mk, zero_mul]
  map_zero' := by
    change φ (0, 0) = 0
    rw [Prod.mk_zero_zero, map_zero]
  map_add' a b := by
    change φ (0, a + b) = φ (0, a) + φ (0, b)
    rw [← map_add, Prod.mk_add_mk, add_zero]

/-- A ring map from `A × A` to a domain factors through one of the two projections. -/
theorem factors {V : Type} [CommRing V] [IsDomain V] (φ : A × A →+* V) :
    ∃ b : Bool, ∃ ψ : A →+* V, ψ.comp (projection A b) = φ := by
  have hidem : IsIdempotentElem (φ (1, 0)) := by
    unfold IsIdempotentElem
    rw [← map_mul, Prod.mk_mul_mk, one_mul, zero_mul]
  have hsum : φ (1, 0) + φ (0, 1) = 1 := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk_one_one, map_one]
  rcases hidem.eq_zero_or_one with h | h
  · have h1 : φ (0, 1) = 1 := by rw [h, zero_add] at hsum; exact hsum
    refine ⟨false, rightPart A φ h1, ?_⟩
    ext ⟨a, b⟩
    change φ (0, b) = φ (a, b)
    have ha : φ (a, 0) = 0 := by
      rw [show ((a : A), (0 : A)) = (a, 0) * (1, 0) by simp, map_mul, h, mul_zero]
    rw [show ((a : A), b) = (a, 0) + (0, b) by simp, map_add, ha, zero_add]
  · have h0 : φ (0, 1) = 0 := by rw [h] at hsum; exact add_eq_left.mp hsum
    refine ⟨true, leftPart A φ h, ?_⟩
    ext ⟨a, b⟩
    change φ (a, 0) = φ (a, b)
    have hb : φ (0, b) = 0 := by
      rw [show ((0 : A), b) = (0, b) * (0, 1) by simp, map_mul, h0, mul_zero]
    rw [show ((a : A), b) = (a, 0) + (0, b) by simp, map_add, hb, add_zero]

/-- The two components jointly cover `Spec (A × A)` in the arc topology. -/
theorem components_isJointArcCover :
    IsJointArcCover (Presieve.ofArrows (fun _ : Bool => affine (.of A)) (component A)) := by
  refine ⟨Bool, inferInstance, fun _ => affine (.of A), component A,
    fun b => Presieve.ofArrows.mk b, fun V x => ?_⟩
  obtain ⟨b, ψ, hψ⟩ := factors A (Spec.preimage x).hom
  refine ⟨b, ⟨⟨⟨V, RingHom.id V.ring, RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩,
    Spec.map (CommRingCat.ofHom ψ), ?_⟩⟩⟩
  change Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (projection A b)) =
    Spec.map (𝟙 _) ≫ x
  rw [Spec.map_id, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ,
    CommRingCat.ofHom_hom]
  exact Spec.map_preimage x

/-- The empty scheme, as a quasi-compact quasi-separated scheme. -/
def emptyScheme : QcqsScheme where
  scheme := ∅
  compact := inferInstance
  quasiSeparated := ⟨fun _ _ _ _ _ _ => (Set.toFinite _).isCompact⟩

/-- The empty family covers the empty scheme. -/
theorem empty_isJointArcCover : IsJointArcCover (⊥ : Presieve emptyScheme) := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, fun i => i.elim, fun i => i.elim, fun V x => ?_⟩
  exact (IsEmpty.false (α := (∅ : Scheme))
    (x.base (show Spec (.of V.ring) from ⟨⊥, Ideal.isPrime_bot⟩))).elim

end MathlibExtTest.GeneralArcTopology
