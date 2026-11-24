/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.VanishingIdeal
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Basic

import Mathlib.Order.LatticeIntervals
import Mathlib.Topology.Order.Compact

/-!
# The literal asymptotic C-star algebra and quotient lifts

AsymptoticAlgebra B is the actual Cb([1,infty),B)/C0([1,infty),B)
quotient, using the stock bounded-continuous algebra, the constructed closed
star ideal, and the existing quotient C-star factory. Its norm is not changed.

A set-theoretic lifting of an actual homomorphism into this quotient gives a
raw nonlinear asymptotic family. Its four laws are derived from the actual
kernel criterion. No Source bound theorem or extra raw bound premise is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

universe uA uB

/-- The genuine quotient of bounded time-functions by those vanishing at infinity. -/
abbrev AsymptoticAlgebra (B : Type uB) [NonUnitalCStarAlgebra B] :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).Quotient

namespace AsymptoticAlgebra

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Explicit existing quotient C-star data. It is not globally registered. -/
@[instance_reducible]
def cStarAlgebra (B : Type uB) [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientCStarAlgebra

attribute [local instance] cStarAlgebra

/-- The actual quotient projection, with the preceding fixed quotient dictionaries. -/
def quotientMap (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticTime →ᵇ B) →⋆ₙₐ[ℂ] AsymptoticAlgebra B :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap

private theorem ray_cocompact_eq_atTop :
    cocompact AsymptoticTime = (atTop : Filter AsymptoticTime) := by
  let : OrderBot AsymptoticTime := Set.Ici.orderBot
  let : NoMaxOrder AsymptoticTime :=
    ⟨fun t =>
      ⟨⟨(t : ℝ) + 1, t.property.trans (le_add_of_nonneg_right zero_le_one)⟩,
        lt_add_one (t : ℝ)⟩⟩
  let : ClosedIciTopology AsymptoticTime :=
    ⟨fun t => (isClosed_Ici : IsClosed (Set.Ici (t : ℝ))).preimage
      continuous_subtype_val⟩
  let : CompactIccSpace AsymptoticTime :=
    ⟨fun {a b} => by
      apply Subtype.isCompact_iff.mpr
      have himage : Subtype.val '' (Set.Icc a b : Set AsymptoticTime) =
          Set.Icc (a : ℝ) (b : ℝ) := by
        ext x
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ht
        · intro hx
          exact ⟨⟨x, a.property.trans hx.1⟩, hx, rfl⟩
      rw [himage]
      exact isCompact_Icc⟩
  exact cocompact_eq_atTop

/-- The actual ideal on the closed ray is characterized by atTop vanishing. -/
theorem mem_vanishingIdeal_iff (f : AsymptoticTime →ᵇ B) :
    f ∈ BoundedContinuousFunction.vanishingIdeal AsymptoticTime B ↔
      Tendsto f atTop (nhds 0) := by
  rw [BoundedContinuousFunction.mem_vanishingIdeal_iff, ray_cocompact_eq_atTop]

/-- Zero in the real quotient is exactly vanishing at infinity. -/
theorem quotientMap_eq_zero_iff (f : AsymptoticTime →ᵇ B) :
    quotientMap B f = 0 ↔ Tendsto f atTop (nhds 0) := by
  change (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap f = 0 ↔ _
  rw [ClosedStarIdeal.quotientMap_eq_zero_iff, mem_vanishingIdeal_iff]

/-- Equality of quotient classes is precisely the vanishing-difference criterion. -/
theorem quotientMap_eq_iff (f g : AsymptoticTime →ᵇ B) :
    quotientMap B f = quotientMap B g ↔
      Tendsto (fun t => f t - g t) atTop (nhds 0) := by
  rw [← sub_eq_zero, ← map_sub, quotientMap_eq_zero_iff]
  rfl

/-- The canonical C0 inclusion has zero quotient class. -/
theorem quotientMap_toBCF (f : C₀(AsymptoticTime, B)) :
    quotientMap B f.toBCF = 0 :=
  ((BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap_eq_zero_iff
    f.toBCF).2 (BoundedContinuousFunction.toBCF_mem_vanishingIdeal f)

/-- Surjectivity is inherited from the actual Submodule quotient, not assumed. -/
theorem quotientMap_surjective (B : Type uB) [NonUnitalCStarAlgebra B] :
    Function.Surjective (quotientMap B) :=
  (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).quotientMap_surjective

/-- Any genuine set-theoretic lifting of a quotient hom yields a raw family.
F is arbitrary in the coefficient; no linearity or continuity-in-a is imposed. -/
def ofLift (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (F : A → AsymptoticTime →ᵇ B)
    (hF : ∀ a : A, quotientMap B (F a) = ρ a) : AsymptoticMorphism A B where
  toFun t a := F a t
  continuous_orbit a := (F a).continuous
  add_defect_tendsto a b := by
    have hzero : quotientMap B (F (a + b) - (F a + F b)) = 0 := by
      simp only [map_sub, map_add, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.add_apply])
  smul_defect_tendsto z a := by
    have hzero : quotientMap B (F (z • a) - z • F a) = 0 := by
      simp only [map_sub, map_smul, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply])
  mul_defect_tendsto a b := by
    have hzero : quotientMap B (F (a * b) - F a * F b) = 0 := by
      simp only [map_sub, map_mul, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply])
  star_defect_tendsto a := by
    have hzero : quotientMap B (F (star a) - star (F a)) = 0 := by
      simp only [map_sub, map_star, hF, sub_self]
    have h := (quotientMap_eq_zero_iff _).1 hzero
    exact h.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.star_apply])

/-- The lifting family has the original pointwise values. -/
@[simp]
theorem ofLift_apply (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (F : A → AsymptoticTime →ᵇ B)
    (hF : ∀ a : A, quotientMap B (F a) = ρ a)
    (t : AsymptoticTime) (a : A) : ofLift ρ F hF t a = F a t := by
  rfl

/-- Two set-theoretic liftings of the same quotient map are strictly equivalent. -/
theorem strictlyEquivalent_ofLift (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (F G : A → AsymptoticTime →ᵇ B)
    (hF : ∀ a : A, quotientMap B (F a) = ρ a)
    (hG : ∀ a : A, quotientMap B (G a) = ρ a) :
    AsymptoticMorphism.StrictlyEquivalent (ofLift ρ F hF) (ofLift ρ G hG) := by
  intro a
  have h := (quotientMap_eq_iff (F a) (G a)).1 ((hF a).trans (hG a).symm)
  simpa only [ofLift_apply] using h

/-- Actual quotient surjectivity supplies a set-theoretic lift by choice.
This choice constructs the family; it is not an output-model input. -/
def ofHom (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) : AsymptoticMorphism A B :=
  ofLift ρ
    (fun a => Classical.choose (quotientMap_surjective B (ρ a)))
    (fun a => Classical.choose_spec (quotientMap_surjective B (ρ a)))

/-- Characteristic values of the computed set-theoretic lift. -/
@[simp]
theorem ofHom_apply (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B)
    (t : AsymptoticTime) (a : A) :
    ofHom ρ t a =
      (Classical.choose (quotientMap_surjective B (ρ a)) : AsymptoticTime →ᵇ B) t := by
  rfl

end AsymptoticAlgebra
