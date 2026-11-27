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

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.BoundedHom
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The true C0 ideal in the bounded continuous function algebra

For an arbitrary topological space, the image of C0(X,B).toBCF is a closed
two-sided star ideal of the actual bounded continuous function algebra.
Closedness is the existing stock closed-range theorem. Ambient absorption uses
the real supremum norm, not an assumed limit for the bounded factor.

The coefficient algebra may be nonunital; no nonempty/local-compactness
assumption or replacement norm is introduced.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped ZeroAtInfty CStarAlgebra

noncomputable section

namespace BoundedContinuousFunction

universe uX uB uA uC

variable {X : Type uX} [TopologicalSpace X]
variable {B : Type uB} [NonUnitalCStarAlgebra B]

private theorem bounded_mul_tendsto_zero (a : X →ᵇ B) (f : X → B)
    (hf : Tendsto f (cocompact X) (nhds 0)) :
    Tendsto (fun x => a x * f x) (cocompact X) (nhds 0) := by
  refine squeeze_zero_norm (a := fun x => ‖a‖ * ‖f x‖) ?_ ?_
  · intro x
    exact (norm_mul_le (a x) (f x)).trans
      (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm x) (norm_nonneg (f x)))
  · simpa only [Function.comp_def, mul_zero] using
      (tendsto_norm_zero.comp hf).const_mul ‖a‖

private theorem tendsto_zero_mul_bounded (f : X → B)
    (hf : Tendsto f (cocompact X) (nhds 0)) (a : X →ᵇ B) :
    Tendsto (fun x => f x * a x) (cocompact X) (nhds 0) := by
  refine squeeze_zero_norm (a := fun x => ‖f x‖ * ‖a‖) ?_ ?_
  · intro x
    exact (norm_mul_le (f x) (a x)).trans
      (mul_le_mul_of_nonneg_left (a.norm_coe_le_norm x) (norm_nonneg (f x)))
  · simpa only [Function.comp_def, zero_mul] using
      (tendsto_norm_zero.comp hf).mul_const ‖a‖

private def vanishingSubalgebra (X : Type uX) [TopologicalSpace X]
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    NonUnitalStarSubalgebra ℂ (X →ᵇ B) where
  toNonUnitalSubalgebra :=
    { carrier := Set.range (ZeroAtInftyContinuousMap.toBCF : C₀(X, B) → X →ᵇ B)
      zero_mem' := ⟨0, rfl⟩
      add_mem' := by
        rintro f g ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, rfl⟩
      mul_mem' := by
        rintro f g ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f * g, rfl⟩
      smul_mem' := by
        rintro c f ⟨f, rfl⟩
        exact ⟨c • f, rfl⟩ }
  star_mem' := by
    rintro f ⟨f, rfl⟩
    exact ⟨star f, rfl⟩

/-- Let `X` be a topological space. Let `B` be a possibly nonunital complex C*-algebra.

The closed two-sided C0 ideal inside the BCF algebra. -/
@[no_expose]
def vanishingIdeal (X : Type uX) [TopologicalSpace X]
    (B : Type uB) [NonUnitalCStarAlgebra B] : ClosedStarIdeal (X →ᵇ B) where
  carrier := vanishingSubalgebra X B
  isClosed := ZeroAtInftyContinuousMap.isClosed_range_toBCF
  isTwoSided := by
    constructor
    · rintro a f ⟨f, rfl⟩
      let g : C₀(X, B) :=
        { toFun := fun x => a x * f x
          continuous_toFun := a.continuous.fun_mul f.continuous_toFun
          zero_at_infty' := bounded_mul_tendsto_zero a f (zero_at_infty f) }
      exact ⟨g, rfl⟩
    · rintro f ⟨f, rfl⟩ a
      let g : C₀(X, B) :=
        { toFun := fun x => f x * a x
          continuous_toFun := f.continuous_toFun.fun_mul a.continuous
          zero_at_infty' := tendsto_zero_mul_bounded f (zero_at_infty f) a }
      exact ⟨g, rfl⟩

/-- Let `X` be a topological space. Let `B` be a possibly nonunital complex C*-algebra.

Membership is precisely the cocompact vanishing property. -/
theorem mem_vanishingIdeal_iff (f : X →ᵇ B) :
    f ∈ vanishingIdeal X B ↔ Tendsto f (cocompact X) (nhds 0) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact zero_at_infty g
  · intro hf
    let g : C₀(X, B) :=
      { toContinuousMap := f.toContinuousMap
        zero_at_infty' := hf }
    exact ⟨g, rfl⟩

/-- Let `X` be a topological space. Let `B` be a possibly nonunital complex C*-algebra.

The set carrier is the image of C0, not an abstract ideal model. -/
theorem vanishingIdeal_carrier (X : Type uX) [TopologicalSpace X]
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (vanishingIdeal X B : Set (X →ᵇ B)) =
      Set.range (ZeroAtInftyContinuousMap.toBCF : C₀(X, B) → X →ᵇ B) := by
  rfl

/-- Let `X` be a topological space. Let `B` be a possibly nonunital complex C*-algebra.

The C0 inclusion lands in the constructed ideal. -/
theorem toBCF_mem_vanishingIdeal (f : C₀(X, B)) :
    f.toBCF ∈ vanishingIdeal X B :=
  (mem_vanishingIdeal_iff f.toBCF).2 (zero_at_infty f)

/-- Let `X` be a topological space. Let `A`, `C` be possibly nonunital complex C*-algebras.

Coefficient postcomposition carries the vanishing ideal into the target vanishing ideal for
every topological domain, including the empty one. -/
theorem compNonUnitalStarAlgHom_mapsTo_vanishingIdeal
    {A : Type uA} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₙₐ[ℂ] C) :
    Set.MapsTo (compNonUnitalStarAlgHom (X := X) φ)
      (vanishingIdeal X A) (vanishingIdeal X C) := by
  intro f hf
  apply (mem_vanishingIdeal_iff ((compNonUnitalStarAlgHom φ) f)).2
  have hf' := (mem_vanishingIdeal_iff f).1 hf
  have hφ : Continuous (φ : A → C) := map_continuous φ
  have hcomp : Tendsto (φ ∘ f) (cocompact X) (nhds 0) := by
    simpa only [map_zero] using
      (hφ.tendsto (0 : A)).comp hf'
  exact hcomp.congr fun x => (compNonUnitalStarAlgHom_apply φ f x).symm

#print axioms compNonUnitalStarAlgHom_mapsTo_vanishingIdeal

end BoundedContinuousFunction
