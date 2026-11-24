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

public import MathlibExt.MeasureTheory.Function.BoundedMeasurable
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous functions as bounded measurable functions

On a compact Borel space, every complex-valued continuous function
is bounded and measurable.  This file packages the pointwise inclusion

`C(X, ℂ) →⋆ₐ[ℂ] BoundedMeasurableFunction X`

and proves that it is isometric.  The construction also covers the empty
compact space and installs no new instances.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace MathlibExt.MeasureTheory.Function
namespace BoundedMeasurableFunction

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

/-- A continuous complex-valued function on a compact Borel space, regarded
as a bounded measurable function. -/
noncomputable def ofContinuousMap (f : C(X, ℂ)) : BoundedMeasurableFunction X :=
  ⟨⟨(show PreLp (fun _ : X ↦ ℂ) from fun x ↦ f x), by
      change Memℓp (fun x ↦ f x) ∞
      rw [memℓp_infty_iff]
      refine ⟨‖f‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact f.norm_coe_le_norm x⟩,
    f.continuous.measurable⟩

/-- Including a continuous function in the bounded measurable functions preserves evaluation. -/
@[simp]
theorem ofContinuousMap_apply (f : C(X, ℂ)) (x : X) :
    ofContinuousMap f x = f x :=
  rfl

/-- The continuous-function inclusion, bundled as a unital complex
star-algebra homomorphism. -/
noncomputable def continuousMapStarAlgHom :
    C(X, ℂ) →⋆ₐ[ℂ] BoundedMeasurableFunction X where
  toFun := ofContinuousMap
  map_one' := by
    apply Subtype.ext
    apply lp.ext
    funext x
    rfl
  map_mul' f g := by
    apply Subtype.ext
    apply lp.ext
    funext x
    rfl
  map_zero' := by
    apply Subtype.ext
    apply lp.ext
    funext x
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply lp.ext
    funext x
    rfl
  commutes' c := by
    apply Subtype.ext
    apply lp.ext
    funext x
    rfl
  map_star' f := by
    apply Subtype.ext
    apply lp.ext
    funext x
    rfl

/-- The continuous-function inclusion preserves every pointwise value. -/
@[simp]
theorem continuousMapStarAlgHom_apply (f : C(X, ℂ)) (x : X) :
    continuousMapStarAlgHom f x = f x :=
  rfl

/-- The continuous-function inclusion has a measurable underlying function. -/
theorem continuousMapStarAlgHom_measurable (f : C(X, ℂ)) :
    Measurable fun x ↦ continuousMapStarAlgHom f x :=
  (continuousMapStarAlgHom f).measurable

/-- The inclusion preserves the compact sup norm, including when `X` is
empty. -/
@[simp]
theorem norm_continuousMapStarAlgHom (f : C(X, ℂ)) :
    ‖continuousMapStarAlgHom f‖ = ‖f‖ := by
  rw [BoundedMeasurableFunction.norm_eq_iSup_norm,
    ContinuousMap.norm_eq_iSup_norm]
  rfl

/-- The continuous-function inclusion preserves the supremum metric. -/
theorem isometry_continuousMapStarAlgHom :
    Isometry (continuousMapStarAlgHom (X := X)) :=
  AddMonoidHomClass.isometry_of_norm (continuousMapStarAlgHom (X := X))
    (norm_continuousMapStarAlgHom (X := X))

end

end BoundedMeasurableFunction
end MathlibExt.MeasureTheory.Function
