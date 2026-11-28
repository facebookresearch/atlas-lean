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
# Isometric inclusion of compact continuous functions

On a compact Borel space `X`, every continuous complex-valued function is bounded and
measurable. Pointwise inclusion is the unital complex star homomorphism `C(X,ℂ) →
BoundedMeasurableFunction X`.

It preserves the supremum norm and metric. Empty compact spaces are included, and no Hausdorff
hypothesis is required.
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

/-- **Compact continuous function as a bounded measurable function.** Let `X` be a compact
topological space with its Borel measurable structure, without a Hausdorff or
nonempty-space assumption. `ofContinuousMap f` includes `f∈C(X,ℂ)` pointwise into bounded
measurable functions. -/
noncomputable def ofContinuousMap (f : C(X, ℂ)) : BoundedMeasurableFunction X :=
  ofBound (fun x ↦ f x) f.continuous.measurable ‖f‖ (fun x ↦ f.norm_coe_le_norm x)

/-- **Value of a compact continuous-function inclusion.** Let `X` be a compact topological
space with its Borel measurable structure, without a Hausdorff or nonempty-space
assumption. for `f∈C(X,ℂ)` and `x∈X`, `ofContinuousMap f x=f(x)`. -/
@[simp]
theorem ofContinuousMap_apply (f : C(X, ℂ)) (x : X) :
    ofContinuousMap f x = f x :=
  rfl

/-- **Unital star inclusion of compact continuous functions.** Let `X` be a compact
topological space with its Borel measurable structure, without a Hausdorff or
nonempty-space assumption. `continuousMapStarAlgHom : C(X,ℂ) →⋆ₐ[ℂ]
BoundedMeasurableFunction X` is the pointwise function inclusion. -/
noncomputable def continuousMapStarAlgHom :
    C(X, ℂ) →⋆ₐ[ℂ] BoundedMeasurableFunction X where
  toFun := ofContinuousMap
  map_one' := by
    apply BoundedMeasurableFunction.ext
    intro x
    rfl
  map_mul' f g := by
    apply BoundedMeasurableFunction.ext
    intro x
    rfl
  map_zero' := by
    apply BoundedMeasurableFunction.ext
    intro x
    rfl
  map_add' f g := by
    apply BoundedMeasurableFunction.ext
    intro x
    rfl
  commutes' c := by
    apply BoundedMeasurableFunction.ext
    intro x
    rfl
  map_star' f := by
    apply BoundedMeasurableFunction.ext
    intro x
    rfl

/-- **Pointwise value of the continuous-function star inclusion.** Let `X` be a compact
topological space with its Borel measurable structure, without a Hausdorff or
nonempty-space assumption. for `f∈C(X,ℂ)` and `x∈X`, `continuousMapStarAlgHom f x=f(x)`. -/
@[simp]
theorem continuousMapStarAlgHom_apply (f : C(X, ℂ)) (x : X) :
    continuousMapStarAlgHom f x = f x :=
  rfl

/-- **Measurable function underlying the compact continuous inclusion.** Let `X` be a compact
topological space with its Borel measurable structure, without a Hausdorff or
nonempty-space assumption. the underlying function of `continuousMapStarAlgHom f` is
measurable for every `f∈C(X,ℂ)`. -/
theorem continuousMapStarAlgHom_measurable (f : C(X, ℂ)) :
    Measurable fun x ↦ continuousMapStarAlgHom f x :=
  (continuousMapStarAlgHom f).measurable

/-- **Supremum norm retained by continuous-function inclusion.** Let `X` be a compact
topological space with its Borel measurable structure, without a Hausdorff or
nonempty-space assumption. for every `f∈C(X,ℂ)`, `‖continuousMapStarAlgHom f‖∞=‖f‖∞`. -/
@[simp]
theorem norm_continuousMapStarAlgHom (f : C(X, ℂ)) :
    ‖continuousMapStarAlgHom f‖ = ‖f‖ := by
  rw [BoundedMeasurableFunction.norm_eq_iSup_norm,
    ContinuousMap.norm_eq_iSup_norm]
  rfl

/-- **Metric isometry of the compact continuous inclusion.** Let `X` be a compact topological
space with its Borel measurable structure, without a Hausdorff or nonempty-space
assumption. `continuousMapStarAlgHom` is an isometry for the supremum-norm metrics. -/
theorem isometry_continuousMapStarAlgHom :
    Isometry (continuousMapStarAlgHom (X := X)) :=
  AddMonoidHomClass.isometry_of_norm (continuousMapStarAlgHom (X := X))
    (norm_continuousMapStarAlgHom (X := X))

end

end BoundedMeasurableFunction
end MathlibExt.MeasureTheory.Function
