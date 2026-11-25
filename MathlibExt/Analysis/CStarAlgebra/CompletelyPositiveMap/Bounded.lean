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

public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Canonical
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bounded access to completely positive maps

Complete positivity gives the existing positive-linear-map class, whose
continuity is already proved in Mathlib. The constructor below simply
projects the existing positive continuous linear-map adapter.

No bound is added to the CP carrier. Operator-norm estimates use a supplied
pointwise bound, so the contraction specialization does not claim that an
arbitrary completely positive map is contractive or unital.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CompletelyPositiveMap

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]

/-- **Bounded linear map associated with a CP map.** A completely positive map `φ : A → B` between
nonunital complex C*-algebras with star-compatible partial orders is continuous. This is its
continuous complex-linear map, with the same values. -/
def toContinuousLinearMap (phi : A →CP B) : A →L[ℂ] B :=
  (PositiveContinuousLinearMap.ofClass phi).toContinuousLinearMap

/-- **Evaluation of the bounded CP map.** For nonunital complex C*-algebras `A` and `B` with
star-compatible partial orders, a completely positive map `φ : A → B`, and `a ∈ A`, its associated
continuous linear map evaluates to `φ(a)`. -/
@[simp]
theorem toContinuousLinearMap_apply (phi : A →CP B) (a : A) :
    phi.toContinuousLinearMap a = phi a :=
  rfl

/-- **Underlying linear map of a bounded CP map.** For a completely positive map `φ : A → B` between
nonunital complex C*-algebras with star-compatible partial orders, the associated continuous linear
map has exactly the original complex-linear map. -/
@[simp]
theorem toContinuousLinearMap_toLinearMap (phi : A →CP B) :
    phi.toContinuousLinearMap.toLinearMap = phi.toLinearMap :=
  rfl

/-- **Operator-norm bound for a CP map.** Let `φ : A → B` be completely positive between nonunital
complex C*-algebras with star-compatible partial orders. If `C ≥ 0` and `‖φ(a)‖ ≤ C ‖a‖` for every
`a ∈ A`, the operator norm of its associated continuous linear map is at most `C`. -/
theorem norm_toContinuousLinearMap_le (phi : A →CP B)
    {C : ℝ} (hC : 0 ≤ C) (hphi : ∀ a : A, ‖phi a‖ ≤ C * ‖a‖) :
    ‖phi.toContinuousLinearMap‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ hC hphi

/-- **Norm of a completely positive contraction.** For nonunital complex C*-algebras `A` and `B` with
star-compatible partial orders, a completely positive map `φ : A → B` satisfying `‖φ(a)‖ ≤ ‖a‖` for
every `a` has operator norm at most one. -/
theorem norm_toContinuousLinearMap_le_one (phi : A →CP B)
    (hphi : ∀ a : A, ‖phi a‖ ≤ ‖a‖) :
    ‖phi.toContinuousLinearMap‖ ≤ 1 := by
  apply norm_toContinuousLinearMap_le phi zero_le_one
  intro a
  simpa only [one_mul] using hphi a

end CompletelyPositiveMap
