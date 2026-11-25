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
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-rank completely positive contractive approximation

The approximation witnesses are actual canonical completely positive maps,
with an explicit pointwise contraction bound and finite-dimensional linear
range. Source and target may be nonunital or zero. No nuclearity theorem,
selected approximation, matrix model or new order/norm instance is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CompletelyPositiveMap

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Finite-rank completely positive approximation.** For nonunital complex C*-algebras `A` and `B`, a
function `f : A → B` has this property when, for every finite `F ⊆ A` and every `ε > 0`, there is a
completely positive contraction `φ : A → B` with finite-dimensional complex-linear range such that
`‖φ(a) - f(a)‖ < ε` for every `a ∈ F`. Positivity uses the spectral orders of `A` and `B`. -/
def HasFiniteRankCPCApproximation (f : A → B) : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ phi : Canonical A B,
      (∀ a : A, ‖phi a‖ ≤ ‖a‖) ∧
      FiniteDimensional ℂ (LinearMap.range phi.toLinearMap) ∧
      ∀ a ∈ F, ‖phi a - f a‖ < ε

/-- **Finite-test characterization of finite-rank CP approximation.** For nonunital complex C*-algebras
`A` and `B` and a function `f : A → B`, finite-rank completely positive approximation is equivalent
to the following condition: for every finite `F ⊆ A` and `ε > 0`, a completely positive contraction
with finite-dimensional complex-linear range approximates `f` within `ε` at every point of `F`. Both
algebras carry their spectral orders. -/
theorem hasFiniteRankCPCApproximation_iff (f : A → B) :
    HasFiniteRankCPCApproximation f ↔
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : PartialOrder B := CStarAlgebra.spectralOrder B
       letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
       ∀ (F : Finset A) (ε : ℝ), 0 < ε →
         ∃ phi : Canonical A B,
           (∀ a : A, ‖phi a‖ ≤ ‖a‖) ∧
           FiniteDimensional ℂ (LinearMap.range phi.toLinearMap) ∧
           ∀ a ∈ F, ‖phi a - f a‖ < ε) :=
  Iff.rfl

end CompletelyPositiveMap
