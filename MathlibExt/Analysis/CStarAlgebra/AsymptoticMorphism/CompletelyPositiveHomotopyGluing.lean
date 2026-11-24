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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositiveHomotopy
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositivePostcomp

/-!
# CPC preservation for the existing ordinary homotopy gluing

The existing matching pair family is postcomposed by the existing glue hom.
This proves CPC for the exact ordinary transitive homotopy family; no second
glued family or CPC transitivity operation is defined.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction
namespace Homotopy

open ContinuousMap.IntervalGluing

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {phi psi chi : CompletelyPositiveContraction A B}

/-- The exact family stored by the existing ordinary transitive homotopy is
CPC at every finite time. -/
theorem trans_family_isCompletelyPositiveContraction
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    IsCompletelyPositiveContraction
      ((H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).family) := by
  let glued := (H.matchingPairFamily K).postcomp
    (ContinuousMap.IntervalGluing.glueHom (B := B))
  have hCPC := glued.completelyPositiveContraction
  change IsCompletelyPositiveContraction
    (AsymptoticMorphism.postcomp
      (AsymptoticMorphism.Homotopy.pairFamily
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy)
      (ContinuousMap.IntervalGluing.glueHom (B := B)))
  simpa only [glued,
    CompletelyPositiveContraction.postcomp_toAsymptoticMorphism,
    matchingPairFamily_toAsymptoticMorphism] using hCPC

end Homotopy
end CompletelyPositiveContraction
end AsymptoticMorphism
