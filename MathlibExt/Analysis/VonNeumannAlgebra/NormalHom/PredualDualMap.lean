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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom

/-!
# The actual predual pullback's dual is the original normal map

Continuous functional precomposition by the constructed predual pullback
is its bounded dual map. The existing original normal-functional evaluation
isometries identify that dual map with the same original normal homomorphism.
Every value is literal evaluation at f(x). No predual quotient, dual
surjectivity, closed image or inverse/model certificate is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The literal dual of original predual pullback agrees with the original map under actual evaluation. -/
theorem predualPullback_dual_evaluation (f : NormalStarAlgHom M N) (x : M) :
    ((ContinuousLinearMap.compL ℂ (normalFunctionalSpace N) (normalFunctionalSpace M) ℂ).flip
      f.predualPullback) (normalFunctionalEvaluationEquiv M x) =
        normalFunctionalEvaluationEquiv N (f x) := by
  apply ContinuousLinearMap.ext
  intro φ
  change normalFunctionalEvaluationEquiv M x (f.predualPullback φ) =
    normalFunctionalEvaluationEquiv N (f x) φ
  rw [normalFunctionalEvaluationEquiv_apply, normalFunctionalEvaluationEquiv_apply,
    f.predualPullback_apply]

end

end VonNeumannAlgebra.NormalStarAlgHom
