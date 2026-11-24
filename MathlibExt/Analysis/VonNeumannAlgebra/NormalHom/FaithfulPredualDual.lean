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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.PredualDualMap
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulBallImage

/-!
# Faithfulness makes the actual bounded dual of predual pullback isometric

The existing evaluation equivalences identify every source predual-dual
functional with an original algebra element x. The actual dual pullback
sends it to evaluation at f(x), and the faithful original star map preserves
its C-star norm. Thus the literal bounded dual is isometric. No quotient,
surjectivity, image-closedness or inverse/model certificate is an input.
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

/-- The literal dual of predual pullback preserves every original dual norm under faithfulness. -/
theorem predualPullback_dual_norm (f : NormalStarAlgHom M N) (hf : Function.Injective f)
    (F : StrongDual ℂ (normalFunctionalSpace M)) :
    ‖((ContinuousLinearMap.compL ℂ (normalFunctionalSpace N) (normalFunctionalSpace M) ℂ).flip
      f.predualPullback) F‖ = ‖F‖ := by
  let x : M := (normalFunctionalEvaluationEquiv M).symm F
  have hF : normalFunctionalEvaluationEquiv M x = F :=
    (normalFunctionalEvaluationEquiv M).apply_symm_apply F
  rw [← hF, f.predualPullback_dual_evaluation x]
  rw [(normalFunctionalEvaluationEquiv N).norm_map, (normalFunctionalEvaluationEquiv M).norm_map]
  exact NonUnitalStarAlgHom.norm_map f.toStarAlgHom hf x

/-- The same literal bounded dual map is isometric; no predual quotient property is assumed. -/
theorem predualPullback_dual_isometry (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Isometry ((ContinuousLinearMap.compL ℂ (normalFunctionalSpace N) (normalFunctionalSpace M) ℂ).flip
      f.predualPullback) :=
  AddMonoidHomClass.isometry_of_norm _ (f.predualPullback_dual_norm hf)

end

end VonNeumannAlgebra.NormalStarAlgHom
