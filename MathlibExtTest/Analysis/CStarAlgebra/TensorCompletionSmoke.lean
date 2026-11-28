/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Completion
import MathlibExt.Analysis.CStarAlgebra.Module.Compact
import MathlibExt.Analysis.CStarAlgebra.NonUnitalCompletion
import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# Nonunital tensor and algebra-completion API examples

The coefficient algebra consists of functions vanishing at infinity. Its
actual left regular action supplies the internal tensor-product constructor;
no tensor model, norm certificate, or unital action is an input.
-/

noncomputable section
open scoped ZeroAtInfty CStarModule.Right RightActions
open CStarModule.InternalTensorProduct
namespace TensorCompletionSmoke

private abbrev Coefficients := C₀(ℝ, ℂ)

local instance : PartialOrder Coefficientsᵐᵒᵖ :=
  CStarAlgebra.spectralOrder Coefficientsᵐᵒᵖ
local instance : StarOrderedRing Coefficientsᵐᵒᵖ :=
  CStarAlgebra.spectralOrderedRing Coefficientsᵐᵒᵖ
local instance : CStarModule Coefficientsᵐᵒᵖ Coefficients := CStarModule.Right.selfModule

private abbrev action := CStarModule.AdjointableOperator.leftRegular (B := Coefficients)
private abbrev Radical := RadicalTensor (E₁ := Coefficients) action

local instance : NormedAddCommGroup Radical := radicalTensorNormedAddCommGroup action
local instance : NormedSpace ℂ Radical := radicalTensorNormedSpace action
local instance : SMul Coefficientsᵐᵒᵖ Radical := radicalRightAction action
local instance : CStarModule Coefficientsᵐᵒᵖ Radical := radicalTensorCStarModule action
private abbrev Tensor := CompletedTensor (E₁ := Coefficients) action
local instance : CStarModule Coefficientsᵐᵒᵖ Tensor := completedCStarModule action

-- Zero in either factor gives the actual zero in the completed radical quotient.
example (g : Coefficients) : completedPure action (0 : Coefficients) g = 0 := by
  simpa only [zero_smul] using
    completedPure_smul_left action (0 : ℂ) (0 : Coefficients) g

example (f : Coefficients) : completedPure action f (0 : Coefficients) = 0 := by
  simpa only [zero_smul] using
    completedPure_smul_right action (0 : ℂ) f (0 : Coefficients)

-- Balancing uses the computed nonunital left multiplication action.
example (f a g : Coefficients) :
    completedPure action (f <• a) g = completedPure action f (a * g) := by
  simpa only [action, CStarModule.AdjointableOperator.leftRegular_apply] using
    completedPure_balance action f a g

-- The completed module carries the actual coefficient-valued inner product.
example (f g : Coefficients) :
    CStarModule.rightInner (B := Coefficients)
        (completedPure action f g) (completedPure action f g) =
      CStarModule.rightInner (B := Coefficients) g
        (action (CStarModule.rightInner (B := Coefficients) f f) g) :=
  rightInner_completedPure action f f g g

section AlgebraCompletion

local instance : NonUnitalCStarAlgebra (UniformSpace.Completion Coefficients) :=
  CStarAlgebra.completionNonUnitalCStarAlgebra Coefficients

-- The nonunital algebra completion preserves the original involution.
example (f : Coefficients) :
    star (f : UniformSpace.Completion Coefficients) =
      ((star f : Coefficients) : UniformSpace.Completion Coefficients) :=
  CStarAlgebra.completionNonUnitalCStarAlgebra_star_coe Coefficients f

example (f : Coefficients) : ‖(f : UniformSpace.Completion Coefficients)‖ = ‖f‖ :=
  UniformSpace.Completion.norm_coe f

end AlgebraCompletion

-- The finite ring-equivalence API also works with nonunital coefficients and
-- empty matrix indices, without a unit-valued coordinate or matrix model.
example (M : Matrix (Fin 0) (Fin 0) Coefficients) :
    (CStarMatrix.ofMatrixNonUnitalRingEquiv (A := Coefficients) (n := Fin 0)).symm
      ((CStarMatrix.ofMatrixNonUnitalRingEquiv (A := Coefficients) (n := Fin 0)) M) = M :=
  RingEquiv.symm_apply_apply _ _

end TensorCompletionSmoke
