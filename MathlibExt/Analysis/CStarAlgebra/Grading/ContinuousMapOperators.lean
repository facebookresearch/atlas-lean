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

public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap.ConstantOperators
public import MathlibExt.Analysis.CStarAlgebra.Grading.ContinuousMap
public import MathlibExt.Analysis.CStarAlgebra.Grading.Module.Self
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.GradedLeft

/-!
# Graded constant End homomorphisms on continuous sections

The actual pointwise module grading and actual constant unital End map use
the original coefficient orders and the original supremum norm. Their
literal pure-generator formula instantiates the shared graded left constructor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra CStarModule.Right RightActions

namespace CStarModuleGrading

universe uX uB uE

variable (X : Type uX) [TopologicalSpace X] [CompactSpace X]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
  [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {γ : CStarGrading B}

attribute [local instance] CStarModule.ContinuousMap.rightAction
  CStarModule.ContinuousMap.cstarModule

/-- **Homogeneous operators under constant extension.** Let `X` be a compact topological space, `B` a
graded nonunital complex C*-algebra, and `E` a complete right Hilbert `B`-module with compatible
generator `G`. Assume star-compatible orders on the opposite algebras of `B` and `C(X,B)`. If an
adjointable endomorphism `T` of `E` has degree `n ∈ ℤ/2ℤ`, its pointwise constant extension `(Tf)(t)
= T(f(t))` has the same degree for the grading of `C(X,E)`. -/
theorem constantEndomorphismMap_isHomogeneous (δ : CStarModuleGrading γ E)
    (n : ZMod 2) (T : CStarModule.AdjointableOperator.End B E)
    (hT : IsHomogeneousOperator δ δ n T) :
    IsHomogeneousOperator (continuousMap X δ) (continuousMap X δ) n
      (CStarModule.ContinuousMap.constantEndomorphismMap (B := B) X T) := by
  intro f
  apply _root_.ContinuousMap.ext
  intro t
  simpa only [continuousMap_generator_apply,
    CStarModule.ContinuousMap.constantEndomorphismMap_apply, _root_.ContinuousMap.smul_apply]
    using hT (f t)

/-- **Graded constant extension of endomorphisms.** Let `X` be a compact topological space, `B` a graded
nonunital complex C*-algebra, and `E` a complete right Hilbert `B`-module with compatible generator
`G`. Assume star-compatible orders on the opposite algebras of `B` and `C(X,B)`. Constant pointwise
extension gives an equivariant star homomorphism from the graded adjointable endomorphism algebra of
`E` to that of `C(X,E)`. -/
def constantGradedEndomorphismMap (δ : CStarModuleGrading γ E) :
    CStarGrading.Hom δ.operatorGrading (continuousMap X δ).operatorGrading := by
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  refine CStarModule.InternalTensorProduct.IsModel.gradedLeftHom
    (CStarModule.InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X)
    δ (self (PointNormCStarAction.continuousMap X γ)) (continuousMap X δ) ?_
  intro x b
  apply _root_.ContinuousMap.ext
  intro t
  simp only [continuousMap_generator_apply,
    CStarModule.InternalTensorProduct.continuousMapPure_apply, self_generator_apply,
    δ.generator_right_smul, CStarGrading.generatorAut_apply,
    PointNormCStarAction.continuousMap_apply]

end CStarModuleGrading
