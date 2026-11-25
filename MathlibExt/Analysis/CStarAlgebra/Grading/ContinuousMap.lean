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

public import MathlibExt.Analysis.CStarAlgebra.Grading.Module
public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.ContinuousMap

/-!
# Pointwise gradings of continuous-function modules

The input module grading is lifted on the computed function module. Its
generator and coefficient grading act on values, without changing the
parameter. This is standard-function-module data, not a construction of
general interval tensor fibres or countable generation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModuleGrading

universe uX uB uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {γ : CStarGrading B}

/-- **Pointwise grading of continuous module sections.** Let `X` be a compact topological space, `B` a
graded nonunital complex C*-algebra, and `E` a complete right Hilbert `B`-module with compatible
generator `G`. Assume star-compatible orders on the opposite algebras of `B` and `C(X,B)`. The
complete right Hilbert `C(X,B)`-module `C(X,E)`, with pointwise action and inner product and the
supremum norm, is graded by `f ↦ (t ↦ G(f(t)))`. -/
def continuousMap (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (δ : CStarModuleGrading γ E) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     CStarModuleGrading (PointNormCStarAction.continuousMap X γ) C(X, E)) := by
  letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  let L : C(X, E) →L[ℂ] C(X, E) :=
    δ.generatorCLM.compLeftContinuous ℂ X
  have hL (f : C(X, E)) (t : X) : L f t = δ.generator (f t) := by
    rfl
  have hLeft : Function.LeftInverse L L := by
    intro f
    apply _root_.ContinuousMap.ext
    intro t
    rw [hL, hL]
    exact δ.generator_involutive (f t)
  have hRight : Function.RightInverse L L := by
    intro f
    exact hLeft f
  let U : C(X, E) ≃L[ℂ] C(X, E) :=
    ContinuousLinearEquiv.equivOfInverse L L hLeft hRight
  have hU (f : C(X, E)) (t : X) : U f t = δ.generator (f t) := by
    dsimp only [U]
    exact (congrArg (fun g : C(X, E) => g t)
      (ContinuousLinearEquiv.equivOfInverse_apply L L hLeft hRight f)).trans (hL f t)
  have hγ (b : C(X, B)) (t : X) :
      (CStarGrading.generatorAut (PointNormCStarAction.continuousMap X γ) b) t =
        γ.generatorAut (b t) := by
    simp only [CStarGrading.generatorAut_apply,
      PointNormCStarAction.continuousMap_apply]
  exact
    { generator := U
      generator_involutive := by
        intro f
        apply _root_.ContinuousMap.ext
        intro t
        rw [hU, hU]
        exact δ.generator_involutive (f t)
      generator_right_smul := by
        intro f b
        apply _root_.ContinuousMap.ext
        intro t
        simpa only [hU, CStarModule.ContinuousMap.right_smul_apply, hγ] using
          δ.generator_right_smul (f t) (b t)
      generator_rightInner := by
        intro f g
        apply _root_.ContinuousMap.ext
        intro t
        simpa only [CStarModule.ContinuousMap.rightInner_apply, hU, hγ] using
          δ.generator_rightInner (f t) (g t) }

/-- **Values of the continuous-section grading generator.** Let `X` be a compact topological space, `B`
a graded nonunital complex C*-algebra, and `E` a complete right Hilbert `B`-module with compatible
generator `G`. Assume star-compatible orders on the opposite algebras of `B` and `C(X,B)`. For a
continuous section `f` and `t ∈ X`, the lifted grading generator has value `G(f(t))`. -/
@[simp]
theorem continuousMap_generator_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (δ : CStarModuleGrading γ E) (f : C(X, E)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
       CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
     ((continuousMap X δ).generator f) t = δ.generator (f t)) := by
  dsimp only [continuousMap]
  simp only [ContinuousLinearEquiv.equivOfInverse_apply]
  rfl

end CStarModuleGrading
