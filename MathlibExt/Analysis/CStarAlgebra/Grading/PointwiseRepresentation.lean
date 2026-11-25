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

public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap.PointwiseRepresentation
public import MathlibExt.Analysis.CStarAlgebra.Grading.ContinuousMapOperators
import Mathlib.Tactic.FinCases

/-!
# Graded pointwise coefficient representation on continuous sections

Both coefficient algebras and the original module are extended pointwise.
The actual generator on C(X,E) comes from the original module grading.
Evaluation proves grading covariance for the new left algebra C(X,D).
No graded representation, generator, norm or tensor model is an output
premise. Blackadar18.4.4 uses this map in its first-variable homotopy.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModuleGrading

universe uX uD uB uE

variable (X : Type uX) [TopologicalSpace X] [CompactSpace X]
variable {D : Type uD} [NonUnitalCStarAlgebra D]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
  [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {gammaD : CStarGrading D} {gammaB : CStarGrading B}

attribute [local instance] CStarModule.ContinuousMap.rightAction
  CStarModule.ContinuousMap.cstarModule

/-- **Pointwise graded representation on sections.** Let `X` be a compact topological space, let `D,B`
be graded nonunital complex C*-algebras, and let `E` be a complete compatibly graded right Hilbert
`B`-module. Assume star-compatible opposite orders on `B` and `C(X,B)`, and let `ρ : D → End*(E)` be
a graded star representation into adjointable endomorphisms. The formula `(ρ_X(a)f)(t) =
ρ(a(t))(f(t))` defines a graded star representation of `C(X,D)` on the complete right Hilbert
`C(X,B)`-module `C(X,E)`. -/
def continuousCoefficientGradedRepresentation
    (delta : CStarModuleGrading gammaB E)
    (rho : CStarGrading.Hom gammaD delta.operatorGrading) :
    CStarGrading.Hom (PointNormCStarAction.continuousMap X gammaD)
      (continuousMap X delta).operatorGrading where
  toNonUnitalStarAlgHom :=
    CStarModule.AdjointableOperator.continuousCoefficientRepresentation X rho.toNonUnitalStarAlgHom
  equivariant' := by
    intro n a
    change CStarModule.AdjointableOperator.continuousCoefficientRepresentation X
        rho.toNonUnitalStarAlgHom
        (PointNormCStarAddAction.aut (PointNormCStarAction.continuousMap X gammaD) n.toAdd a) =
      PointNormCStarAddAction.aut (continuousMap X delta).operatorGrading n.toAdd
        (CStarModule.AdjointableOperator.continuousCoefficientRepresentation X
          rho.toNonUnitalStarAlgHom a)
    have hn (k : ZMod 2) : k = 0 ∨ k = 1 := by
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hn n.toAdd with h0 | h1
    · rw [h0]
      simp only [PointNormCStarAddAction.aut_zero, StarAlgEquiv.one_apply]
    · rw [h1]
      change CStarModule.AdjointableOperator.continuousCoefficientRepresentation X
          rho.toNonUnitalStarAlgHom
          (CStarGrading.generatorAut
            (PointNormCStarAction.continuousMap X gammaD) a) =
        (continuousMap X delta).operatorGrading.generatorAut
          (CStarModule.AdjointableOperator.continuousCoefficientRepresentation X
            rho.toNonUnitalStarAlgHom a)
      apply CStarModule.AdjointableOperator.ext
      intro f
      apply _root_.ContinuousMap.ext
      intro t
      have hgamma :
          (CStarGrading.generatorAut (PointNormCStarAction.continuousMap X gammaD) a) t =
            gammaD.generatorAut (a t) := by
        simp only [CStarGrading.generatorAut_apply, PointNormCStarAction.continuousMap_apply]
      have h := CStarGrading.Hom.equivariant rho 1 (a t)
      change rho (gammaD.generatorAut (a t)) = delta.operatorGrading.generatorAut (rho (a t)) at h
      have hx := congrArg (fun T : CStarModule.AdjointableOperator.End B E => T (f t)) h
      have hview (b : D) : rho.toNonUnitalStarAlgHom b = rho b := rfl
      simpa only [CStarModule.AdjointableOperator.continuousCoefficientRepresentation_apply,
        hgamma, hview, operatorGrading_generatorAut, operatorGenerator_apply,
        continuousMap_generator_apply] using hx

/-- **Underlying pointwise section representation.** Let `X` be a compact topological space, let `D,B`
be graded nonunital complex C*-algebras, and let `E` be a complete compatibly graded right Hilbert
`B`-module. Assume star-compatible opposite orders on `B` and `C(X,B)`, and let `ρ : D → End*(E)` be
a graded star representation into adjointable endomorphisms. Forgetting grading equivariance gives
the pointwise nonunital star representation of continuous `D`-valued coefficients on continuous
`E`-valued sections. -/
@[simp]
theorem continuousCoefficientGradedRepresentation_toNonUnitalStarAlgHom
    (delta : CStarModuleGrading gammaB E)
    (rho : CStarGrading.Hom gammaD delta.operatorGrading) :
    (continuousCoefficientGradedRepresentation X delta rho).toNonUnitalStarAlgHom =
      CStarModule.AdjointableOperator.continuousCoefficientRepresentation X
        rho.toNonUnitalStarAlgHom := rfl

/-- **Evaluation of a pointwise graded representation.** Let `X` be a compact topological space, let
`D,B` be graded nonunital complex C*-algebras, and let `E` be a complete compatibly graded right
Hilbert `B`-module. Assume star-compatible opposite orders on `B` and `C(X,B)`, and let `ρ : D →
End*(E)` be a graded star representation into adjointable endomorphisms. For `a ∈ C(X,D)`, `f ∈
C(X,E)`, and `t ∈ X`, the represented section has value `ρ(a(t))(f(t))`. -/
@[simp]
theorem continuousCoefficientGradedRepresentation_apply
    (delta : CStarModuleGrading gammaB E)
    (rho : CStarGrading.Hom gammaD delta.operatorGrading)
    (a : C(X, D)) (f : C(X, E)) (t : X) :
    continuousCoefficientGradedRepresentation X delta rho a f t = rho (a t) (f t) :=
  CStarModule.AdjointableOperator.continuousCoefficientRepresentation_apply X
    rho.toNonUnitalStarAlgHom a f t

/-- **Constant coefficients in the graded section representation.** Let `X` be a compact topological
space, let `D,B` be graded nonunital complex C*-algebras, and let `E` be a complete compatibly
graded right Hilbert `B`-module. Assume star-compatible opposite orders on `B` and `C(X,B)`, and let
`ρ : D → End*(E)` be a graded star representation into adjointable endomorphisms. For `a ∈ D`
regarded as a constant section, the pointwise representation is the constant extension of the
operator `ρ(a)` on `E`. -/
theorem continuousCoefficientGradedRepresentation_const
    (delta : CStarModuleGrading gammaB E)
    (rho : CStarGrading.Hom gammaD delta.operatorGrading) (a : D) :
    continuousCoefficientGradedRepresentation X delta rho (_root_.ContinuousMap.const X a) =
      constantGradedEndomorphismMap X delta (rho a) :=
  CStarModule.AdjointableOperator.continuousCoefficientRepresentation_const X
    rho.toNonUnitalStarAlgHom a

end CStarModuleGrading
