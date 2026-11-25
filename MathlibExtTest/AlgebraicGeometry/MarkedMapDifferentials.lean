/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
import MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials

open CategoryTheory AlgebraicGeometry Opposite
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies

noncomputable section

example : reduction ℚ ≫ parameterProjection ℚ = 𝟙 (Spec (.of ℚ)) :=
  reduction_projection ℚ

section PositiveGenus

variable {V S : Scheme.{0}} {q : V ⟶ S} {Ω : Type} [Field Ω]
    {b : Spec (.of Ω) ⟶ S} (F : Family q 2 2 (Spec (.of Ω)) b)

-- Two markings on a genus-two source use the actual target maps after reduction.
example (c : DeformationClasses F) :
    reduction Ω ≫ (classEvaluation F 1 c).map = evaluation F 1 :=
  (classEvaluation F 1 c).reduction_map

-- Family automorphisms preserving the reduction do not change marked evaluation.
example {D E : Deformation F} (h : Isomorphic F D E) :
    evaluationDeformation F D 0 = evaluationDeformation F E 0 :=
  evaluationDeformation_eq_of_isomorphic F h 0

-- The origin is fixed by the actual constant family, rather than a chosen vector.
example (T : TrivialDeformation F) :
    (classEvaluation F 1 (deformationClass F T.deformation)).map =
      parameterProjection Ω ≫ evaluation F 1 := by
  rw [classEvaluation_trivial]
  rfl

end PositiveGenus

-- First-order family classes also exist when there are no evaluation markings.
example {V S : Scheme.{0}} {q : V ⟶ S} {Ω : Type} [Field Ω]
    {b : Spec (.of Ω) ⟶ S} (F : Family q 0 3 (Spec (.of Ω)) b)
    (D : Deformation F) : DeformationClasses F := deformationClass F D

section UniversalDifferential

open MathlibExt.AlgebraicGeometry.MarkedHomEvaluation
open MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
open MathlibExt.AlgebraicGeometry.FourierMukai

variable {k : Type} [Field k]
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (C V : Over (Spec (.of k))) {n : ℕ} (P : Markings C n)
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas)
    (B : DifferentialData C V P M a) (i : Fin n) (U : a.U.left.Opens)

-- The computed evaluation derivative is linear on the actual local tangent sections.
example : ((B.evaluationTangent i).app U) 0 = 0 :=
  (((B.evaluationTangent i).val.app (op U)).hom).map_zero

example (c : Γ(a.U.left, U)) (s : Γ(tangent a.U, U)) :
    ((B.evaluationTangent i).app U) (c • s) =
      c • ((B.evaluationTangent i).app U) s :=
  (((B.evaluationTangent i).val.app (op U)).hom).map_smul c s

end UniversalDifferential
