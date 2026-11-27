/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
import MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.CompletedHeightProductFormula

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights

variable {K : Type} [Field K] [CharZero K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (B : EffectiveBoundary A X) (m : BoundaryMetricCompletion (L := L) B)
  {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)

/-- Scalar five is removed by the original product formula on the actual completed class. -/
example (H : CompletedAdelicPointHeights.IsAdmissible B m F)
    (e : AlgebraicFibre X L x) (he : e ≠ 0) :
    CompletedAdelicPointHeights.height B m F ((5 : K) • e) =
      CompletedAdelicPointHeights.height B m F e :=
  CompletedAdelicPointHeights.height_smul B m F H 5 (by norm_num) e he

/-- Constant classes retain the original measured height on the same algebraic fibre. -/
example (N : MetrizedLine A X L)
    (H : CompletedAdelicPointHeights.IsAdmissible B
      (MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations.constantClass B N) F)
    (H' : MeasuredLinePointHeights.IsAdmissible A X L N F) :
    CompletedAdelicPointHeights.pointHeight B
      (MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations.constantClass B N) F H =
        MeasuredLinePointHeights.pointHeight A X L N F H' :=
  CompletedAdelicPointHeights.pointHeight_constant B F N H H'

/-- A standard archimedean place cannot enter the purely geometric nef model definition. -/
example {k : Type} [Field k] (ι : k →+* K)
    (m : RationalAdelicModelMetrics.ModelMetric (A := A) (X := X) (L := L))
    (G : AdelicSemipositiveClosures.GeometricNefModel k ι m) (v : A.places)
    (P : HermitianModelRestrictions.StandardArchimedeanPlace (A := A) v) : False := by
  have h2 : ‖(1 + 1 : A.completion v)‖ = 2 := by
    rw [← P.isometry]
    simp only [map_add, map_one]
    norm_num
  have h := G.nonarchimedean v 1 1
  rw [h2] at h
  norm_num at h

end MathlibExtTest.AlgebraicGeometry.CompletedHeightProductFormula
