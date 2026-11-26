/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AdelicCompletionOperationsAdmissible
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AdelicCompletionOperationsAdmissible

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights

variable {K : Type} [Field K] [CharZero K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (B : EffectiveBoundary A X) (m : BoundaryMetricCompletion (L := L) B)
  {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)

/-- A dominated approximation makes every algebraic scalar invisible to the completed height. -/
example (D : DominatedApproximation B m F) (a : K) (ha : a ≠ 0)
    (e : AlgebraicFibre X L x) (he : e ≠ 0) :
    CompletedAdelicPointHeights.height B m F (a • e) =
      CompletedAdelicPointHeights.height B m F e :=
  CompletedAdelicPointHeights.height_smul B m F
    (WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights.admissible B m F D) a ha e he

/-- A dominated approximation makes the completed height independent of the fibre vector. -/
example (D : DominatedApproximation B m F) (e f : AlgebraicFibre X L x) (he : e ≠ 0)
    (hf : f ≠ 0) :
    CompletedAdelicPointHeights.height B m F e =
      CompletedAdelicPointHeights.height B m F f :=
  CompletedAdelicPointHeights.height_independent B m F
    (WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights.admissible B m F D) e f he hf

/-- Scalar two is removed by the product formula on a dominated completed class. -/
example (D : DominatedApproximation B m F) :
    CompletedAdelicPointHeights.height B m F ((2 : K) • F.basis ()) =
      CompletedAdelicPointHeights.pointHeight B m F
        (WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights.admissible B m F D) :=
  CompletedAdelicPointHeights.height_smul B m F
    (WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights.admissible B m F D) 2
    (by norm_num) _ (F.basis.ne_zero ())

end MathlibExtTest.AlgebraicGeometry.AdelicCompletionOperationsAdmissible
