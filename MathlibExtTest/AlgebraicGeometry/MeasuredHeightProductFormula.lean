/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

/-! The source measure's product formula makes a genuine nonzero algebraic
scalar (three) invisible to the measured height on the same scheme fibre.
The check retains the actual point-frame maps and their integrability gate.
-/

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

noncomputable section

variable {K : Type} [Field K] [CharZero K] (A : AdelicField K)
  (X : Over (Spec (.of K))) (L : X.left.Modules)
  (N : MetrizedLine A X L) {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)
  (H : IsAdmissible A X L N F)

example : height A X L N F ((3 : K) • F.basis ()) =
    pointHeight A X L N F H := by
  exact height_smul A X L N F H 3 (by norm_num) _ (F.basis.ne_zero ())

#print axioms MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.completedScalars_norm
#print axioms MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height_smul
#print axioms MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height_independent
