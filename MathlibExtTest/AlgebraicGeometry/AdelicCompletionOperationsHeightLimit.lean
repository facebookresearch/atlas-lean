/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AdelicCompletionOperationsHeightLimit

set_option autoImplicit false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AdelicCompletionOperationsHeightLimit

open CategoryTheory _root_.AlgebraicGeometry Filter
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
open WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights
open scoped Topology

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} {B : EffectiveBoundary A X} {m : BoundaryMetricCompletion (L := L) B}
  {x : BasePoint (K := K) ⟶ X} {F : PointFrame A X L x}

/-- The computed quotient height is the unique limit of the native model heights. -/
example (D : DominatedApproximation B m F) (H : ℝ)
    (hH : Tendsto (fun n : ℕ ↦ MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height
      A X L (D.sequence.model n).metric F (F.basis ())) atTop (𝓝 H)) :
    H = MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights.height B m F (F.basis ()) := by
  have h : Tendsto (fun n : ℕ ↦ MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height
      A X L (D.sequence.model n).metric F (F.basis ())) atTop
      (𝓝 (MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights.height B m F
        (F.basis ()))) :=
    heightLimit B m F D
  exact tendsto_nhds_unique hH h

/-- Model heights minus the quotient height converge to zero. -/
example (D : DominatedApproximation B m F) :
    Tendsto (fun n : ℕ ↦ MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height A X L
      (D.sequence.model n).metric F (F.basis ()) -
      MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights.height B m F (F.basis ()))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights.height
      A X L (D.sequence.model n).metric F (F.basis ())) atTop
      (𝓝 (MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights.height B m F
        (F.basis ()))) :=
    heightLimit B m F D
  have hsub := h.sub (tendsto_const_nhds (x :=
    MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights.height B m F (F.basis ())))
  simpa only [sub_self] using hsub

end MathlibExtTest.AlgebraicGeometry.AdelicCompletionOperationsHeightLimit
