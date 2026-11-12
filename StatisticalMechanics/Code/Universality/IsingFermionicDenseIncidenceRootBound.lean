/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge





namespace StatMech.Universality

open Filter Set Topology

noncomputable section

namespace FKIsingCaratheodoryApproximation




theorem StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths_of_root_tendsto
    {tangent : ∀ n,
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.M n → Complex}
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.StableFullMedialInterpolation
      tangent)
    (Hholder :
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
        I.interpolant)
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {mesh bulkRate layerRate : Nat → Real}
    (target Phi : Complex → Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh)
    (P : FKIsingDenseIncidencePrimitivePathCompatibility
      (N := N) (hN := hN) (mesh := mesh) I.interpolant D)
    (Hrobin :
      FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs
        N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hMorera : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ I.interpolant (phi (psi n))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      Complex.IsConservativeOn f
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hroot : Tendsto
      (fun n ↦ I.interpolant n
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
    TendstoLocallyUniformlyOn I.interpolant target atTop
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  let u : Nat → Complex := fun n ↦ I.interpolant n
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.root
  have hu : Tendsto u atTop (nhds (target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
    simpa [u] using hroot
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto u hu).subset_closedBall 0
  have hanchorBound : ∀ n, norm (I.interpolant n
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) ≤ B := by
    intro n
    have hn := hB (show u n ∈ Set.range u from ⟨n, rfl⟩)
    rw [Metric.mem_closedBall] at hn
    simpa [u, dist_eq_norm] using hn
  exact StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths
    I Hholder B hanchorBound target Phi D P Hrobin lipschitzConstant hPhiLip
      htarget htarget_ne hPhi hPhideriv E hMorera hroot

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
