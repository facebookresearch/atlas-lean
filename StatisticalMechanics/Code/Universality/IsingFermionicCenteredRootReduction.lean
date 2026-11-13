/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredTensorTentRegularity













open Filter Set Topology

namespace StatMech.Universality

noncomputable section


theorem isingReflectedCenteredRadialGridCellPoint_center
    (n : Nat) (hn : 0 < n) (mesh : Real) :
    isingReflectedCenteredRadialGridCellPoint mesh n (n - 1) (n - 1)
        (1 / 2) (1 / 2) = 0 := by
  rw [isingReflectedCenteredRadialGridCellPoint_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub (by omega : 1 <= n)]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]



noncomputable def fkIsingExpandingBoundarySquareCenteredRootNode
    (k : Nat) (a b : Fin 2) : Complex :=
  fkIsingSquareBoundaryCenteredRadialPatchFullObservable
      (fkIsingExpandingSquareSide k)
      (fkIsingExpandingSquareSide_pos k)
      ⟨a.1 + (fkIsingExpandingSquareSide k - 1), by
        have ha := a.2
        have hn := fkIsingExpandingSquareSide_pos k
        omega⟩
      ⟨b.1 + (fkIsingExpandingSquareSide k - 1), by
        have hb := b.2
        have hn := fkIsingExpandingSquareSide_pos k
        omega⟩ /
    (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)



theorem fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_zero_eq_center_average
    (k : Nat) :
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0 =
      (fkIsingExpandingBoundarySquareCenteredRootNode k 0 0 +
        fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 +
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 +
        fkIsingExpandingBoundarySquareCenteredRootNode k 1 1) / 4 := by
  let n := fkIsingExpandingSquareSide k
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hi : (n - 1) + 1 < 2 * n := by omega
  have hcenter := isingReflectedCenteredRadialGridCellPoint_center n hn
    (fkIsingExpandingSquareScale k)
  rw [show (0 : Complex) =
      (starRingEnd Complex)
        (isingCenteredRadialGridCellPoint
          (fkIsingExpandingSquareScale k) n (n - 1) (n - 1)
            (1 / 2) (1 / 2)) by
      simpa [isingReflectedCenteredRadialGridCellPoint] using hcenter.symm]
  unfold fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    n (n - 1) (n - 1) hn
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
    (fkIsingExpandingSquareScale_pos k).ne' hi hi (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  subst n
  simp only [fkIsingExpandingBoundarySquareCenteredRootNode]
  unfold complexBilinearCell
  push_cast
  simp
  ring



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes
    (target : Complex -> Complex)
    (hnode : forall a b : Fin 2,
      Tendsto
        (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k a b)
        atTop (nhds (target 0))) :
    Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
  change Tendsto
    (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0)
    atTop (nhds (target 0))
  have hsum := (((hnode 0 0).add (hnode 1 0)).add (hnode 0 1)).add
    (hnode 1 1)
  have havg := hsum.const_mul (1 / 4 : Complex)
  convert havg using 1
  · funext k
    rw [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_zero_eq_center_average]
    simp
    ring
  · simp
    ring





theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredNeighbor
    (target : Complex -> Complex)
    (hneighbor : FKIsingExpandingCenteredNeighborTransport)
    (hbase : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0))) :
    Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
  obtain ⟨L, N, hN⟩ := hneighbor
  have hscale : Tendsto
      (fun k => fkIsingExpandingSquareScale k * (L : Real))
      atTop (nhds 0) := by
    simpa [mul_comm] using
      fkIsingExpandingSquareScale_tendsto_zero.const_mul (L : Real)
  have tendstoDiff (f : Nat -> Complex)
      (hf : ∀ᶠ k in atTop,
        norm (f k) <= fkIsingExpandingSquareScale k * (L : Real)) :
      Tendsto f atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    have hepsilonScale := (Metric.tendsto_nhds.1 hscale) epsilon hepsilon
    filter_upwards [hf, hepsilonScale] with k hk hkScale
    rw [dist_zero_right]
    refine lt_of_le_of_lt hk ?_
    have hnonneg :
        0 <= fkIsingExpandingSquareScale k * (L : Real) :=
      mul_nonneg (fkIsingExpandingSquareScale_pos k).le (NNReal.coe_nonneg L)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg,
      abs_of_pos (fkIsingExpandingSquareScale_pos k)] using hkScale
  have h10Bound : ∀ᶠ k in atTop,
      norm
        (fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 -
          fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) <=
        fkIsingExpandingSquareScale k * (L : Real) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hn := fkIsingExpandingSquareSide_pos k
    have h := (hN k hk).1
      (fkIsingExpandingSquareSide k - 1)
      (fkIsingExpandingSquareSide k - 1) (by omega) (by omega)
    simpa [fkIsingExpandingBoundarySquareCenteredRootNode,
      Nat.add_comm] using h
  have h01Bound : ∀ᶠ k in atTop,
      norm
        (fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 -
          fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) <=
        fkIsingExpandingSquareScale k * (L : Real) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hn := fkIsingExpandingSquareSide_pos k
    have h := (hN k hk).2
      (fkIsingExpandingSquareSide k - 1)
      (fkIsingExpandingSquareSide k - 1) (by omega) (by omega)
    simpa [fkIsingExpandingBoundarySquareCenteredRootNode,
      Nat.add_comm] using h
  have h11Bound : ∀ᶠ k in atTop,
      norm
        (fkIsingExpandingBoundarySquareCenteredRootNode k 1 1 -
          fkIsingExpandingBoundarySquareCenteredRootNode k 1 0) <=
        fkIsingExpandingSquareScale k * (L : Real) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have hn := fkIsingExpandingSquareSide_pos k
    have h := (hN k hk).2
      (fkIsingExpandingSquareSide k - 1 + 1)
      (fkIsingExpandingSquareSide k - 1) (by omega) (by omega)
    simpa [fkIsingExpandingBoundarySquareCenteredRootNode,
      Nat.add_comm] using h
  have h10Diff := tendstoDiff _ h10Bound
  have h01Diff := tendstoDiff _ h01Bound
  have h11Diff := tendstoDiff _ h11Bound
  have h10 : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 1 0)
      atTop (nhds (target 0)) := by
    convert h10Diff.add hbase using 1 <;> simp
  have h01 : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 1)
      atTop (nhds (target 0)) := by
    convert h01Diff.add hbase using 1 <;> simp
  have h11 : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 1 1)
      atTop (nhds (target 0)) := by
    convert h11Diff.add h10 using 1 <;> simp
  apply
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes
      target
  intro a b
  fin_cases a <;> fin_cases b
  · exact hbase
  · exact h01
  · exact h10
  · exact h11




theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredStrictNeighbor
    (target : Complex -> Complex)
    (hneighbor : FKIsingExpandingCenteredStrictNeighborTransport)
    (hbase : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0))) :
    Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
  obtain ⟨L, N, hN⟩ := hneighbor
  have hscale : Tendsto
      (fun k => fkIsingExpandingSquareScale k * (L : Real))
      atTop (nhds 0) := by
    simpa [mul_comm] using
      fkIsingExpandingSquareScale_tendsto_zero.const_mul (L : Real)
  have tendstoDiff (f : Nat -> Complex)
      (hf : ∀ᶠ k in atTop,
        norm (f k) <= fkIsingExpandingSquareScale k * (L : Real)) :
      Tendsto f atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    have hepsilonScale := (Metric.tendsto_nhds.1 hscale) epsilon hepsilon
    filter_upwards [hf, hepsilonScale] with k hk hkScale
    rw [dist_zero_right]
    refine lt_of_le_of_lt hk ?_
    have hnonneg :
        0 <= fkIsingExpandingSquareScale k * (L : Real) :=
      mul_nonneg (fkIsingExpandingSquareScale_pos k).le (NNReal.coe_nonneg L)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg,
      abs_of_pos (fkIsingExpandingSquareScale_pos k)] using hkScale
  have h10Bound : ∀ᶠ k in atTop,
      norm
        (fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 -
          fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) <=
        fkIsingExpandingSquareScale k * (L : Real) := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with k hk hk1
    have hn := fkIsingExpandingSquareSide_pos k
    have hn4 : 4 <= fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide, pow_two]
      nlinarith
    have h := (hN k hk).1
      (fkIsingExpandingSquareSide k - 1)
      (fkIsingExpandingSquareSide k - 1)
      (by omega) (by omega) (by omega) (by omega)
    simpa [fkIsingExpandingBoundarySquareCenteredRootNode,
      Nat.add_comm] using h
  have h01Bound : ∀ᶠ k in atTop,
      norm
        (fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 -
          fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) <=
        fkIsingExpandingSquareScale k * (L : Real) := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with k hk hk1
    have hn := fkIsingExpandingSquareSide_pos k
    have hn4 : 4 <= fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide, pow_two]
      nlinarith
    have h := (hN k hk).2
      (fkIsingExpandingSquareSide k - 1)
      (fkIsingExpandingSquareSide k - 1)
      (by omega) (by omega) (by omega) (by omega)
    simpa [fkIsingExpandingBoundarySquareCenteredRootNode,
      Nat.add_comm] using h
  have h11Bound : ∀ᶠ k in atTop,
      norm
        (fkIsingExpandingBoundarySquareCenteredRootNode k 1 1 -
          fkIsingExpandingBoundarySquareCenteredRootNode k 1 0) <=
        fkIsingExpandingSquareScale k * (L : Real) := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with k hk hk1
    have hn := fkIsingExpandingSquareSide_pos k
    have hn4 : 4 <= fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide, pow_two]
      nlinarith
    have h := (hN k hk).2
      (fkIsingExpandingSquareSide k - 1 + 1)
      (fkIsingExpandingSquareSide k - 1)
      (by omega) (by omega) (by omega) (by omega)
    simpa [fkIsingExpandingBoundarySquareCenteredRootNode,
      Nat.add_comm] using h
  have h10Diff := tendstoDiff _ h10Bound
  have h01Diff := tendstoDiff _ h01Bound
  have h11Diff := tendstoDiff _ h11Bound
  have h10 : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 1 0)
      atTop (nhds (target 0)) := by
    convert h10Diff.add hbase using 1 <;> simp
  have h01 : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 1)
      atTop (nhds (target 0)) := by
    convert h01Diff.add hbase using 1 <;> simp
  have h11 : Tendsto
      (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 1 1)
      atTop (nhds (target 0)) := by
    convert h11Diff.add h10 using 1 <;> simp
  apply
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes
      target
  intro a b
  fin_cases a <;> fin_cases b
  · exact hbase
  · exact h01
  · exact h10
  · exact h11

end

end StatMech.Universality
