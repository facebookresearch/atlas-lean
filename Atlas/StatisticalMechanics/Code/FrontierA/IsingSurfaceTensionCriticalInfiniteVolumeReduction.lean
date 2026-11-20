/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionCriticalSymmetricMean
import Code.FrontierA.IsingSurfaceTensionInteriorBlockClosure












open Filter Topology

namespace StatMech.FrontierA

noncomputable section



theorem cubicalInfiniteVolumeSquareWilsonDensity_le_central
    {beta : Real} (hbeta : 0 < beta) (n : Nat) (hn : 0 < n) :
    cubicalInfiniteVolumeSquareWilsonDensity (gaugeCriticalCoupling beta)
        (2 * n) <= centralCubicalIsingDisorderDensity beta n := by
  let L := 2 * n + 1
  let K := gaugeCriticalCoupling beta
  have hK : 0 < K := gaugeCriticalCoupling_pos hbeta
  let eEmb : CubicalEdge L L 0 ↪ CubicalEdge L L L :=
    cubicalEdgeChart 0 0 (n + 1) (by omega) (by omega) (by dsimp [L]; omega)
  let pEmb : CubicalPlaquette L L 0 ↪ CubicalPlaquette L L L :=
    cubicalPlaquetteChart 0 0 (n + 1)
      (by omega) (by omega) (by dsimp [L]; omega)
  have hsheet :
      (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1)).map pEmb =
        cubicalXYSheet (a := L) (b := L) (c := L)
          (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1)) := by
    ext p
    simp only [cubicalXYSheet, Finset.mem_map, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, ⟨ij, rfl⟩, rfl⟩
      refine ⟨ij, ?_⟩
      cases ij with
      | mk i j =>
          change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy _ _ _
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            simp [finOffsetEmbedding]
          constructor
          · apply Fin.ext
            simp [finOffsetEmbedding]
          · apply Fin.ext
            simp [finOffsetEmbedding]
    · rintro ⟨ij, rfl⟩
      refine ⟨CubicalPlaquette.xy ij.1 ij.2 (0 : Fin 1), ⟨ij, rfl⟩, ?_⟩
      cases ij with
      | mk i j =>
          change CubicalPlaquette.xy _ _ _ = CubicalPlaquette.xy _ _ _
          rw [CubicalPlaquette.xy.injEq]
          constructor
          · apply Fin.ext
            simp [finOffsetEmbedding]
          constructor
          · apply Fin.ext
            simp [finOffsetEmbedding]
          · apply Fin.ext
            simp [finOffsetEmbedding]
  have hlocalLoop :
      cubicalXYLoop (a := L) (b := L) (c := L)
          (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1)) =
        (cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)).map eEmb := by
    have hboundary := gaugeSurfaceBoundary_map
      cubicalPlaquetteIncidence cubicalPlaquetteIncidence eEmb pEmb
      (cubicalPlaquetteIncidence_chart 0 0 (n + 1)
        (by omega) (by omega) (by dsimp [L]; omega))
      (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1))
    rw [hsheet] at hboundary
    simpa [cubicalXYLoop] using hboundary
  let N := n + 1
  let outer : CubicalEdge L L L ↪
      CubicalEdge (N + L + N) (N + L + N) (N + N) :=
    cubicalEdgeChart N N 0 (by omega) (by omega) (by dsimp [N, L]; omega)
  let target : CubicalEdge L L 0 ↪
      CubicalEdge (N + L + N) (N + L + N) (N + N) :=
    cubicalEdgeChart N N N (by omega) (by omega) (by omega)
  have hmap :
      (cubicalXYLoop (a := L) (b := L) (c := L)
          (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))).map outer =
        (cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)).map target := by
    rw [hlocalLoop, Finset.map_map]
    congr 1
    ext e
    simpa [outer, target, eEmb, N] using
      (cubicalEdgeChart_comp_apply 0 0 (n + 1) N N 0
        (by omega) (by omega) (by dsimp [L]; omega)
        (by omega) (by omega) (by dsimp [N, L]; omega) e)
  have hchart := cubicalWilsonExpectation_le_chart
    (a := L) (b := L) (c := L)
    (A := N + L + N) (B := N + L + N) (C := N + N)
    N N 0 (by omega) (by omega) (by dsimp [N, L]; omega) hK.le
    (cubicalXYLoop (a := L) (b := L) (c := L)
      (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1)))
  rw [hmap] at hchart
  have hchart' :
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette L L L => K)
          (cubicalXYLoop (a := L) (b := L) (c := L)
            (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))) <=
        cubicalFixedLoopWilsonSequence K L L N := by
    simpa [cubicalFixedLoopWilsonSequence, cubicalPaddedWilsonExpectation,
      target] using hchart
  have hpadded :
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette L L L => K)
          (cubicalXYLoop (a := L) (b := L) (c := L)
            (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))) <=
        cubicalInfiniteVolumeWilsonExpectation K L L :=
    hchart'.trans (le_ciSup
      (⟨1, fun x ⟨m, hm⟩ => hm ▸
        (cubicalFixedLoopWilsonSequence_mem_Icc hK L L m).2⟩) N)
  have hfinitePos : 0 <
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette L L L => K)
          (cubicalXYLoop (a := L) (b := L) (c := L)
            (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))) := by
    apply (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence (fun _ => K) (fun _ => hK) _).2
    exact ⟨cubicalXYSheet
      (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1)),
      cubicalXYSheet_hasWilsonBoundary _⟩
  have hinfinitePos :
      0 < cubicalInfiniteVolumeWilsonExpectation K L L :=
    cubicalInfiniteVolumeWilsonExpectation_pos hK L L
  have hlog := Real.log_le_log hfinitePos hpadded
  have hduality := neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    (a := L) (b := L) (c := L)
    (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [L]; omega)
    (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))
    (fun _ : CubicalPlaquette L L L => K) (fun _ => hK)
  have hdualityBeta :
      -Real.log
          (gaugeWilsonExpectation cubicalPlaquetteIncidence
            (fun _ : CubicalPlaquette L L L => K)
            (cubicalXYLoop (a := L) (b := L) (c := L)
              (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1)))) =
        multibondDisorderFreeEnergy
          (cubicalDualEnds (a := L) (b := L) (c := L))
          (fun _ : CubicalPlaquette L L L => beta)
          (cubicalXYSheet (a := L) (b := L) (c := L)
            (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))) := by
    simpa [K, gaugeDualCoupling_gaugeCriticalCoupling hbeta] using hduality
  have hfree :
      cubicalInfiniteVolumeWilsonFreeEnergy K L L <=
        multibondDisorderFreeEnergy
          (cubicalDualEnds (a := L) (b := L) (c := L))
          (fun _ : CubicalPlaquette L L L => beta)
          (cubicalXYSheet (a := L) (b := L) (c := L)
            (⟨n + 1, by dsimp [L]; omega⟩ : Fin (L + 1))) := by
    unfold cubicalInfiniteVolumeWilsonFreeEnergy
    rw [← hdualityBeta]
    linarith
  unfold cubicalInfiniteVolumeSquareWilsonDensity
    centralCubicalIsingDisorderDensity
  dsimp [L]
  simpa [centralSquareSide] using
    div_le_div_of_nonneg_right hfree
      (sq_nonneg (((2 * n + 1 : Nat) : Real)))



theorem rectangularIsingSurfaceTension_eq_zero_of_central_tendsto_zero
    {beta : Real} (hbeta : 0 < beta)
    (hcentral : Tendsto (centralCubicalIsingDisorderDensity beta)
      atTop (nhds 0)) :
    rectangularIsingSurfaceTension beta = 0 := by
  let K := gaugeCriticalCoupling beta
  have hK : 0 < K := gaugeCriticalCoupling_pos hbeta
  have hinfinite : Tendsto
      (fun n => cubicalInfiniteVolumeSquareWilsonDensity K (2 * n))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n =>
        cubicalInfiniteVolumeSquareWilsonDensity_nonneg hK (2 * n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact cubicalInfiniteVolumeSquareWilsonDensity_le_central
        hbeta n (by omega)
    · exact hcentral
  have hupper : rectangularIsingSurfaceTension beta <= 0 := by
    apply ge_of_tendsto hinfinite
    exact Filter.Eventually.of_forall fun n => by
      have hle := rectangularIsingSurfaceTension_le_infiniteVolumeSquareWilsonDensity
        K hK (2 * n)
      simpa [K, gaugeDualCoupling_gaugeCriticalCoupling hbeta] using hle
  exact le_antisymm hupper (rectangularIsingSurfaceTension_nonneg hbeta)



theorem rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder_infinite
    (hmean : forall n, OddPrismUnequalBridgeSymmetricMeanOrder
      (StatMech.Ising.betaC 3) n) :
    rectangularIsingSurfaceTension (StatMech.Ising.betaC 3) = 0 := by
  apply rectangularIsingSurfaceTension_eq_zero_of_central_tendsto_zero
    isingBetaC_three_pos
  have hstandard :=
    standardCubicInterfaceDensity_critical_tendsto_zero_of_symmetricMeanOrder
      hmean
  apply hstandard.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity
    (StatMech.Ising.betaC 3) n (by omega)

end

end StatMech.FrontierA
