/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionUnconditionalBounds
import Code.FrontierA.Z2GaugeSurfaceTensionIdentification












open Filter Topology

namespace StatMech.FrontierA

noncomputable section



theorem cubicalSquareWilsonExpectation_le_fixedLoopSequence_self
    {K : Real} (hK : 0 < K) (n : Nat) :
    cubicalSquareWilsonExpectation K n <=
      cubicalFixedLoopWilsonSequence K (n + 1) (n + 1) (n + 1) := by
  let L := n + 1
  let A := L + L + L
  let C := L + L
  let eEmb : CubicalEdge L L 0 ↪ CubicalEdge L L L :=
    cubicalEdgeChart 0 0 0 (by omega) (by omega) (by omega)
  let pEmb : CubicalPlaquette L L 0 ↪ CubicalPlaquette L L L :=
    cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)
  have hsheet :
      (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1)).map pEmb =
        cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1)) := by
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
      refine ⟨CubicalPlaquette.xy ij.1 ij.2 (0 : Fin 1), ?_, ?_⟩
      · exact ⟨ij, rfl⟩
      · cases ij with
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
  have hloop :
      (cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)).map eEmb =
        cubicalXYLoop (a := L) (b := L) (c := L) (0 : Fin (L + 1)) := by
    unfold cubicalXYLoop
    rw [← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence eEmb pEmb]
    · rw [hsheet]
    · intro p
      exact cubicalPlaquetteIncidence_chart 0 0 0
        (by omega) (by omega) (by omega) p
  let outer : CubicalEdge L L L ↪ CubicalEdge A A C :=
    cubicalEdgeChart L L L (by omega) (by omega) (by omega)
  let target : CubicalEdge L L 0 ↪ CubicalEdge A A C :=
    cubicalEdgeChart L L L (by omega) (by omega) (by omega)
  have hmap :
      (cubicalXYLoop (a := L) (b := L) (c := L)
          (0 : Fin (L + 1))).map outer =
        (cubicalXYLoop (a := L) (b := L) (c := 0)
          (0 : Fin 1)).map target := by
    rw [← hloop, Finset.map_map]
    congr 1
    ext e
    simpa [outer, target, eEmb, A, C] using
      (cubicalEdgeChart_comp_apply 0 0 0 L L L
        (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) e)
  have h := cubicalWilsonExpectation_le_chart
    (a := L) (b := L) (c := L) (A := A) (B := A) (C := C)
    L L L (by omega) (by omega) (by omega) hK.le
    (cubicalXYLoop (a := L) (b := L) (c := L) (0 : Fin (L + 1)))
  rw [hmap] at h
  simpa [cubicalSquareWilsonExpectation, cubicalFixedLoopWilsonSequence,
    cubicalPaddedWilsonExpectation, L, A, C, target] using h



theorem cubicalSquareWilsonExpectation_le_infiniteVolume
    {K : Real} (hK : 0 < K) (n : Nat) :
    cubicalSquareWilsonExpectation K n <=
      cubicalInfiniteVolumeWilsonExpectation K (n + 1) (n + 1) := by
  exact (cubicalSquareWilsonExpectation_le_fixedLoopSequence_self hK n).trans
    (le_ciSup
      (⟨1, fun x ⟨m, hm⟩ => hm ▸
        (cubicalFixedLoopWilsonSequence_mem_Icc hK (n + 1) (n + 1) m).2⟩)
      (n + 1))



theorem cubicalInfiniteVolumeSquareWilsonDensity_le_finite
    {K : Real} (hK : 0 < K) (n : Nat) :
    cubicalInfiniteVolumeSquareWilsonDensity K n <=
      cubicalSquareWilsonDensity K n := by
  have hfinitePos := cubicalSquareWilsonExpectation_pos hK n
  have hinfinitePos := cubicalInfiniteVolumeWilsonExpectation_pos hK
    (centralSquareSide n) (centralSquareSide n)
  have hW := cubicalSquareWilsonExpectation_le_infiniteVolume hK n
  have hlog := Real.log_le_log hfinitePos hW
  have hfree :
      cubicalInfiniteVolumeWilsonFreeEnergy K
          (centralSquareSide n) (centralSquareSide n) <=
        cubicalSquareWilsonFreeEnergy K n := by
    unfold cubicalInfiniteVolumeWilsonFreeEnergy
    rw [cubicalSquareWilsonFreeEnergy_eq_neg_log]
    simpa [centralSquareSide] using neg_le_neg hlog
  unfold cubicalInfiniteVolumeSquareWilsonDensity
  unfold cubicalSquareWilsonDensity cubicalSquareWilsonFreeEnergy
  simpa [centralSquareSide] using
    div_le_div_of_nonneg_right hfree (sq_nonneg ((n + 1 : Nat) : Real))



def cubicalFiniteInfiniteSquareDensityGap (K : Real) (n : Nat) : Real :=
  cubicalSquareWilsonDensity K n -
    cubicalInfiniteVolumeSquareWilsonDensity K n

theorem cubicalFiniteInfiniteSquareDensityGap_nonneg
    {K : Real} (hK : 0 < K) (n : Nat) :
    0 <= cubicalFiniteInfiniteSquareDensityGap K n := by
  exact sub_nonneg.mpr
    (cubicalInfiniteVolumeSquareWilsonDensity_le_finite hK n)




theorem cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop
      (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) := by
  have hfinite :=
    cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hK
  have hinfinite :=
    cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC
      K hK hlt
  simpa [cubicalFiniteInfiniteSquareDensityGap] using hfinite.sub hinfinite




theorem rectangularIsingSurfaceTension_eq_zero_iff_gap_tendsto_zero
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    rectangularIsingSurfaceTension (gaugeDualCoupling K) = 0 <->
      Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop (nhds 0) := by
  constructor
  · intro htau
    simpa [htau] using
      cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension K hK hlt
  · intro hzero
    exact tendsto_nhds_unique
      (cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension K hK hlt)
      hzero

end

end StatMech.FrontierA
