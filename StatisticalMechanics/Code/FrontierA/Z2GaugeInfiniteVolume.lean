/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeCubicalGluing










open Filter Set Topology
open scoped BigOperators symmDiff

namespace StatMech.FrontierA

noncomputable section



theorem cubicalWilsonExpectation_le_chart
    {a b c A B C : Nat} (ox oy oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C)
    {beta : Real} (hbeta : 0 ≤ beta) (L : Finset (CubicalEdge a b c)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette a b c => beta) L ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette A B C => beta)
        (L.map (cubicalEdgeChart ox oy oz hx hy hz)) := by
  let eEmb := cubicalEdgeChart ox oy oz hx hy hz
  let pEmb := cubicalPlaquetteChart ox oy oz hx hy hz
  let Ksmall := fun _ : CubicalPlaquette a b c => beta
  have hzero : ∀ p, 0 ≤ extendGaugeCoupling pEmb Ksmall p := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact hbeta
    | inr q => exact le_rfl
  have hle : ∀ p, extendGaugeCoupling pEmb Ksmall p ≤ beta := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact le_rfl
    | inr q => exact hbeta
  calc
    gaugeWilsonExpectation cubicalPlaquetteIncidence Ksmall L =
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (extendGaugeCoupling pEmb Ksmall) (L.map eEmb) :=
      (gaugeWilsonExpectation_extendGaugeCoupling
        cubicalPlaquetteIncidence cubicalPlaquetteIncidence eEmb pEmb
        (cubicalPlaquetteIncidence_chart ox oy oz hx hy hz) Ksmall L).symm
    _ ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette A B C => beta) (L.map eEmb) :=
      gaugeWilsonExpectation_mono_coupling cubicalPlaquetteIncidence
        (extendGaugeCoupling pEmb Ksmall) (fun _ => beta) hzero hle _


theorem cubicalEdgeChart_comp_apply
    {a b c A B C X Y Z : Nat}
    (ox oy oz Ox Oy Oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C)
    (hX : Ox + A ≤ X) (hY : Oy + B ≤ Y) (hZ : Oz + C ≤ Z)
    (e : CubicalEdge a b c) :
    cubicalEdgeChart Ox Oy Oz hX hY hZ
        (cubicalEdgeChart ox oy oz hx hy hz e) =
      cubicalEdgeChart (Ox + ox) (Oy + oy) (Oz + oz)
        (by omega) (by omega) (by omega) e := by
  cases e with
  | x i j k =>
      change CubicalEdge.x _ _ _ = CubicalEdge.x _ _ _
      rw [CubicalEdge.x.injEq]
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
  | y i j k =>
      change CubicalEdge.y _ _ _ = CubicalEdge.y _ _ _
      rw [CubicalEdge.y.injEq]
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
  | z i j k =>
      change CubicalEdge.z _ _ _ = CubicalEdge.z _ _ _
      rw [CubicalEdge.z.injEq]
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega



def cubicalPaddedWilsonExpectation (beta : Real) (a b : Nat)
    (lx rx ly ry lz rz : Nat) : Real :=
  gaugeWilsonExpectation
    (cubicalPlaquetteIncidence
      (a := lx + a + rx) (b := ly + b + ry) (c := lz + rz))
    (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) => beta)
    ((cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)).map
      (cubicalEdgeChart lx ly lz
        (by omega) (by omega) (by omega)))



theorem cubicalPaddedWilsonExpectation_mono
    {beta : Real} (hbeta : 0 ≤ beta) (a b : Nat)
    {lx rx ly ry lz rz LX RX LY RY LZ RZ : Nat}
    (hlx : lx ≤ LX) (hrx : rx ≤ RX)
    (hly : ly ≤ LY) (hry : ry ≤ RY)
    (hlz : lz ≤ LZ) (hrz : rz ≤ RZ) :
    cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤
      cubicalPaddedWilsonExpectation beta a b LX RX LY RY LZ RZ := by
  let oldX := lx + a + rx
  let oldY := ly + b + ry
  let oldZ := lz + rz
  let newX := LX + a + RX
  let newY := LY + b + RY
  let newZ := LZ + RZ
  let outer := cubicalEdgeChart (LX - lx) (LY - ly) (LZ - lz)
    (a := oldX) (b := oldY) (c := oldZ)
    (A := newX) (B := newY) (C := newZ)
    (by dsimp [oldX, newX]; omega)
    (by dsimp [oldY, newY]; omega)
    (by dsimp [oldZ, newZ]; omega)
  let inner := cubicalEdgeChart lx ly lz
    (a := a) (b := b) (c := 0)
    (A := oldX) (B := oldY) (C := oldZ)
    (by dsimp [oldX]; omega) (by dsimp [oldY]; omega)
    (by dsimp [oldZ]; omega)
  let target := cubicalEdgeChart LX LY LZ
    (a := a) (b := b) (c := 0)
    (A := newX) (B := newY) (C := newZ)
    (by dsimp [newX]; omega) (by dsimp [newY]; omega)
    (by dsimp [newZ]; omega)
  let L := cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)
  have hmap : (L.map inner).map outer = L.map target := by
    rw [Finset.map_map]
    congr 1
    ext e
    change outer (inner e) = target e
    simpa [outer, inner, target, oldX, oldY, oldZ, newX, newY, newZ,
      Nat.sub_add_cancel hlx, Nat.sub_add_cancel hly,
      Nat.sub_add_cancel hlz, add_assoc] using
      (cubicalEdgeChart_comp_apply lx ly lz (LX - lx) (LY - ly) (LZ - lz)
        (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) e)
  have h := cubicalWilsonExpectation_le_chart
    (a := oldX) (b := oldY) (c := oldZ)
    (A := newX) (B := newY) (C := newZ)
    (LX - lx) (LY - ly) (LZ - lz)
    (by dsimp [oldX, newX]; omega)
    (by dsimp [oldY, newY]; omega)
    (by dsimp [oldZ, newZ]; omega) hbeta (L.map inner)
  rw [hmap] at h
  simpa [cubicalPaddedWilsonExpectation, oldX, oldY, oldZ,
    newX, newY, newZ, inner, target, L] using h


def cubicalFixedLoopWilsonSequence (beta : Real) (a b n : Nat) : Real :=
  cubicalPaddedWilsonExpectation beta a b n n n n n n

theorem cubicalFixedLoopWilsonSequence_mono
    {beta : Real} (hbeta : 0 ≤ beta) (a b : Nat) :
    Monotone (cubicalFixedLoopWilsonSequence beta a b) := by
  apply monotone_nat_of_le_succ
  intro n
  exact cubicalPaddedWilsonExpectation_mono hbeta a b
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem cubicalFixedLoopWilsonSequence_mem_Icc
    {beta : Real} (hbeta : 0 < beta) (a b n : Nat) :
    cubicalFixedLoopWilsonSequence beta a b n ∈ Set.Icc 0 1 := by
  unfold cubicalFixedLoopWilsonSequence cubicalPaddedWilsonExpectation
  exact gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
    (fun _ => beta) (fun _ => hbeta) _


def cubicalInfiniteVolumeWilsonExpectation
    (beta : Real) (a b : Nat) : Real :=
  ⨆ n : Nat, cubicalFixedLoopWilsonSequence beta a b n

theorem cubicalFixedLoopWilsonSequence_tendsto
    {beta : Real} (hbeta : 0 < beta) (a b : Nat) :
    Tendsto (cubicalFixedLoopWilsonSequence beta a b) atTop
      (nhds (cubicalInfiniteVolumeWilsonExpectation beta a b)) := by
  apply tendsto_atTop_ciSup (cubicalFixedLoopWilsonSequence_mono hbeta.le a b)
  exact ⟨1, fun x ⟨n, hn⟩ => hn ▸
    (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2⟩

theorem cubicalInfiniteVolumeWilsonExpectation_mem_Icc
    {beta : Real} (hbeta : 0 < beta) (a b : Nat) :
    cubicalInfiniteVolumeWilsonExpectation beta a b ∈ Set.Icc 0 1 := by
  have hlim := cubicalFixedLoopWilsonSequence_tendsto hbeta a b
  constructor
  · exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).1)
  · exact le_of_tendsto hlim (Eventually.of_forall fun n =>
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2)



theorem cubicalPaddedWilsonExpectation_le_infiniteVolume
    {beta : Real} (hbeta : 0 < beta) (a b lx rx ly ry lz rz : Nat) :
    cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤
      cubicalInfiniteVolumeWilsonExpectation beta a b := by
  let N := max lx (max rx (max ly (max ry (max lz rz))))
  have hpad : cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤
      cubicalFixedLoopWilsonSequence beta a b N := by
    apply cubicalPaddedWilsonExpectation_mono hbeta.le
    all_goals dsimp [N] <;> omega
  exact hpad.trans (le_ciSup
    (⟨1, fun x ⟨n, hn⟩ => hn ▸
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2⟩)
    N)




theorem cubicalPaddedWilsonExpectation_tendsto_infiniteVolume
    {beta : Real} (hbeta : 0 < beta) (a b : Nat)
    (lx rx ly ry lz rz : Nat → Nat)
    (hlx : Tendsto lx atTop atTop) (hrx : Tendsto rx atTop atTop)
    (hly : Tendsto ly atTop atTop) (hry : Tendsto ry atTop atTop)
    (hlz : Tendsto lz atTop atTop) (hrz : Tendsto rz atTop atTop) :
    Tendsto (fun n => cubicalPaddedWilsonExpectation beta a b
      (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)) atTop
      (nhds (cubicalInfiniteVolumeWilsonExpectation beta a b)) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    have hcanon : ∀ᶠ n : Nat in atTop,
        x < cubicalFixedLoopWilsonSequence beta a b n :=
      (cubicalFixedLoopWilsonSequence_tendsto hbeta a b).eventually
        (Ioi_mem_nhds hx)
    obtain ⟨N, hN⟩ := (eventually_atTop.1 hcanon)
    filter_upwards [hlx.eventually (eventually_ge_atTop N),
      hrx.eventually (eventually_ge_atTop N),
      hly.eventually (eventually_ge_atTop N),
      hry.eventually (eventually_ge_atTop N),
      hlz.eventually (eventually_ge_atTop N),
      hrz.eventually (eventually_ge_atTop N)] with n h1 h2 h3 h4 h5 h6
    exact (hN N le_rfl).trans_le
      (cubicalPaddedWilsonExpectation_mono hbeta.le a b
        h1 h2 h3 h4 h5 h6)
  · intro y hy
    exact Eventually.of_forall fun n =>
      (cubicalPaddedWilsonExpectation_le_infiniteVolume hbeta a b
        (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)).trans_lt hy





theorem cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
    {A B C : Nat} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (K : CubicalPlaquette A B C → Real) (hK : ∀ p, 0 < K p)
    (D : Finset (CubicalPlaquette A B C)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence D) =
      multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling (fun p => gaugeDualCoupling (K p)) D) /
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) := by
  calc
    gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence D) =
      (∑ s : AnchoredConfig (CubicalDualVertex A B C) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1 ∆ D,
            Real.exp (-2 * gaugeDualCoupling (K p))) /
        (∑ s : AnchoredConfig (CubicalDualVertex A B C) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1,
            Real.exp (-2 * gaugeDualCoupling (K p))) := by
      apply gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet
        cubicalPlaquetteIncidence K hK _ D
        (hasWilsonBoundary_gaugeSurfaceBoundary _ _) none cubicalDualEnds
        (cubicalClosedSurfaceAnchoredEquiv hB hC)
      exact multibondCut_cubicalClosedSurfaceAnchoredEquiv hA hB hC
    _ = multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling (fun p => gaugeDualCoupling (K p)) D) /
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) :=
      (multibondIsing_twist_partition_ratio_eq_disorderRatio
        none cubicalDualEnds (fun p => gaugeDualCoupling (K p)) D).symm



theorem neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface
    {A B C : Nat} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (K : CubicalPlaquette A B C → Real) (hK : ∀ p, 0 < K p)
    (D : Finset (CubicalPlaquette A B C)) :
    -Real.log (gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence D)) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) D := by
  rw [cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
    hA hB hC K hK D]
  unfold multibondDisorderFreeEnergy
  rw [Real.log_div
    (multibondIsingPartition_pos _ _).ne'
    (multibondIsingPartition_pos _ _).ne']
  ring


def cubicalPaddedXYSheet (a b lx rx ly ry lz rz : Nat) :
    Finset (CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz)) :=
  (cubicalXYSheet (a := a) (b := b) (c := 0) (0 : Fin 1)).map
    (cubicalPlaquetteChart lx ly lz (by omega) (by omega) (by omega))

theorem gaugeSurfaceBoundary_cubicalPaddedXYSheet
    (a b lx rx ly ry lz rz : Nat) :
    gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalPaddedXYSheet a b lx rx ly ry lz rz) =
      (cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)).map
        (cubicalEdgeChart lx ly lz (by omega) (by omega) (by omega)) := by
  exact gaugeSurfaceBoundary_map
    cubicalPlaquetteIncidence cubicalPlaquetteIncidence
    (cubicalEdgeChart lx ly lz (by omega) (by omega) (by omega))
    (cubicalPlaquetteChart lx ly lz (by omega) (by omega) (by omega))
    (cubicalPlaquetteIncidence_chart lx ly lz (by omega) (by omega) (by omega))
    (cubicalXYSheet (0 : Fin 1))

theorem cubicalPaddedWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (a b lx rx ly ry lz rz : Nat) :
    0 < cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz := by
  unfold cubicalPaddedWilsonExpectation
  apply (gaugeWilsonExpectation_pos_iff_exists_boundary
    cubicalPlaquetteIncidence (fun _ => beta) (fun _ => hbeta) _).mpr
  let D := cubicalPaddedXYSheet a b lx rx ly ry lz rz
  refine ⟨D, ?_⟩
  rw [← gaugeSurfaceBoundary_cubicalPaddedXYSheet]
  exact hasWilsonBoundary_gaugeSurfaceBoundary _ D

theorem cubicalInfiniteVolumeWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (a b : Nat) :
    0 < cubicalInfiniteVolumeWilsonExpectation beta a b := by
  have hfinite : 0 < cubicalFixedLoopWilsonSequence beta a b 0 := by
    exact cubicalPaddedWilsonExpectation_pos hbeta a b 0 0 0 0 0 0
  have hbdd : BddAbove
      (Set.range (cubicalFixedLoopWilsonSequence beta a b)) :=
    ⟨1, fun x ⟨n, hn⟩ => hn ▸
      (cubicalFixedLoopWilsonSequence_mem_Icc hbeta a b n).2⟩
  exact hfinite.trans_le (le_ciSup hbdd 0)


def cubicalInfiniteVolumeWilsonFreeEnergy
    (beta : Real) (a b : Nat) : Real :=
  -Real.log (cubicalInfiniteVolumeWilsonExpectation beta a b)



theorem neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
    {beta : Real} (hbeta : 0 < beta) {a b lx rx ly ry lz rz : Nat}
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < lz + rz) :
    -Real.log (cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) =>
          gaugeDualCoupling beta)
        (cubicalPaddedXYSheet a b lx rx ly ry lz rz) := by
  rw [cubicalPaddedWilsonExpectation,
    ← gaugeSurfaceBoundary_cubicalPaddedXYSheet]
  exact neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface
    (by omega) (by omega) hz (fun _ => beta) (fun _ => hbeta)
      (cubicalPaddedXYSheet a b lx rx ly ry lz rz)


def cubicalPaddedDisorderFreeEnergy (beta : Real) (a b : Nat)
    (lx rx ly ry lz rz : Nat) : Real :=
  multibondDisorderFreeEnergy cubicalDualEnds
    (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) =>
      gaugeDualCoupling beta)
    (cubicalPaddedXYSheet a b lx rx ly ry lz rz)




theorem cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume
    {beta : Real} (hbeta : 0 < beta) {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (lx rx ly ry lz rz : Nat → Nat)
    (hlx : Tendsto lx atTop atTop) (hrx : Tendsto rx atTop atTop)
    (hly : Tendsto ly atTop atTop) (hry : Tendsto ry atTop atTop)
    (hlz : Tendsto lz atTop atTop) (hrz : Tendsto rz atTop atTop) :
    Tendsto (fun n => cubicalPaddedDisorderFreeEnergy beta a b
      (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)) atTop
      (nhds (cubicalInfiniteVolumeWilsonFreeEnergy beta a b)) := by
  have hw := cubicalPaddedWilsonExpectation_tendsto_infiniteVolume
    hbeta a b lx rx ly ry lz rz hlx hrx hly hry hlz hrz
  have hpos := cubicalInfiniteVolumeWilsonExpectation_pos hbeta a b
  have hlog := (Real.continuousAt_log hpos.ne').tendsto.comp hw
  have hneg : Tendsto (fun n =>
      -Real.log (cubicalPaddedWilsonExpectation beta a b
        (lx n) (rx n) (ly n) (ry n) (lz n) (rz n))) atTop
      (nhds (cubicalInfiniteVolumeWilsonFreeEnergy beta a b)) := by
    simpa [cubicalInfiniteVolumeWilsonFreeEnergy] using hlog.neg
  apply hneg.congr'
  filter_upwards [hlz.eventually (eventually_ge_atTop 1)] with n hn
  simpa [cubicalPaddedDisorderFreeEnergy] using
    (neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
    (a := a) (b := b) (lx := lx n) (rx := rx n)
    (ly := ly n) (ry := ry n) (lz := lz n) (rz := rz n)
    hbeta ha hb (by omega))

end

end StatMech.FrontierA
