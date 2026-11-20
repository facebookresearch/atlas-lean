/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.AllOpenCoarseBoundaryGeneral
import Code.Percolation.CanonBurtonKeane
import Code.Walls.bc62coarseclose

open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation
open StatMech.Walls

variable {d : ℕ}



theorem measurableSet_bgfdIndexAllOpen (L : ℕ) (j : Site d) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        BgfdIndexAllOpen omega L j} := by
  classical
  rw [show {omega : ConfigSpace (Sym2 (Site d)) |
      BgfdIndexAllOpen omega L j} =
      ⋂ x : Site d, ⋂ y : Site d,
        {omega | bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice d).Adj x y → omega s(x, y) = true} by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  by_cases hx : bgn_idx L x = j
  · by_cases hy : bgn_idx L y = j
    · by_cases hadj : (hypercubicLattice d).Adj x y
      · simpa only [openSubgraph_adj, hx, hy, hadj, true_and,
          true_implies] using (measurableSet_openAdj x y)
      · have heq : {omega : ConfigSpace (Sym2 (Site d)) |
            bgn_idx L x = j → bgn_idx L y = j →
              (hypercubicLattice d).Adj x y → omega s(x, y) = true} =
            Set.univ := by
          ext omega
          simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy, hadj,
            true_implies, false_implies]
        rw [heq]
        exact MeasurableSet.univ
    · have heq : {omega : ConfigSpace (Sym2 (Site d)) |
          bgn_idx L x = j → bgn_idx L y = j →
            (hypercubicLattice d).Adj x y → omega s(x, y) = true} =
          Set.univ := by
        ext omega
        simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy,
          true_implies, false_implies]
      rw [heq]
      exact MeasurableSet.univ
  · have heq : {omega : ConfigSpace (Sym2 (Site d)) |
        bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice d).Adj x y → omega s(x, y) = true} =
        Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, hx, false_implies]
    rw [heq]
    exact MeasurableSet.univ


theorem measurableSet_bgfdFaithfulAllOpenTrifAt (L : ℕ) (j : Site d) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        BgfdFaithfulAllOpenTrifAt omega L j} := by
  have hcoarse : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        bc67_IsGnTrifurcation omega L (bgfdCentre L j)} := by
    have heq : {omega : ConfigSpace (Sym2 (Site d)) |
        bc67_IsGnTrifurcation omega L (bgfdCentre L j)} =
        {omega | bc61_IsCoarseTrifurcation omega L (bgfdCentre L j)} := by
      ext omega
      exact (bc67_coarseTrif_is_G_n_trifurcation
        omega L (bgfdCentre L j)).symm
    rw [heq]
    exact bc62_measurableSet_coarseTrif L (bgfdCentre L j)
  exact hcoarse.inter (measurableSet_bgfdIndexAllOpen L j)



theorem bgfd_indexAllOpen_shift_centre
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j : Site d) :
    let g : Multiplicative (Site d) :=
      Multiplicative.ofAdd (bgfdCentre L j)
    BgfdIndexAllOpen (shift g omega) L j ↔
      BgfdIndexAllOpen omega L 0 := by
  let c := bgfdCentre L j
  let g : Multiplicative (Site d) := Multiplicative.ofAdd c
  change BgfdIndexAllOpen (shift g omega) L j ↔
    BgfdIndexAllOpen omega L 0
  constructor
  · intro H x y hx hy hadj
    have hxc : bgn_idx L (x + c) = j := by
      rw [bgfd_idx_shift L j x, hx, zero_add]
    have hyc : bgn_idx L (y + c) = j := by
      rw [bgfd_idx_shift L j y, hy, zero_add]
    have hadjc : (hypercubicLattice d).Adj (x + c) (y + c) :=
      (bgfd_lat_shift c x y).2 hadj
    have hs := H (x + c) (y + c) hxc hyc hadjc
    have hex : g • x = x + c := by
      change c + x = x + c
      abel
    have hey : g • y = y + c := by
      change c + y = y + c
      abel
    have he := shift_apply_smul g omega x y
    rw [hex, hey] at he
    rwa [he] at hs
  · intro H x y hx hy hadj
    have hxs : bgn_idx L (x - c) = 0 := by
      have hkey := bgfd_idx_shift L j (x - c)
      rw [sub_add_cancel, hx] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hys : bgn_idx L (y - c) = 0 := by
      have hkey := bgfd_idx_shift L j (y - c)
      rw [sub_add_cancel, hy] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hadjs : (hypercubicLattice d).Adj (x - c) (y - c) := by
      have hkey := bgfd_lat_shift c (x - c) (y - c)
      rw [sub_add_cancel, sub_add_cancel] at hkey
      exact hkey.1 hadj
    have hopen := H (x - c) (y - c) hxs hys hadjs
    have hex : g • (x - c) = x := by
      change c + (x - c) = x
      abel
    have hey : g • (y - c) = y := by
      change c + (y - c) = y
      abel
    have he := shift_apply_smul g omega (x - c) (y - c)
    rw [hex, hey] at he
    rwa [he]



theorem bgfdFaithfulAllOpenTrifAt_shift_centre
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j : Site d) :
    let g : Multiplicative (Site d) :=
      Multiplicative.ofAdd (bgfdCentre L j)
    BgfdFaithfulAllOpenTrifAt (shift g omega) L j ↔
      BgfdFaithfulAllOpenTrifAt omega L 0 := by
  let g : Multiplicative (Site d) :=
    Multiplicative.ofAdd (bgfdCentre L j)
  change BgfdFaithfulAllOpenTrifAt (shift g omega) L j ↔
    BgfdFaithfulAllOpenTrifAt omega L 0
  have hgc : g • (0 : Site d) = bgfdCentre L j := by
    change bgfdCentre L j + 0 = bgfdCentre L j
    simp
  constructor
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation omega L 0 :=
      (bc62_isCoarseTrif_shift g omega L 0).1
        (by rw [hgc]; exact
          (bc67_coarseTrif_is_G_n_trifurcation
            (shift g omega) L (bgfdCentre L j)).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation omega L 0).1 hcoarse,
      (bgfd_indexAllOpen_shift_centre omega L j).1 hopen⟩
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation
        (shift g omega) L (bgfdCentre L j) := by
      rw [← hgc]
      exact (bc62_isCoarseTrif_shift g omega L 0).2
        ((bc67_coarseTrif_is_G_n_trifurcation omega L 0).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation
      (shift g omega) L (bgfdCentre L j)).1 hcoarse,
      (bgfd_indexAllOpen_shift_centre omega L j).2 hopen⟩



theorem bgfdFaithfulAllOpenTrifAt_prob_const
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (L : ℕ) (j : Site d) :
    mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} =
      mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
  let g : Multiplicative (Site d) :=
    Multiplicative.ofAdd (bgfdCentre L j)
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) →
      ConfigSpace (Sym2 (Site d))) ⁻¹'
      {omega | BgfdFaithfulAllOpenTrifAt omega L j} =
      {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
    ext omega
    exact bgfdFaithfulAllOpenTrifAt_shift_centre omega L j
  calc
    mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} =
        mu ((shift g) ⁻¹' {omega |
          BgfdFaithfulAllOpenTrifAt omega L j}) :=
      (hinv.measure_preimage g
        (measurableSet_bgfdFaithfulAllOpenTrifAt L j)).symm
    _ = mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by rw [hpre]

lemma bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) :
    ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) =
      ∑ j ∈ boxFinsetBK d N,
        ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator
          (fun _ => (1 : ℝ≥0∞))) omega := by
  classical
  unfold bgfdFaithfulAllOpenTrifIndicesInBox boxFinsetBK
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : BgfdFaithfulAllOpenTrifAt omega L j
  · simp [h]
  · simp [h]

theorem expected_bgfdFaithfulAllOpenTrifIndicesInBox
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (L N : ℕ) :
    ∫⁻ omega,
        ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu =
      (boxFinsetBK d N).card •
        mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
  classical
  calc
    ∫⁻ omega,
        ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu =
        ∫⁻ omega, ∑ j ∈ boxFinsetBK d N,
          ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
      apply lintegral_congr
      intro omega
      exact bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator omega L N
    _ = ∑ j ∈ boxFinsetBK d N, ∫⁻ omega,
          ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
      rw [lintegral_finsetSum]
      intro j hj
      exact Measurable.indicator measurable_const
        (measurableSet_bgfdFaithfulAllOpenTrifAt L j)
    _ = ∑ j ∈ boxFinsetBK d N,
          mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_indicator
        (measurableSet_bgfdFaithfulAllOpenTrifAt L j)]
      simp
    _ = ∑ _j ∈ boxFinsetBK d N,
          mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
      apply Finset.sum_congr rfl
      intro j hj
      exact bgfdFaithfulAllOpenTrifAt_prob_const mu hinv L j
    _ = (boxFinsetBK d N).card •
        mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
      rw [Finset.sum_const]

noncomputable def bgfdFaithfulAllOpenBoundaryCard
    (d L N : ℕ) : ℕ :=
  boxSV_boundaryCard d ((2 * L + 1) * N + L + 1)

theorem bgfdFaithfulAllOpenTrifIndicesInBox_count_bound
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) :
    (bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card ≤
      bgfdFaithfulAllOpenBoundaryCard d L N := by
  exact bgfdFaithfulAllOpenTrifIndicesInBox_count omega L N

lemma bgfd_boxFinsetBK_card_real (d N : ℕ) :
    ((boxFinsetBK d N).card : ℝ) = (2 * (N : ℝ) + 1) ^ d := by
  unfold boxFinsetBK
  rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
  push_cast
  ring



theorem bgfdFaithfulAllOpen_boundary_volume_ratio_le
    (d L N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) /
        ((boxFinsetBK d N).card : ℝ) ≤
      (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N := by
  let R : ℕ := (2 * L + 1) * N + L + 1
  have hR : 1 ≤ R := by simp [R]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hVR : ((boxFinsetBK d R).card : ℝ) =
      (2 * (R : ℝ) + 1) ^ d := bgfd_boxFinsetBK_card_real d R
  have hVN : ((boxFinsetBK d N).card : ℝ) =
      (2 * (N : ℝ) + 1) ^ d := bgfd_boxFinsetBK_card_real d N
  have hVRpos : (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := by
    rw [hVR]
    positivity
  have hVNpos : (0 : ℝ) < ((boxFinsetBK d N).card : ℝ) := by
    rw [hVN]
    positivity
  have hsurface : (boxSV_boundaryCard d R : ℝ) ≤
      (2 * (d : ℝ) / R) * ((boxFinsetBK d R).card : ℝ) := by
    apply (div_le_iff₀ hVRpos).mp
    simpa using bkc_boundary_vol_ratio_le d R hd hR
  have hbase : (2 * (R : ℝ) + 1) ≤
      ((3 * L + 2 : ℕ) : ℝ) * (2 * (N : ℝ) + 1) := by
    dsimp [R]
    push_cast
    nlinarith [show (0 : ℝ) ≤ L by positivity,
      show (1 : ℝ) ≤ N by exact_mod_cast hN]
  have hvolume : ((boxFinsetBK d R).card : ℝ) ≤
      ((3 * L + 2 : ℕ) : ℝ) ^ d *
        ((boxFinsetBK d N).card : ℝ) := by
    rw [hVR, hVN, ← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) hbase) d
  have hNR : (N : ℝ) ≤ R := by
    have hfac : 1 ≤ 2 * L + 1 := by omega
    have hmul : 1 * N ≤ (2 * L + 1) * N :=
      Nat.mul_le_mul_right N hfac
    exact_mod_cast (show N ≤ R by dsimp [R]; omega)
  have hcoef : 2 * (d : ℝ) / R ≤ 2 * (d : ℝ) / N := by
    rw [div_le_div_iff₀ hRpos hNpos]
    nlinarith [show (0 : ℝ) ≤ d by positivity]
  have hfinal : (boxSV_boundaryCard d R : ℝ) ≤
      ((2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N) *
        ((boxFinsetBK d N).card : ℝ) := by
    calc
      (boxSV_boundaryCard d R : ℝ) ≤
          (2 * (d : ℝ) / R) *
            ((boxFinsetBK d R).card : ℝ) := hsurface
      _ ≤ (2 * (d : ℝ) / R) *
            (((3 * L + 2 : ℕ) : ℝ) ^ d *
              ((boxFinsetBK d N).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hvolume (by positivity)
      _ ≤ (2 * (d : ℝ) / N) *
            (((3 * L + 2 : ℕ) : ℝ) ^ d *
              ((boxFinsetBK d N).card : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d / N) *
            ((boxFinsetBK d N).card : ℝ) := by ring
  rw [div_le_iff₀ hVNpos]
  simpa [bgfdFaithfulAllOpenBoundaryCard, R] using hfinal

theorem bgfdFaithfulAllOpen_boundary_volume_tendsto
    (d L : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun N => (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) /
      ((boxFinsetBK d N).card : ℝ)) atTop (nhds 0) := by
  have htop : Tendsto
      (fun N : ℕ =>
        (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds
      (x := 2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d)).div_atTop
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ htop
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact bgfdFaithfulAllOpen_boundary_volume_ratio_le d L N hd hN



theorem bgfdFaithfulAllOpenTrifAt_prob_eq_zero
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (L : ℕ) :
    mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} = 0 := by
  classical
  let p : ℝ≥0∞ := mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0}
  have hkey : ∀ N,
      ((boxFinsetBK d N).card : ℝ≥0∞) * p ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) := by
    intro N
    have hexp := expected_bgfdFaithfulAllOpenTrifIndicesInBox mu hinv L N
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ omega,
        ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) := by
      calc
        ∫⁻ omega,
            ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
            ∫⁻ _omega,
              (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) ∂mu := by
          apply lintegral_mono
          intro omega
          change ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ≤
            (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞)
          exact_mod_cast
            bgfdFaithfulAllOpenTrifIndicesInBox_count_bound omega L N
        _ = (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) := by
          rw [lintegral_const]
          simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := measure_ne_top mu _
  let pr : ℝ := p.toReal
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ N,
      ((boxFinsetBK d N).card : ℝ) * pr ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) := by
    intro N
    have h := hkey N
    have h' : (((boxFinsetBK d N).card : ℝ≥0∞) * p).toReal ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, pr] using h'
  have hvolr : ∀ N, (0 : ℝ) < ((boxFinsetBK d N).card : ℝ) := by
    intro N
    exact_mod_cast bkc_boxFinsetBK_card_pos d N
  have hle : ∀ N, pr ≤
      (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) /
        ((boxFinsetBK d N).card : ℝ) := by
    intro N
    rw [le_div_iff₀ (hvolr N)]
    linarith [hkeyr N]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto'
    tendsto_const_nhds
      (bgfdFaithfulAllOpen_boundary_volume_tendsto d L hd) hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := hpreq
  have hpzero : p = 0 :=
    (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  exact hpzero

end StatMech.FrontierA
