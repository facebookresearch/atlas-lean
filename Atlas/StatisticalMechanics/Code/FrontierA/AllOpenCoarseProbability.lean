/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierA.AllOpenCoarseBoundary
import Code.Walls.bdcdetcount
import Code.Walls.bc62coarseclose

open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation
open StatMech.Walls


theorem measurableSet_bgF2IndexAllOpen (L : ℕ) (j : Site 2) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site 2)) |
        bgf2_IndexAllOpen omega L j} := by
  classical
  rw [show {omega : ConfigSpace (Sym2 (Site 2)) |
      bgf2_IndexAllOpen omega L j} =
      ⋂ x : Site 2, ⋂ y : Site 2,
        {omega | bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice 2).Adj x y → omega s(x, y) = true} by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  by_cases hx : bgn_idx L x = j
  · by_cases hy : bgn_idx L y = j
    · by_cases hadj : (hypercubicLattice 2).Adj x y
      · simpa only [openSubgraph_adj, hx, hy, hadj, true_and,
          true_implies] using (measurableSet_openAdj x y)
      · have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
            bgn_idx L x = j → bgn_idx L y = j →
              (hypercubicLattice 2).Adj x y → omega s(x, y) = true} = Set.univ := by
          ext omega
          simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy, hadj,
            true_implies, false_implies]
        rw [heq]
        exact MeasurableSet.univ
    · have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
          bgn_idx L x = j → bgn_idx L y = j →
            (hypercubicLattice 2).Adj x y → omega s(x, y) = true} = Set.univ := by
        ext omega
        simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy,
          true_implies, false_implies]
      rw [heq]
      exact MeasurableSet.univ
  · have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
        bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice 2).Adj x y → omega s(x, y) = true} = Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, hx,
        false_implies]
    rw [heq]
    exact MeasurableSet.univ



theorem measurableSet_faithfulAllOpenTrifAt (L : ℕ) (j : Site 2) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site 2)) |
        FaithfulAllOpenTrifAt omega L j} := by
  have hcoarse : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site 2)) |
        bc67_IsGnTrifurcation omega L (bgf2_centre L j)} := by
    have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
        bc67_IsGnTrifurcation omega L (bgf2_centre L j)} =
        {omega | bc61_IsCoarseTrifurcation omega L (bgf2_centre L j)} := by
      ext omega
      exact (bc67_coarseTrif_is_G_n_trifurcation
        omega L (bgf2_centre L j)).symm
    rw [heq]
    exact bc62_measurableSet_coarseTrif L (bgf2_centre L j)
  exact hcoarse.inter (measurableSet_bgF2IndexAllOpen L j)



theorem bgf2_indexAllOpen_shift_centre
    (omega : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) :
    let g : Multiplicative (Site 2) :=
      Multiplicative.ofAdd (bgf2_centre L j)
    bgf2_IndexAllOpen (shift g omega) L j ↔
      bgf2_IndexAllOpen omega L 0 := by
  let c := bgf2_centre L j
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd c
  change bgf2_IndexAllOpen (shift g omega) L j ↔
    bgf2_IndexAllOpen omega L 0
  constructor
  · intro H x y hx hy hadj
    have hxc : bgn_idx L (x + c) = j := by
      rw [bdc_bgn_idx_shift L j x, hx, zero_add]
    have hyc : bgn_idx L (y + c) = j := by
      rw [bdc_bgn_idx_shift L j y, hy, zero_add]
    have hadjc : (hypercubicLattice 2).Adj (x + c) (y + c) :=
      (bdc_lat_shift c x y).2 hadj
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
      have hkey := bdc_bgn_idx_shift L j (x - c)
      rw [sub_add_cancel, hx] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hys : bgn_idx L (y - c) = 0 := by
      have hkey := bdc_bgn_idx_shift L j (y - c)
      rw [sub_add_cancel, hy] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hadjs : (hypercubicLattice 2).Adj (x - c) (y - c) := by
      have hkey := bdc_lat_shift c (x - c) (y - c)
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



theorem faithfulAllOpenTrifAt_shift_centre
    (omega : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) :
    let g : Multiplicative (Site 2) :=
      Multiplicative.ofAdd (bgf2_centre L j)
    FaithfulAllOpenTrifAt (shift g omega) L j ↔
      FaithfulAllOpenTrifAt omega L 0 := by
  let g : Multiplicative (Site 2) :=
    Multiplicative.ofAdd (bgf2_centre L j)
  change FaithfulAllOpenTrifAt (shift g omega) L j ↔
    FaithfulAllOpenTrifAt omega L 0
  have hgc : g • (0 : Site 2) = bgf2_centre L j := by
    change bgf2_centre L j + 0 = bgf2_centre L j
    simp
  constructor
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation omega L 0 :=
      (bc62_isCoarseTrif_shift g omega L 0).1
        (by rw [hgc]; exact
          (bc67_coarseTrif_is_G_n_trifurcation
            (shift g omega) L (bgf2_centre L j)).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation omega L 0).1 hcoarse,
      (bgf2_indexAllOpen_shift_centre omega L j).1 hopen⟩
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation
        (shift g omega) L (bgf2_centre L j) := by
      rw [← hgc]
      exact (bc62_isCoarseTrif_shift g omega L 0).2
        ((bc67_coarseTrif_is_G_n_trifurcation omega L 0).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation
      (shift g omega) L (bgf2_centre L j)).1 hcoarse,
      (bgf2_indexAllOpen_shift_centre omega L j).2 hopen⟩



theorem faithfulAllOpenTrifAt_prob_const
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu)
    (L : ℕ) (j : Site 2) :
    mu {omega | FaithfulAllOpenTrifAt omega L j} =
      mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
  let g : Multiplicative (Site 2) :=
    Multiplicative.ofAdd (bgf2_centre L j)
  have hpre : (shift g : ConfigSpace (Sym2 (Site 2)) →
      ConfigSpace (Sym2 (Site 2))) ⁻¹'
      {omega | FaithfulAllOpenTrifAt omega L j} =
      {omega | FaithfulAllOpenTrifAt omega L 0} := by
    ext omega
    exact faithfulAllOpenTrifAt_shift_centre omega L j
  calc
    mu {omega | FaithfulAllOpenTrifAt omega L j} =
        mu ((shift g) ⁻¹' {omega | FaithfulAllOpenTrifAt omega L j}) :=
      (hinv.measure_preimage g
        (measurableSet_faithfulAllOpenTrifAt L j)).symm
    _ = mu {omega | FaithfulAllOpenTrifAt omega L 0} := by rw [hpre]

lemma faithfulAllOpenTrifIndicesInBox_eq_sum_indicator
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) :
    ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) =
      ∑ j ∈ boxFinsetBK 2 N,
        ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator
          (fun _ => (1 : ℝ≥0∞))) omega := by
  classical
  unfold faithfulAllOpenTrifIndicesInBox boxFinsetBK
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : FaithfulAllOpenTrifAt omega L j
  · simp [h]
  · simp [h]

theorem expected_faithfulAllOpenTrifIndicesInBox
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu)
    (L N : ℕ) :
    ∫⁻ omega,
        ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu =
      (boxFinsetBK 2 N).card •
        mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
  classical
  calc
    ∫⁻ omega,
        ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu =
        ∫⁻ omega, ∑ j ∈ boxFinsetBK 2 N,
          ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
      apply lintegral_congr
      intro omega
      exact faithfulAllOpenTrifIndicesInBox_eq_sum_indicator omega L N
    _ = ∑ j ∈ boxFinsetBK 2 N, ∫⁻ omega,
          ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
      rw [lintegral_finsetSum]
      intro j hj
      exact Measurable.indicator measurable_const
        (measurableSet_faithfulAllOpenTrifAt L j)
    _ = ∑ j ∈ boxFinsetBK 2 N,
          mu {omega | FaithfulAllOpenTrifAt omega L j} := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_indicator (measurableSet_faithfulAllOpenTrifAt L j)]
      simp
    _ = ∑ _j ∈ boxFinsetBK 2 N,
          mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
      apply Finset.sum_congr rfl
      intro j hj
      exact faithfulAllOpenTrifAt_prob_const mu hinv L j
    _ = (boxFinsetBK 2 N).card •
        mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
      rw [Finset.sum_const]

noncomputable def faithfulAllOpenBoundaryCard (L N : ℕ) : ℕ :=
  boxSV_boundaryCard 2 ((2 * L + 1) * N + L + 1)

theorem faithfulAllOpenTrifIndicesInBox_count_bound
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) :
    (faithfulAllOpenTrifIndicesInBox omega L N).card ≤
      faithfulAllOpenBoundaryCard L N := by
  exact faithfulAllOpenTrifIndicesInBox_count omega L N

lemma boxSV_boundaryCard_two (r : ℕ) (hr : 1 ≤ r) :
    (boxSV_boundaryCard 2 r : ℝ) = 8 * r := by
  rw [boxSV_boundary_card 2 r hr]
  have hle : (2 * r - 1) ^ 2 ≤ (2 * r + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  rw [Nat.cast_sub hle]
  have hsub : 1 ≤ 2 * r := by omega
  push_cast [Nat.cast_sub hsub]
  ring

lemma boxFinsetBK_card_two (N : ℕ) :
    ((boxFinsetBK 2 N).card : ℝ) = (2 * (N : ℝ) + 1) ^ 2 := by
  unfold boxFinsetBK
  rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
  push_cast
  ring

theorem faithfulAllOpen_boundary_volume_ratio_le
    (L N : ℕ) (hN : 1 ≤ N) :
    (faithfulAllOpenBoundaryCard L N : ℝ) /
        ((boxFinsetBK 2 N).card : ℝ) ≤
      (8 * (3 * L + 2) : ℝ) / N := by
  rw [faithfulAllOpenBoundaryCard,
    boxSV_boundaryCard_two _ (by omega), boxFinsetBK_card_two]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 * N + 1) ^ 2)
    (by exact_mod_cast hN : (0 : ℝ) < N)]
  push_cast
  nlinarith [show (0 : ℝ) ≤ L by positivity,
    show (1 : ℝ) ≤ N by exact_mod_cast hN]

theorem faithfulAllOpen_boundary_volume_tendsto (L : ℕ) :
    Tendsto (fun N => (faithfulAllOpenBoundaryCard L N : ℝ) /
      ((boxFinsetBK 2 N).card : ℝ)) atTop (𝓝 0) := by
  have htop : Tendsto (fun N : ℕ => (8 * (3 * L + 2) : ℝ) / N)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds
      (x := (8 * (3 * L + 2) : ℝ))).div_atTop
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ htop
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact faithfulAllOpen_boundary_volume_ratio_le L N hN



theorem faithfulAllOpenTrifAt_prob_eq_zero
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu)
    (L : ℕ) :
    mu {omega | FaithfulAllOpenTrifAt omega L 0} = 0 := by
  classical
  let p : ℝ≥0∞ := mu {omega | FaithfulAllOpenTrifAt omega L 0}
  have hkey : ∀ N,
      ((boxFinsetBK 2 N).card : ℝ≥0∞) * p ≤
        (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) := by
    intro N
    have hexp := expected_faithfulAllOpenTrifIndicesInBox mu hinv L N
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ omega,
        ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
        (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) := by
      calc
        ∫⁻ omega,
            ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
            ∫⁻ _omega, (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) ∂mu := by
          apply lintegral_mono
          intro omega
          change ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ≤
            (faithfulAllOpenBoundaryCard L N : ℝ≥0∞)
          exact_mod_cast
            faithfulAllOpenTrifIndicesInBox_count_bound omega L N
        _ = (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) := by
          rw [lintegral_const]
          simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := measure_ne_top mu _
  let pr : ℝ := p.toReal
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ N,
      ((boxFinsetBK 2 N).card : ℝ) * pr ≤
        (faithfulAllOpenBoundaryCard L N : ℝ) := by
    intro N
    have h := hkey N
    have h' : (((boxFinsetBK 2 N).card : ℝ≥0∞) * p).toReal ≤
        (faithfulAllOpenBoundaryCard L N : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, pr] using h'
  have hvolr : ∀ N, (0 : ℝ) < ((boxFinsetBK 2 N).card : ℝ) := by
    intro N
    exact_mod_cast bkc_boxFinsetBK_card_pos 2 N
  have hle : ∀ N, pr ≤ (faithfulAllOpenBoundaryCard L N : ℝ) /
      ((boxFinsetBK 2 N).card : ℝ) := by
    intro N
    rw [le_div_iff₀ (hvolr N)]
    linarith [hkeyr N]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto'
    tendsto_const_nhds (faithfulAllOpen_boundary_volume_tendsto L) hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := hpreq
  have hpzero : p = 0 :=
    (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  exact hpzero

end StatMech.FrontierA
