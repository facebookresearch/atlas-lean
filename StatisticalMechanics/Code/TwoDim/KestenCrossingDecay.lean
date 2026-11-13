/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Percolation.SharpnessUnconditional
import Code.TwoDim.SharpThreshold
import Code.RSW.Defs
import Code.Lattice.BoxSurfaceVolume

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality



def kcd_localOneArm (x : Site 2) (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  (ConfigSpace.shift (Multiplicative.ofAdd (-x))) ⁻¹' crossingEvent 2 n



theorem kcd_localOneArm_prob (p : ℝ≥0) (hp : p ≤ 1) (x : Site 2) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (kcd_localOneArm x n)
      = crossProb 2 p hp n := by
  unfold kcd_localOneArm crossProb
  exact ((bernoulli_translationInvariant (E := Sym2 (Site 2))
    (G := Multiplicative (Site 2)) p hp) (Multiplicative.ofAdd (-x))).measureReal_preimage
      (measurableSet_crossingEvent n).nullMeasurableSet



theorem kcd_horizontal_subset_localOneArm (n : ℕ) (hn : 0 < n) :
    StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ)
      ⊆ ⋃ x ∈ boxSV_boxF 2 n, kcd_localOneArm x n := by
  intro ω hω
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    (StatMech.RSW.Box.HorizontalCrossing.connected hω)
  have hxbox : x ∈ box 2 n := by
    intro i
    fin_cases i
    · change (x 0).natAbs ≤ n
      rw [hx.2]
      simp
    · change (x 1).natAbs ≤ n
      rw [← Int.ofNat_le, Int.natAbs_of_nonneg hx.1.2.2.1]
      exact hx.1.2.2.2
  have hxfin : x ∈ boxSV_boxF 2 n := by
    rw [boxSV_mem_boxF]
    intro i
    rw [Finset.mem_Icc]
    fin_cases i
    · simpa [hx.2]
    · change -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ)
      exact ⟨by linarith [hx.1.2.2.1], hx.1.2.2.2⟩
  refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxfin, ?_⟩⟩
  change ConfigSpace.shift (Multiplicative.ofAdd (-x)) ω ∈ crossingEvent 2 n
  rw [mem_crossingEvent]
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-x)
  have hgx : g • x = origin 2 := by
    funext i
    simp [g, smul_site_apply, origin]
  refine ⟨g • y, ?_, ?_⟩
  · rw [← hgx]
    exact (connected_shift g ω x y).2 hxy
  · intro hybox
    have hb := hybox (0 : Fin 2)
    have hcoord : (g • y) (0 : Fin 2) = (n : ℤ) := by
      change -x 0 + y 0 = (n : ℤ)
      rw [hx.2, hy.2]
      simp
    rw [hcoord] at hb
    simp at hb
    omega


theorem kcd_horizontal_prob_le_box_mul_crossProb (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ))
      ≤ ((boxSV_boxF 2 n).card : ℝ) * crossProb 2 p hp n := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  calc
    μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ))
        ≤ μ.real (⋃ x ∈ boxSV_boxF 2 n, kcd_localOneArm x n) :=
      measureReal_mono (kcd_horizontal_subset_localOneArm n hn) (measure_ne_top _ _)
    _ ≤ ∑ x ∈ boxSV_boxF 2 n, μ.real (kcd_localOneArm x n) :=
      measureReal_biUnion_finset_le _ _
    _ = ((boxSV_boxF 2 n).card : ℝ) * crossProb 2 p hp n := by
      simp [μ, kcd_localOneArm_prob]



theorem kcd_quadratic_mul_exp_tendsto_zero {c C : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) ^ 2 * (C * Real.exp (-c * n)))
      atTop (𝓝 0) := by
  have hcn : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hpow (k : ℕ) :
      Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * n)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hcn
    have hcne : c ≠ 0 := hc.ne'
    convert h.const_mul ((c ^ k)⁻¹) using 1
    · funext n
      simp only [Function.comp_apply]
      field_simp [hcne]
      ring
    · simp
  have h2 := (hpow 2).const_mul (4 * C)
  have h1 := (hpow 1).const_mul (4 * C)
  have h0 := (hpow 0).const_mul C
  convert (h2.add h1).add h0 using 1
  · funext n
    ring
  · simp



theorem kcd_horizontal_tendsto_zero_of_exp (p : ℝ≥0) (hp : p ≤ 1)
    (hdecay : ∃ c > 0, ∃ C > 0,
      ∀ n, 0 < n → crossProb 2 p hp n ≤ C * Real.exp (-c * n)) :
    Tendsto (fun n : ℕ =>
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ)))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC, hdecay⟩ := hdecay
  have hub : Tendsto (fun n : ℕ =>
      (2 * (n : ℝ) + 1) ^ 2 * (C * Real.exp (-c * n))) atTop (𝓝 0) :=
    kcd_quadratic_mul_exp_tendsto_zero hc
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) _ hub
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  calc
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ))
        ≤ ((boxSV_boxF 2 n).card : ℝ) * crossProb 2 p hp n :=
      kcd_horizontal_prob_le_box_mul_crossProb p hp n (by omega)
    _ ≤ ((boxSV_boxF 2 n).card : ℝ) * (C * Real.exp (-c * n)) := by
      exact mul_le_mul_of_nonneg_left (hdecay n (by omega)) (Nat.cast_nonneg _)
    _ = (2 * (n : ℝ) + 1) ^ 2 * (C * Real.exp (-c * n)) := by
      rw [boxSV_card_boxF]
      push_cast
      ring




theorem kcd_crossProb_mono_param {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) {n : ℕ} (hn : 0 < n) :
    crossProb 2 p hp n ≤ crossProb 2 q hq n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hpI : (p : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨p.coe_nonneg, by exact_mod_cast hp⟩
  have hqI : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨q.coe_nonneg, by exact_mod_cast hq⟩
  have hmono : MonotoneOn (crossPoly 2 k) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (differentiable_boxCrossProb (d := 2) (k + 1)).continuous.continuousOn
      (differentiable_boxCrossProb (d := 2) (k + 1)).differentiableOn
    intro t ht
    rw [interior_Icc, Set.mem_Ioo] at ht
    exact deriv_boxCrossProb_nonneg (d := 2) (k + 1) t ht.1.le ht.2.le
  have hmain : crossProb 2 p hp (k + 1) ≤ crossProb 2 q hq (k + 1) := by calc
    crossProb 2 p hp (k + 1) = crossProbReal 2 (k + 1) p :=
      (crossProbReal_eq 2 (k + 1) p hp).symm
    _ = crossPoly 2 k p := crossProbReal_eq_prob k hpI.1 hpI.2
    _ ≤ crossPoly 2 k q := hmono hpI hqI hpqR
    _ = crossProbReal 2 (k + 1) q := (crossProbReal_eq_prob k hqI.1 hqI.2).symm
    _ = crossProb 2 q hq (k + 1) := crossProbReal_eq 2 (k + 1) q hq
  rw [hk, Nat.add_comm]
  exact hmain



theorem kcd_horizontal_sharpThreshold :
    ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
      Tendsto (fun n : ℕ =>
        (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
          (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ)))
        atTop (𝓝 0) := by
  intro p hp hpc
  obtain ⟨hsharp, hsub, -⟩ := sharpness_unconditional (d := 2) (by norm_num)
  have hp_pc : p < pc 2 := by
    rw [kst_criticalProbability_eq_pc] at hpc
    exact_mod_cast hpc
  have hp_tilde : p < tildePc 2 := by simpa [hsharp] using hp_pc
  have hbdd : BddAbove (tildePcSet 2) :=
    ⟨1, fun q hq => (mem_tildePcSet.mp hq).choose⟩
  have hne : (tildePcSet 2).Nonempty := by
    by_contra h
    have hempty : tildePcSet 2 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [tildePc, hempty, csSup_empty] at hp_tilde
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ p)) hp_tilde
  obtain ⟨q, hq, hpq⟩ := (lt_csSup_iff hbdd hne).1 hp_tilde
  have hq1 : q ≤ 1 := (mem_tildePcSet.mp hq).choose
  have hqdecay := hsub q hq hq1
  obtain ⟨c, hc, C, hC, hqbound⟩ := hqdecay
  have hpbound : ∀ n, 0 < n → crossProb 2 p hp n ≤ C * Real.exp (-c * n) := by
    intro n hn
    exact le_trans (kcd_crossProb_mono_param hp hq1 hpq.le hn) (hqbound n)
  exact kcd_horizontal_tendsto_zero_of_exp p hp ⟨c, hc, C, hC, hpbound⟩

end StatMech.TwoDim
