/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public section

section
namespace MathlibExt.Analysis.FunctionalAnalysis.DaugavetWanted

private lemma compact_subseq_tendsto_zero
    (T : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ))
    (hT : IsCompactOperator T)
    (u : ℕ → C(Set.Icc (0 : ℝ) 1, ℝ))
    (Cbound : ℝ)
    (hbound : ∀ s : Finset ℕ, ‖∑ i ∈ s, u i‖ ≤ Cbound) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => T (u (φ n))) Filter.atTop (nhds 0) := by
  have hCnonneg : 0 ≤ Cbound := by
    have h := hbound ∅
    simp at h
    linarith
  have hsingle : ∀ n, ‖u n‖ ≤ Cbound := by
    intro n
    have h := hbound {n}
    simpa using h
  have hT' : IsCompactOperator (⇑T.toLinearMap) := hT
  obtain ⟨K, hKcompact, hKsub⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := T.toLinearMap) hT' Cbound
  have hmem : ∀ n, T (u n) ∈ K := by
    intro n
    apply hKsub
    simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    exact ⟨u n, hsingle n, rfl⟩
  obtain ⟨a, _, φ, hφmono, hφlim⟩ := hKcompact.tendsto_subseq hmem
  have hces : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, T (u (φ i)))
      Filter.atTop (nhds a) :=
    Filter.Tendsto.cesaro_smul hφlim
  have hsumBound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, u (φ i)‖ ≤ Cbound := by
    intro n
    have heq : (∑ i ∈ Finset.range n, u (φ i)) = ∑ j ∈ (Finset.range n).map ⟨φ, hφmono.injective⟩, u
        j := by
      rw [Finset.sum_map]
      rfl
    rw [heq]
    exact hbound _
  have havg0 : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, T (u (φ i)))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro t
      have hle : ‖T (∑ i ∈ Finset.range t, u (φ i))‖ ≤ ‖T‖ * Cbound := by
        calc ‖T (∑ i ∈ Finset.range t, u (φ i))‖ ≤ ‖T‖ * ‖∑ i ∈ Finset.range t, u (φ i)‖ :=
              ContinuousLinearMap.le_opNorm T _
          _ ≤ ‖T‖ * Cbound := by
              gcongr
              exact hsumBound t
      calc ‖(t : ℝ)⁻¹ • ∑ i ∈ Finset.range t, T (u (φ i))‖
          = ‖(t : ℝ)⁻¹‖ * ‖T (∑ i ∈ Finset.range t, u (φ i))‖ := by
            rw [← map_sum]
            rw [norm_smul]
        _ ≤ ‖(t : ℝ)⁻¹‖ * (‖T‖ * Cbound) := by
            gcongr
        _ = (fun n : ℕ => ‖((n : ℝ))⁻¹‖ * (‖T‖ * Cbound)) t := rfl
    · have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have h2 : Filter.Tendsto (fun n : ℕ => ‖((n : ℝ))⁻¹‖ * (‖T‖ * Cbound)) Filter.atTop
          (nhds (‖(0:ℝ)‖ * (‖T‖ * Cbound))) := by
        apply Filter.Tendsto.mul _ tendsto_const_nhds
        exact h1.norm
      simpa using h2
  have ha0 : a = 0 := tendsto_nhds_unique hces havg0
  subst ha0
  exact ⟨φ, hφmono, hφlim⟩

/--
**Daugavet's theorem for compact operators.** Let $C[0,1]$ be the real Banach space of continuous
functions $[0,1] \to \mathbb{R}$ with the supremum norm, and let $I$ be the identity operator on
it. Every compact bounded linear operator $T : C[0,1] \to C[0,1]$ satisfies
$\|I + T\| = 1 + \|T\|$, where the norms are operator norms.

Proves `Wanted` entry `daugavet`.

Source: I. K. Daugavet, Izv. Vyssh.
Uchebn. Zaved. Matematika 1963; Kadets et al., 1980s Daugavet property; Werner, Recent progress on
Daugavet property, 2001; Lean states `C(Icc 0 1, ℝ)` compact-operator specialization of the
general Daugavet property `‖Id+T‖=1+‖T‖`.
-/
theorem daugavet
    (T : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ))
    (hT : IsCompactOperator T) :
    ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ = 1 + ‖T‖ := by
  apply le_antisymm
  · calc ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖
        ≤ ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ)‖ + ‖T‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
      _ = 1 + ‖T‖ := by rw [ContinuousLinearMap.norm_id]
  · apply le_of_forall_pos_le_add
    intro ε hε
    by_cases h2T : 2 * ‖T‖ ≤ ε
    · have hid : ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ)‖ = 1 :=
        ContinuousLinearMap.norm_id
      have htri : (‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ)‖ : ℝ) ≤
          ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ + ‖T‖ := by
        have hdecomp : ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) =
            (ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T) + (-T) := by
          simp
        conv_lhs => rw [hdecomp]
        calc ‖(ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T) + (-T)‖
            ≤ ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ + ‖-T‖ :=
              ContinuousLinearMap.opNorm_add_le _ _
          _ = ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ + ‖T‖ := by
              rw [ContinuousLinearMap.opNorm_neg]
      rw [hid] at htri
      linarith
    · push Not at h2T
      have hT_half : ε / 2 < ‖T‖ := by
        have hnn := norm_nonneg T
        linarith
      have hTpos : 0 < ‖T‖ := by linarith
      have hδpos : 0 < ε / 4 := by linarith
      have hCnonnegT : 0 ≤ ‖T‖ - ε / 4 := by linarith
      obtain ⟨f, hfnorm, hfgt⟩ : ∃ f : C(Set.Icc (0 : ℝ) 1, ℝ), ‖f‖ = 1 ∧ ‖T‖ - ε/4 < ‖T f‖ := by
        by_contra hcon
        push Not at hcon
        have hle : ‖T‖ ≤ ‖T‖ - ε/4 := by
          apply ContinuousLinearMap.opNorm_le_of_unit_norm hCnonnegT
          intro x hx
          exact hcon x hx
        linarith
      have hTf_gt : ε / 4 < ‖T f‖ := by linarith
      have hCnonnegTf : 0 ≤ ‖T f‖ - ε/4 := by linarith [norm_nonneg (T f)]
      obtain ⟨p, hpgt⟩ : ∃ p : ↥(Set.Icc (0:ℝ) 1), ‖T f‖ - ε/4 < ‖T f p‖ := by
        by_contra hcon
        push Not at hcon
        have hle : ‖T f‖ ≤ ‖T f‖ - ε/4 :=
          (ContinuousMap.norm_le (T f) hCnonnegTf).mpr hcon
        linarith
      set s : ℝ := (if 0 ≤ (T f) p then 1 else -1) with hsdef
      have hs_abs : |s| = 1 := by
        rw [hsdef]; split <;> simp
      have hs_add : |s + (T f) p| = 1 + |(T f) p| := by
        rw [hsdef]
        split
        · next h =>
          have habs : |(T f) p| = (T f) p := abs_of_nonneg h
          have hnn : (0:ℝ) ≤ 1 + (T f) p := by linarith [abs_nonneg ((T f) p)]
          rw [habs, abs_of_nonneg hnn]
        · next h =>
          push Not at h
          have habs : |(T f) p| = -((T f) p) := abs_of_neg h
          have hnn : (-1 + (T f) p) < 0 := by linarith
          have : |-1 + (T f) p| = 1 + |(T f) p| := by
            rw [habs, abs_of_neg hnn]; ring
          simpa using this
      set pval : ℝ := (p : ℝ) with hpval
      have hpmem : pval ∈ Set.Icc (0:ℝ) 1 := p.2
      rw [Set.mem_Icc] at hpmem
      obtain ⟨hp0, hp1⟩ := hpmem
      set d : ℝ := max pval (1 - pval) with hddef
      have hd_pos : 0 < d := by
        have : (1:ℝ)/2 ≤ d := by
          rw [hddef]
          rcases le_total pval (1 - pval) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        linarith
      set dir : ℝ := (if pval ≤ 1/2 then (1:ℝ) else -1) with hdirdef
      have hdir_sq : dir * dir = 1 := by
        rw [hdirdef]; split <;> norm_num
      set low : ℕ → ℝ := fun n => d / (2*(n:ℝ)+2) with hlowdef
      set high : ℕ → ℝ := fun n => d / (2*(n:ℝ)+1) with hhighdef
      set mid : ℕ → ℝ := fun n => (low n + high n)/2 with hmiddef
      set w : ℕ → ℝ := fun n => (high n - low n)/2 with hwdef
      have hlow_pos : ∀ n : ℕ, 0 < low n := by
        intro n; rw [hlowdef]; positivity
      have hhigh_pos : ∀ n : ℕ, 0 < high n := by
        intro n; rw [hhighdef]; positivity
      have hlow_lt_high : ∀ n : ℕ, low n < high n := by
        intro n
        rw [hlowdef, hhighdef]
        apply div_lt_div_of_pos_left hd_pos (by positivity) (by linarith)
      have hw_pos : ∀ n : ℕ, 0 < w n := by
        intro n; rw [hwdef]; have h := hlow_lt_high n; linarith
      have hhigh_le_d : ∀ n : ℕ, high n ≤ d := by
        intro n
        rw [hhighdef]
        have h1 : (1:ℝ) ≤ 2 * (n:ℝ) + 1 := by
          have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
          linarith
        calc d / (2 * (n:ℝ) + 1) ≤ d / 1 := by
              apply div_le_div_of_nonneg_left (le_of_lt hd_pos) (by norm_num) h1
          _ = d := by rw [div_one]
      have hmid_nonneg : ∀ n : ℕ, 0 ≤ mid n := by
        intro n
        rw [hmiddef]
        have h1 := hlow_pos n; have h2 := hhigh_pos n; linarith
      have hmid_le_high : ∀ n : ℕ, mid n ≤ high n := by
        intro n; rw [hmiddef]; have h := hlow_lt_high n; linarith
      have hmid_le_d : ∀ n : ℕ, mid n ≤ d := fun n => le_trans (hmid_le_high n) (hhigh_le_d n)
      set qval : ℕ → ℝ := fun n => pval + dir * mid n with hqdef
      have hq_mem : ∀ n : ℕ, qval n ∈ Set.Icc (0:ℝ) 1 := by
        intro n
        rw [Set.mem_Icc]
        by_cases hp_half : pval ≤ 1/2
        · have hdir1 : dir = 1 := by rw [hdirdef, ite_eq_left hp_half]
          have hd_eq : d = 1 - pval := by rw [hddef]; apply max_eq_right; linarith
          have hmidb := hmid_le_d n; have hmidnn := hmid_nonneg n
          rw [hd_eq] at hmidb
          simp only [hqdef, hdir1]
          constructor <;> linarith
        · push Not at hp_half
          have hdir1 : dir = -1 := by rw [hdirdef, ite_eq_right (by linarith)]
          have hd_eq : d = pval := by rw [hddef]; apply max_eq_left; linarith
          have hmidb := hmid_le_d n; have hmidnn := hmid_nonneg n
          rw [hd_eq] at hmidb
          simp only [hqdef, hdir1]
          constructor <;> linarith
      set bReal : ℕ → ℝ → ℝ := fun n x => max 0 (1 - |dir * (x - pval) - mid n| / w n) with hbdef
      have hb_cont : ∀ n, Continuous (bReal n) := by
        intro n
        rw [hbdef]
        fun_prop
      have hb_nonneg : ∀ n x, 0 ≤ bReal n x := by
        intro n x; rw [hbdef]; exact le_max_left _ _
      have hb_le_one : ∀ n x, bReal n x ≤ 1 := by
        intro n x
        rw [hbdef]
        apply max_le (by linarith)
        have hy : 0 ≤ |dir * (x - pval) - mid n| / w n :=
          div_nonneg (abs_nonneg _) (le_of_lt (hw_pos n))
        linarith
      have hb_supp : ∀ n x, bReal n x ≠ 0 → low n < dir * (x - pval) ∧ dir * (x - pval) < high
          n := by
        intro n x hb
        rw [hbdef] at hb
        have hw := hw_pos n
        have hpos : 0 < 1 - |dir * (x - pval) - mid n| / w n := by
          rcases eq_or_lt_of_le (le_max_left 0 (1 - |dir * (x - pval) - mid n| / w n)) with h | h
          · exfalso; exact hb h.symm
          · simpa using h
        have hlt : |dir * (x - pval) - mid n| / w n < 1 := by linarith
        have habs : |dir * (x - pval) - mid n| < w n := by rwa [div_lt_one hw] at hlt
        have hmid_eq : mid n = (low n + high n) / 2 := by rw [hmiddef]
        have hw_eq : w n = (high n - low n) / 2 := by rw [hwdef]
        rw [hmid_eq, hw_eq] at habs
        rw [abs_lt] at habs
        constructor <;> linarith
      have hdir_mid : ∀ n : ℕ, dir * (qval n - pval) = mid n := by
        intro n
        have hsq := hdir_sq
        have hq : qval n = pval + dir * mid n := by simp only [hqdef]
        rw [hq]
        calc dir * ((pval + dir * mid n) - pval) = (dir * dir) * mid n := by ring
          _ = mid n := by rw [hsq, one_mul]
      have hb_at_q : ∀ n : ℕ, bReal n (qval n) = 1 := by
        intro n
        simp only [hbdef]
        have h0 : |dir * (qval n - pval) - mid n| / w n = 0 := by
          rw [hdir_mid n, sub_self, abs_zero, zero_div]
        rw [h0, sub_zero]
        simp
      set bMap : ℕ → C(Set.Icc (0:ℝ) 1, ℝ) :=
        fun n => ⟨fun x => bReal n (x:ℝ), (hb_cont n).comp continuous_subtype_val⟩ with hbmapdef
      set sConst : C(Set.Icc (0:ℝ) 1, ℝ) := ContinuousMap.const _ s with hsconstdef
      set y : ℕ → C(Set.Icc (0:ℝ) 1, ℝ) :=
        fun n => f + bMap n * (sConst - f) with hydef
      set u : ℕ → C(Set.Icc (0:ℝ) 1, ℝ) :=
        fun n => bMap n * (sConst - f) with hudef
      set qq : ℕ → ↥(Set.Icc (0:ℝ) 1) := fun n => ⟨qval n, hq_mem n⟩ with hqqdef
      have hf_abs : ∀ x : ↥(Set.Icc (0:ℝ) 1), |f x| ≤ 1 := by
        intro x
        have h := ContinuousMap.norm_coe_le_norm f x
        rw [hfnorm] at h
        rwa [Real.norm_eq_abs] at h
      have hsle : |s| ≤ 1 := by rw [hs_abs]
      have hu_eq : ∀ n (x : ↥(Set.Icc (0:ℝ) 1)), (u n) x = bReal n (x:ℝ) * (s - f x) := by
        intro n x
        simp only [hudef, hbmapdef, hsconstdef]
        rw [ContinuousMap.mul_apply, ContinuousMap.sub_apply]
        rfl
      have hy_eq : ∀ n (x : ↥(Set.Icc (0:ℝ) 1)), (y n) x = f x + bReal n (x:ℝ) * (s - f x) := by
        intro n x
        simp only [hydef, hbmapdef, hsconstdef]
        rw [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply]
        rfl
      have hy_at_q : ∀ n, (y n) (qq n) = s := by
        intro n
        rw [hy_eq]
        have hb1 : bReal n (qq n) = 1 := by
          have hqqr : ((qq n : ℝ)) = qval n := rfl
          rw [hqqr]
          exact hb_at_q n
        rw [hb1]
        ring
      have hy_norm : ∀ n, ‖y n‖ ≤ 1 := by
        intro n
        apply (ContinuousMap.norm_le (y n) (by norm_num)).mpr
        intro x
        rw [Real.norm_eq_abs, hy_eq]
        have hb0 := hb_nonneg n (x:ℝ)
        have hb1 := hb_le_one n (x:ℝ)
        have hf1 := hf_abs x
        have h1 : f x + bReal n (x:ℝ) * (s - f x) = (1 - bReal n (x:ℝ)) * f x + bReal n (x:ℝ) *
            s := by ring
        rw [h1]
        calc |(1 - bReal n (x:ℝ)) * f x + bReal n (x:ℝ) * s|
            ≤ |(1 - bReal n (x:ℝ)) * f x| + |bReal n (x:ℝ) * s| := abs_add_le _ _
          _ = (1 - bReal n (x:ℝ)) * |f x| + bReal n (x:ℝ) * |s| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg
                  (by linarith : (0:ℝ) ≤ 1 - bReal n (x:ℝ))]
          _ ≤ (1 - bReal n (x:ℝ)) * 1 + bReal n (x:ℝ) * 1 := by gcongr
          _ = 1 := by ring
      have hu_bound_pt : ∀ n (x : ↥(Set.Icc (0:ℝ) 1)), |(u n) x| ≤ 2 := by
        intro n x
        rw [hu_eq]
        have hb0 := hb_nonneg n (x:ℝ)
        have hb1 := hb_le_one n (x:ℝ)
        have hf1 := hf_abs x
        calc |bReal n (x:ℝ) * (s - f x)| = bReal n (x:ℝ) * |s - f x| := by
              rw [abs_mul, abs_of_nonneg hb0]
          _ ≤ bReal n (x:ℝ) * (|s| + |f x|) := by
              gcongr
              calc |s - f x| = |s + (-f x)| := by rw [sub_eq_add_neg]
                _ ≤ |s| + |-f x| := abs_add_le _ _
                _ = |s| + |f x| := by rw [abs_neg]
          _ ≤ 1 * (1 + 1) := by gcongr
          _ = 2 := by ring
      have hdisj : ∀ n m (x : ↥(Set.Icc (0:ℝ) 1)), n ≠ m →
          bReal n (x:ℝ) ≠ 0 → bReal m (x:ℝ) ≠ 0 → False := by
        intro n m x hnm hn hm
        obtain ⟨h1lo, h1hi⟩ := hb_supp n _ hn
        obtain ⟨h2lo, h2hi⟩ := hb_supp m _ hm
        rcases lt_or_gt_of_ne hnm with h | h
        · have hle : high m ≤ low n := by
            rw [hhighdef, hlowdef]
            apply div_le_div_of_nonneg_left (le_of_lt hd_pos) (by positivity) (by
              have hnmr : (n:ℝ) + 1 ≤ (m:ℝ) := by
                have : n + 1 ≤ m := h
                exact_mod_cast this
              linarith)
          linarith
        · have hle : high n ≤ low m := by
            rw [hhighdef, hlowdef]
            apply div_le_div_of_nonneg_left (le_of_lt hd_pos) (by positivity) (by
              have hnmr : (m:ℝ) + 1 ≤ (n:ℝ) := by
                have : m + 1 ≤ n := by omega
                exact_mod_cast this
              linarith)
          linarith
      have hsum_bound : ∀ s_ : Finset ℕ, ‖∑ i ∈ s_, u i‖ ≤ 2 := by
        intro s_
        apply (ContinuousMap.norm_le _ (by norm_num)).mpr
        intro x
        rw [ContinuousMap.sum_apply, Real.norm_eq_abs]
        by_cases hex : ∃ i0 ∈ s_, bReal i0 (x:ℝ) ≠ 0
        · obtain ⟨i0, hi0mem, hi0ne⟩ := hex
          have hsum_eq : ∑ i ∈ s_, (u i) x = (u i0) x := by
            apply Finset.sum_eq_single i0 _ (by simp [hi0mem])
            intro b hb hbne
            rw [hu_eq]
            have hb0 : bReal b (x:ℝ) = 0 := by
              by_contra hcon
              exact hdisj b i0 x hbne hcon hi0ne
            rw [hb0, zero_mul]
          rw [hsum_eq]
          exact hu_bound_pt i0 x
        · push Not at hex
          have hzero : ∑ i ∈ s_, (u i) x = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [hu_eq]
            rw [hex i hi, zero_mul]
          rw [hzero, abs_zero]
          norm_num
      obtain ⟨φ, hφmono, hφlim⟩ := compact_subseq_tendsto_zero T hT u 2 hsum_bound
      have hhigh_tend : Filter.Tendsto (fun n : ℕ => high n) Filter.atTop (nhds 0) := by
        have h2n : Filter.Tendsto (fun n : ℕ => 2*(n:ℝ)) Filter.atTop Filter.atTop :=
          Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
        have h1 : Filter.Tendsto (fun n : ℕ => (2*(n:ℝ)+1)) Filter.atTop Filter.atTop :=
          Filter.Tendsto.atTop_add h2n tendsto_const_nhds
        have h2 : Filter.Tendsto (fun n : ℕ => (2*(n:ℝ)+1)⁻¹) Filter.atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp h1
        have heq : (fun n : ℕ => high n) = (fun n : ℕ => d * ((2*(n:ℝ)+1)⁻¹)) := by
          ext n
          simp only [hhighdef]
          rw [div_eq_mul_inv]
        rw [heq]
        simpa using h2.const_mul d
      have hmid_tend : Filter.Tendsto mid Filter.atTop (nhds 0) :=
        squeeze_zero (fun n => hmid_nonneg n) (fun n => hmid_le_high n) hhigh_tend
      have hqval_tend : Filter.Tendsto qval Filter.atTop (nhds pval) := by
        have hmid0 : Filter.Tendsto (fun n : ℕ => dir * mid n) Filter.atTop (nhds (dir * 0)) :=
          hmid_tend.const_mul dir
        simp only [mul_zero] at hmid0
        have hadd : Filter.Tendsto (fun n : ℕ => pval + dir * mid n) Filter.atTop
            (nhds (pval + 0)) :=
          tendsto_const_nhds.add hmid0
        simp only [add_zero] at hadd
        have heq : qval = (fun n : ℕ => pval + dir * mid n) := by simp only [hqdef]
        rw [heq]
        exact hadd
      have hqq_tend : Filter.Tendsto qq Filter.atTop (nhds p) := by
        rw [tendsto_subtype_rng]
        have h1 : (fun x : ℕ => ((qq x : ↥(Set.Icc (0:ℝ) 1)) : ℝ)) = qval := rfl
        have h2 : ((p : ↥(Set.Icc (0:ℝ) 1)) : ℝ) = pval := by rw [hpval]
        rw [h1, h2]
        exact hqval_tend
      have hTf_tend : Filter.Tendsto (fun n => (T f) (qq (φ n))) Filter.atTop (nhds ((T f) p)) :=
        ((T f).continuous.tendsto p).comp (hqq_tend.comp hφmono.tendsto_atTop)
      have hTu_eval_tend : Filter.Tendsto (fun n => (T (u (φ n))) (qq (φ n))) Filter.atTop
          (nhds 0) := by
        apply squeeze_zero_norm
        · intro n
          calc ‖(T (u (φ n))) (qq (φ n))‖ ≤ ‖T (u (φ n))‖ :=
                ContinuousMap.norm_coe_le_norm _ _
            _ = (fun n : ℕ => ‖T (u (φ n))‖) n := rfl
        · simpa using hφlim.norm
      have hcomb : Filter.Tendsto (fun n => s + (T f) (qq (φ n)) + (T (u (φ n))) (qq (φ n)))
          Filter.atTop (nhds (s + (T f) p)) := by
        have h1 : Filter.Tendsto (fun n => s + (T f) (qq (φ n))) Filter.atTop
            (nhds (s + (T f) p)) :=
          tendsto_const_nhds.add hTf_tend
        have h2 := h1.add hTu_eval_tend
        simpa using h2
      have hyu : ∀ k, y k = f + u k := by
        intro k
        simp only [hydef, hudef]
      have hbound_each : ∀ n, |s + (T f) (qq (φ n)) + (T (u (φ n))) (qq (φ n))| ≤
          ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ := by
        intro n
        have hTy : T (y (φ n)) = T f + T (u (φ n)) := by rw [hyu, map_add]
        have heq : ((ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T) (y (φ n))) (qq (φ n)) =
            s + (T f) (qq (φ n)) + (T (u (φ n))) (qq (φ n)) := by
          have h1 : ((ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T) (y (φ n))) =
              y (φ n) + T (y (φ n)) := by simp
          have h2 : (y (φ n) + T (y (φ n))) (qq (φ n)) =
              (y (φ n)) (qq (φ n)) + (T (y (φ n))) (qq (φ n)) :=
            ContinuousMap.add_apply _ _ _
          rw [h1, h2, hy_at_q, hTy]
          rw [ContinuousMap.add_apply, add_assoc]
        calc |s + (T f) (qq (φ n)) + (T (u (φ n))) (qq (φ n))|
            = ‖((ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T) (y (φ n))) (qq (φ n))‖ := by
              rw [heq, Real.norm_eq_abs]
          _ ≤ ‖(ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T) (y (φ n))‖ :=
              ContinuousMap.norm_coe_le_norm _ _
          _ ≤ ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ * ‖y (φ n)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ * 1 := by
              gcongr
              exact hy_norm _
          _ = ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ := mul_one _
      have hle_abs : |s + (T f) p| ≤ ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ := by
        have hlim_abs : Filter.Tendsto
            (fun n => |s + (T f) (qq (φ n)) + (T (u (φ n))) (qq (φ n))|)
            Filter.atTop (nhds |s + (T f) p|) :=
          (continuous_abs.tendsto _).comp hcomb
        exact le_of_tendsto hlim_abs (Filter.Eventually.of_forall hbound_each)
      have hTf_abs : ‖T f‖ - ε/4 < |(T f) p| := by
        have h := hpgt
        rw [Real.norm_eq_abs] at h
        exact h
      have h1 : 1 + |(T f) p| ≤ ‖ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, ℝ) + T‖ := by
        rw [← hs_add]
        exact hle_abs
      linarith

end MathlibExt.Analysis.FunctionalAnalysis.DaugavetWanted
