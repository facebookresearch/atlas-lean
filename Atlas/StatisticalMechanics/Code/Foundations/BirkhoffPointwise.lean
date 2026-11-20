/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Foundations.MaximalErgodicGarsia

open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal

namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}




def IsInvariantSet (T : α → α) (E : Set α) : Prop := ∀ x, x ∈ E ↔ T x ∈ E

omit [MeasurableSpace α] in
theorem IsInvariantSet.iterate {E : Set α} (hE : IsInvariantSet T E) (k : ℕ) (x : α) :
    x ∈ E ↔ T^[k] x ∈ E := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, Function.iterate_succ_apply', hE]

omit [MeasurableSpace α] in


theorem birkhoffSum_indicator {E : Set α} (hE : IsInvariantSet T E) (g : α → ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (E.indicator g) n x = E.indicator (fun y => birkhoffSum T g n y) x := by
  simp only [birkhoffSum, Set.indicator]
  by_cases hx : x ∈ E
  · simp only [hx, if_true]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [if_pos ((hE.iterate k x).mp hx)]
  · simp only [hx, if_false]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg (fun h => hx ((hE.iterate k x).mpr h))]

open StatMech.GarsiaMax in
omit [MeasurableSpace α] in


theorem maxPartialSum_indicator {E : Set α} (hE : IsInvariantSet T E) (g : α → ℝ) {N : ℕ}
    (hN : 1 ≤ N) (x : α) :
    maxPartialSum T (E.indicator g) N hN x =
      E.indicator (fun y => maxPartialSum T g N hN y) x := by
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    unfold maxPartialSum
    refine Finset.sup'_congr _ rfl (fun n _ => ?_)
    rw [birkhoffSum_indicator hE g n x, Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx]
    unfold maxPartialSum
    have h0 : ∀ n ∈ Finset.Icc 1 N, birkhoffSum T (E.indicator g) n x = 0 := by
      intro n _
      rw [birkhoffSum_indicator hE g n x, Set.indicator_of_notMem hx]
    rw [Finset.sup'_congr _ rfl h0]
    simp

open StatMech.GarsiaMax in
omit [MeasurableSpace α] in

theorem setOf_maxPartialSum_indicator {E : Set α} (hE : IsInvariantSet T E) (g : α → ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    {x | 0 < maxPartialSum T (E.indicator g) N hN x}
      = E ∩ {x | 0 < maxPartialSum T g N hN x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, maxPartialSum_indicator hE g hN x]
  by_cases hx : x ∈ E
  · simp [hx]
  · simp [hx]

open StatMech.GarsiaMax in
omit [MeasurableSpace α] in

theorem maxPartialSum_mono (g : α → ℝ) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : N ≤ M) (x : α) :
    maxPartialSum T g N hN x ≤ maxPartialSum T g M hM x := by
  obtain ⟨n, hn1, hn2, hneq⟩ := exists_eq_maxPartialSum hN x
  rw [← hneq]
  exact birkhoffSum_le_maxPartialSum hM hn1 (le_trans hn2 hNM) x









omit [MeasurableSpace α] in

theorem cocycle_avg (x : α) (n : ℕ) :
    ((n : ℝ) + 1) * birkhoffAverage ℝ T f (n + 1) x
      = f x + (n : ℝ) * birkhoffAverage ℝ T f n (T x) := by
  simp only [birkhoffAverage, smul_eq_mul]
  rw [birkhoffSum_succ' T f n x]
  have e1 : ((n : ℝ) + 1) * ((↑(n + 1))⁻¹ * (f x + birkhoffSum T f n (T x)))
      = f x + birkhoffSum T f n (T x) := by
    rw [show ((n : ℕ) + 1 : ℕ) = (n + 1) from rfl]; push_cast; field_simp
  rw [e1]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [birkhoffSum_zero]
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp

omit [MeasurableSpace α] in

theorem avg_comp_eq (x : α) {n : ℕ} (hn : 1 ≤ n) :
    birkhoffAverage ℝ T f n (T x)
      = (((n : ℝ) + 1) / n) * birkhoffAverage ℝ T f (n + 1) x - (f x) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have := cocycle_avg (T := T) (f := f) x n
  field_simp at this ⊢; linarith [this]

omit [MeasurableSpace α] in

theorem avg_succ_eq (x : α) (n : ℕ) :
    birkhoffAverage ℝ T f (n + 1) x
      = ((n : ℝ) / (n + 1)) * birkhoffAverage ℝ T f n (T x) + (f x) / (n + 1) := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have := cocycle_avg (T := T) (f := f) x n
  field_simp at this ⊢; linarith [this]

omit [MeasurableSpace α] in

theorem limsup_avg_comp_le (x : α) :
    limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop
      ≤ limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop := by
  set L : EReal := limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop with hL
  rw [limsup_le_iff']
  intro y hyL
  obtain ⟨z, hLz, hzy⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have h0 : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f n x : ℝ) : EReal) < (z : EReal) :=
    eventually_lt_of_limsup_lt (hL ▸ hLz)
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T f (n + 1) x < z := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually h0] with n hn
    exact_mod_cast hn
  have hr : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / n) * z - (f x) / n) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) / n = 1 + 1 / (n : ℝ) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp
      rw [tendsto_congr' key]
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => (f x) / (n : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := f x)).div_atTop tendsto_natCast_atTop_atTop
    simpa using (h1.mul tendsto_const_nhds).sub h2
  have hbound : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T f n (T x) < (((n : ℝ) + 1) / n) * z - (f x) / n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    rw [avg_comp_eq x hn1]
    have hpos : 0 < ((n : ℝ) + 1) / n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      positivity
    have hmul : (((n : ℝ) + 1) / n) * birkhoffAverage ℝ T f (n + 1) x < (((n : ℝ) + 1) / n) * z :=
      mul_lt_mul_of_pos_left hn hpos
    linarith
  rcases eq_top_or_lt_top y with hytop | hytop
  · filter_upwards with n; rw [hytop]; exact le_top
  · have hybot : y ≠ ⊥ := fun h => by rw [h] at hzy; exact not_lt_bot hzy
    have hyr : y = (y.toReal : EReal) := (EReal.coe_toReal hytop.ne hybot).symm
    have hzyr : z < y.toReal := by rw [hyr] at hzy; exact_mod_cast hzy
    have hrlt : ∀ᶠ n : ℕ in atTop, (((n : ℝ) + 1) / n) * z - (f x) / n < y.toReal :=
      hr.eventually (eventually_lt_nhds hzyr)
    filter_upwards [hbound, hrlt] with n hn1 hn2
    have hlt : birkhoffAverage ℝ T f n (T x) < y.toReal := lt_trans hn1 hn2
    rw [hyr]; exact_mod_cast hlt.le

omit [MeasurableSpace α] in

theorem limsup_avg_le_comp (x : α) :
    limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop
      ≤ limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop := by
  set L : EReal := limsup (fun n => ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal)) atTop with hL
  rw [limsup_le_iff']
  intro y hyL
  obtain ⟨z, hLz, hzy⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have h0 : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f n (T x) : ℝ) : EReal) < (z : EReal) :=
    eventually_lt_of_limsup_lt (hL ▸ hLz)
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T f n (T x) < z := by
    filter_upwards [h0] with n hn; exact_mod_cast hn
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) * z + (f x) / (n + 1)) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (n + 1) = 1 - 1 / ((n : ℝ) + 1) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [tendsto_congr' key]
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
    have h2 : Tendsto (fun n : ℕ => (f x) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := f x)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using (h1.mul tendsto_const_nhds).add h2
  have hbound : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T f (n + 1) x < ((n : ℝ) / (n + 1)) * z + (f x) / (n + 1) := by
    filter_upwards [hev, eventually_gt_atTop 0] with n hn h0n
    rw [avg_succ_eq x n]
    have hmul' : ((n : ℝ) / (n + 1)) * birkhoffAverage ℝ T f n (T x) < ((n : ℝ) / (n + 1)) * z :=
      mul_lt_mul_of_pos_left hn (by positivity)
    linarith
  rcases eq_top_or_lt_top y with hytop | hytop
  · filter_upwards with n; rw [hytop]; exact le_top
  · have hybot : y ≠ ⊥ := fun h => by rw [h] at hzy; exact not_lt_bot hzy
    have hyr : y = (y.toReal : EReal) := (EReal.coe_toReal hytop.ne hybot).symm
    have hzyr : z < y.toReal := by rw [hyr] at hzy; exact_mod_cast hzy
    have hrlt : ∀ᶠ n : ℕ in atTop, ((n : ℝ) / (n + 1)) * z + (f x) / (n + 1) < y.toReal :=
      hr.eventually (eventually_lt_nhds hzyr)
    have hsucc : ∀ᶠ n in atTop, ((birkhoffAverage ℝ T f (n + 1) x : ℝ) : EReal) ≤ y := by
      filter_upwards [hbound, hrlt] with n hn1 hn2
      have hlt : birkhoffAverage ℝ T f (n + 1) x < y.toReal := lt_trans hn1 hn2
      rw [hyr]; exact_mod_cast hlt.le
    rw [eventually_atTop] at hsucc ⊢
    obtain ⟨N, hN⟩ := hsucc
    exact ⟨N + 1, fun m hm => by
      have := hN (m - 1) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this⟩




noncomputable def fStar (T : α → α) (f : α → ℝ) (x : α) : EReal :=
  limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop


noncomputable def fStarLow (T : α → α) (f : α → ℝ) (x : α) : EReal :=
  liminf (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop

omit [MeasurableSpace α] in

theorem fStar_comp (x : α) : fStar T f (T x) = fStar T f x :=
  le_antisymm (limsup_avg_comp_le x) (limsup_avg_le_comp x)

omit [MeasurableSpace α] in

theorem coe_avg_neg (x : α) (n : ℕ) :
    ((birkhoffAverage ℝ T (-f) n x : ℝ) : EReal) = -((birkhoffAverage ℝ T f n x : ℝ) : EReal) := by
  rw [show (birkhoffAverage ℝ T (-f) n x : ℝ) = -(birkhoffAverage ℝ T f n x : ℝ) by
    rw [birkhoffAverage_neg]; rfl, EReal.coe_neg]

omit [MeasurableSpace α] in

theorem fStarLow_eq_neg_fStar_neg (x : α) : fStarLow T f x = -fStar T (-f) x := by
  unfold fStarLow fStar
  rw [← EReal.liminf_neg]
  refine liminf_congr ?_
  filter_upwards with n
  rw [Pi.neg_apply, coe_avg_neg, neg_neg]

omit [MeasurableSpace α] in

theorem fStarLow_comp (x : α) : fStarLow T f (T x) = fStarLow T f x := by
  rw [fStarLow_eq_neg_fStar_neg, fStarLow_eq_neg_fStar_neg, fStar_comp]



open StatMech.GarsiaMax in









theorem setIntegral_nonneg_of_invariant (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : Integrable g μ) {E : Set α} (hEmeas : NullMeasurableSet E μ) (hEinv : IsInvariantSet T E)
    (hpos : ∀ x ∈ E, ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x) :
    0 ≤ ∫ x in E, g x ∂μ := by
  
  have hgE : Integrable (E.indicator g) μ := hg.indicator₀ hEmeas
  
  set s : ℕ → Set α := fun N => {x | 0 < maxPartialSum T (E.indicator g) (N + 1) N.succ_pos x}
    with hs_def
  
  have hs_eq : ∀ N, s N = E ∩ {x | 0 < maxPartialSum T g (N + 1) N.succ_pos x} := by
    intro N
    exact setOf_maxPartialSum_indicator hEinv g N.succ_pos
  
  have hM_int : ∀ N : ℕ, Integrable
      (fun x => maxPartialSum T (E.indicator g) (N + 1) N.succ_pos x) μ :=
    fun N => integrable_maxPartialSum hT hgE N.succ_pos
  have hs_meas : ∀ N, NullMeasurableSet (s N) μ := fun N =>
    nullMeasurableSet_lt aemeasurable_const (hM_int N).aestronglyMeasurable.aemeasurable
  
  have hs_subE : ∀ N, s N ⊆ E := by
    intro N
    rw [hs_eq N]; exact Set.inter_subset_left
  
  have hs_mono : Monotone s := by
    intro N M hNM x hx
    simp only [hs_def, Set.mem_setOf_eq] at hx ⊢
    exact lt_of_lt_of_le hx
      (maxPartialSum_mono (E.indicator g) N.succ_pos M.succ_pos (Nat.succ_le_succ hNM) x)
  
  have hs_union : (⋃ N, s N) = E := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset hs_subE
    · intro x hxE
      obtain ⟨n, hn1, hnpos⟩ := hpos x hxE
      refine Set.mem_iUnion.mpr ⟨n - 1, ?_⟩
      rw [hs_eq]
      refine ⟨hxE, ?_⟩
      simp only [Set.mem_setOf_eq]
      
      have heq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn1
      have hle : birkhoffSum T g n x ≤ maxPartialSum T g (n - 1 + 1) (n - 1).succ_pos x :=
        birkhoffSum_le_maxPartialSum (n - 1).succ_pos hn1 (by omega) x
      exact lt_of_lt_of_le hnpos hle
  
  have hgarsia : ∀ N, 0 ≤ ∫ x in s N, g x ∂μ := by
    intro N
    have hG := garsia_maximal_inequality (T := T) (f := E.indicator g) hT hgE N.succ_pos
    
    have hset : {x | 0 < maxPartialSum T (E.indicator g) (N + 1) N.succ_pos x} = s N := rfl
    rw [hset] at hG
    
    rwa [setIntegral_congr_fun₀ (hs_meas N)
      (fun x hx => Set.indicator_of_mem (hs_subE N hx) g)] at hG
  
  have hlim : Tendsto (fun N => ∫ x in s N, g x ∂μ) atTop (𝓝 (∫ x in E, g x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone₀ (μ := μ) (f := g) hs_meas hs_mono
      (by rw [hs_union]; exact hg.integrableOn)
    rwa [hs_union] at h
  exact ge_of_tendsto' hlim hgarsia




theorem aestronglyMeasurable_birkhoffAverage (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (n : ℕ) : AEStronglyMeasurable (fun x => birkhoffAverage ℝ T f n x) μ := by
  have hbs : Integrable (fun x => birkhoffSum T f n x) μ := by
    simp only [birkhoffSum]
    refine integrable_finsetSum _ fun i _ => ?_
    rw [← memLp_one_iff_integrable] at hf ⊢
    exact hf.comp_measurePreserving (hT.iterate i)
  simp only [birkhoffAverage]
  exact AEStronglyMeasurable.const_smul hbs.aestronglyMeasurable ((n : ℝ)⁻¹)


theorem aemeasurable_coe_birkhoffAverage (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (n : ℕ) : AEMeasurable (fun x => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) μ :=
  measurable_coe_real_ereal.comp_aemeasurable
    (aestronglyMeasurable_birkhoffAverage hT hf n).aemeasurable


theorem aemeasurable_fStar (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    AEMeasurable (fStar T f) μ := by
  have hA := aemeasurable_coe_birkhoffAverage hT hf
  refine ⟨fun x => limsup (fun n => (hA n).mk _ x) atTop,
    Measurable.limsup (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((birkhoffAverage ℝ T f n x : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  exact limsup_congr (Eventually.of_forall fun n => hx n)


theorem aemeasurable_fStarLow (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    AEMeasurable (fStarLow T f) μ := by
  have hA := aemeasurable_coe_birkhoffAverage hT hf
  refine ⟨fun x => liminf (fun n => (hA n).mk _ x) atTop,
    Measurable.liminf (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((birkhoffAverage ℝ T f n x : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  exact liminf_congr (Eventually.of_forall fun n => hx n)



omit [MeasurableSpace α] in

theorem birkhoffSum_sub_const (b : ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (fun y => f y - b) n x = birkhoffSum T f n x - n • b := by
  have hsub := birkhoffSum_sub T f (fun _ => b) n x
  have hconst : (fun (_ : α) => b) ∘ T = (fun (_ : α) => b) := rfl
  rw [show (fun y => f y - b) = f - (fun _ => b) from rfl, hsub, birkhoffSum_of_comp_eq hconst]
  simp

omit [MeasurableSpace α] in


theorem exists_birkhoffSum_sub_pos {b : ℝ} {x : α} (hx : (b : EReal) < fStar T f x) :
    ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y => f y - b) n x := by
  have hfreq : ∃ᶠ n in atTop, (b : EReal) < ((birkhoffAverage ℝ T f n x : ℝ) : EReal) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hx
  have hfreq' : ∃ᶠ n in atTop, 1 ≤ n ∧ b < birkhoffAverage ℝ T f n x := by
    refine hfreq.mp ?_
    filter_upwards [eventually_ge_atTop 1] with n hn hlt
    exact ⟨hn, by exact_mod_cast hlt⟩
  obtain ⟨n, hn1, hlt⟩ := hfreq'.exists
  refine ⟨n, hn1, ?_⟩
  
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [birkhoffSum_sub_const]
  simp only [birkhoffAverage, smul_eq_mul] at hlt
  rw [nsmul_eq_mul]
  
  have hmul : (n : ℝ) * b < (n : ℝ) * ((n : ℝ)⁻¹ * birkhoffSum T f n x) :=
    mul_lt_mul_of_pos_left hlt hn0
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul] at hmul
  linarith

omit [MeasurableSpace α] in


theorem exists_birkhoffSum_sub_pos' {a : ℝ} {x : α} (hx : fStarLow T f x < (a : EReal)) :
    ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y => a - f y) n x := by
  
  have hx' : ((-a : ℝ) : EReal) < fStar T (-f) (x) := by
    rw [fStarLow_eq_neg_fStar_neg] at hx
    have h1 : -fStar T (-f) x < (a : EReal) := hx
    rw [EReal.coe_neg]
    exact EReal.neg_lt_comm.mp h1
  obtain ⟨n, hn1, hpos⟩ := exists_birkhoffSum_sub_pos (f := -f) (b := -a) (x := x) hx'
  refine ⟨n, hn1, ?_⟩
  have hcongr : (fun y => (-f) y - (-a)) = (fun y => a - f y) := by funext y; simp; ring
  rwa [hcongr] at hpos



variable [IsFiniteMeasure μ]



def levelSet (T : α → α) (f : α → ℝ) (a b : ℝ) : Set α :=
  {x | fStarLow T f x < (a : EReal) ∧ (b : EReal) < fStar T f x}

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem isInvariantSet_levelSet (a b : ℝ) : IsInvariantSet T (levelSet T f a b) := by
  intro x
  simp only [levelSet, Set.mem_setOf_eq, fStar_comp, fStarLow_comp]

omit [IsFiniteMeasure μ] in

theorem nullMeasurableSet_levelSet (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (a b : ℝ) :
    NullMeasurableSet (levelSet T f a b) μ := by
  have h1 : NullMeasurableSet {x | fStarLow T f x < (a : EReal)} μ :=
    nullMeasurableSet_lt (aemeasurable_fStarLow hT hf) aemeasurable_const
  have h2 : NullMeasurableSet {x | (b : EReal) < fStar T f x} μ :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_fStar hT hf)
  exact h1.inter h2



theorem setIntegral_ge_of_lt_fStar (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {b : ℝ} {E : Set α} (hEmeas : NullMeasurableSet E μ) (hEinv : IsInvariantSet T E)
    (hE : ∀ x ∈ E, (b : EReal) < fStar T f x) :
    b * (μ E).toReal ≤ ∫ x in E, f x ∂μ := by
  have hgb : Integrable (fun y => f y - b) μ := hf.sub (integrable_const b)
  have hnn : 0 ≤ ∫ x in E, (f x - b) ∂μ :=
    setIntegral_nonneg_of_invariant hT hgb hEmeas hEinv
      (fun x hx => exists_birkhoffSum_sub_pos (hE x hx))
  have hsplit : ∫ x in E, (f x - b) ∂μ = (∫ x in E, f x ∂μ) - b * (μ E).toReal := by
    rw [integral_sub hf.integrableOn (integrable_const b).integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, Measure.real]
  linarith [hsplit ▸ hnn]



theorem setIntegral_le_of_fStarLow_lt (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {a : ℝ} {E : Set α} (hEmeas : NullMeasurableSet E μ) (hEinv : IsInvariantSet T E)
    (hE : ∀ x ∈ E, fStarLow T f x < (a : EReal)) :
    ∫ x in E, f x ∂μ ≤ a * (μ E).toReal := by
  have hga : Integrable (fun y => a - f y) μ := (integrable_const a).sub hf
  have hnn : 0 ≤ ∫ x in E, (a - f x) ∂μ :=
    setIntegral_nonneg_of_invariant hT hga hEmeas hEinv
      (fun x hx => exists_birkhoffSum_sub_pos' (hE x hx))
  have hsplit : ∫ x in E, (a - f x) ∂μ = a * (μ E).toReal - ∫ x in E, f x ∂μ := by
    rw [integral_sub (integrable_const a).integrableOn hf.integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, Measure.real]
  linarith [hsplit ▸ hnn]







theorem measure_levelSet_eq_zero (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {a b : ℝ} (hab : a < b) : μ (levelSet T f a b) = 0 := by
  set E := levelSet T f a b with hEdef
  have hEinv : IsInvariantSet T E := isInvariantSet_levelSet a b
  have hEmeas : NullMeasurableSet E μ := nullMeasurableSet_levelSet hT hf a b
  set m : ℝ := (μ E).toReal with hm
  have hlow : b * m ≤ ∫ x in E, f x ∂μ :=
    setIntegral_ge_of_lt_fStar hT hf hEmeas hEinv (fun x hx => hx.2)
  have hupp : ∫ x in E, f x ∂μ ≤ a * m :=
    setIntegral_le_of_fStarLow_lt hT hf hEmeas hEinv (fun x hx => hx.1)
  
  have hbm_le_am : b * m ≤ a * m := le_trans hlow hupp
  have hm_nonneg : 0 ≤ m := ENNReal.toReal_nonneg
  have hm_zero : m = 0 := by
    by_contra hne
    have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hne)
    nlinarith [hbm_le_am, hab, hm_pos]
  have hfin : μ E ≠ ∞ := measure_ne_top μ E
  rwa [hm, ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at hm_zero








theorem fStar_lt_top_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, fStar T f x < ⊤ := by
  set C : ℝ := ∫ x, |f x| ∂μ with hC
  have hCnn : 0 ≤ C := integral_nonneg (fun x => abs_nonneg _)
  
  have htop : μ {x | fStar T f x = ⊤} = 0 := by
    set S : Set α := {x | fStar T f x = ⊤} with hSdef
    have hSmeas : NullMeasurableSet S μ := by
      have : S = (fStar T f) ⁻¹' {⊤} := by ext x; simp [hSdef]
      rw [this]
      exact (aemeasurable_fStar hT hf).nullMeasurableSet_preimage (measurableSet_singleton ⊤)
    
    have hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * (μ S).toReal ≤ C := by
      intro n hn
      set E : Set α := {x | ((n : ℝ) : EReal) < fStar T f x} with hEdef
      have hEinv : IsInvariantSet T E := by
        intro x; simp only [hEdef, Set.mem_setOf_eq, fStar_comp]
      have hEmeas : NullMeasurableSet E μ :=
        nullMeasurableSet_lt aemeasurable_const (aemeasurable_fStar hT hf)
      have hSsubE : S ⊆ E := by
        intro x hx
        simp only [hEdef, Set.mem_setOf_eq]
        rw [show fStar T f x = ⊤ from hx]; exact EReal.coe_lt_top _
      have hge : (n : ℝ) * (μ E).toReal ≤ ∫ x in E, f x ∂μ :=
        setIntegral_ge_of_lt_fStar hT hf hEmeas hEinv (fun x hx => hx)
      have hfle : ∫ x in E, f x ∂μ ≤ C := by
        calc ∫ x in E, f x ∂μ ≤ ∫ x in E, |f x| ∂μ :=
              setIntegral_mono_ae hf.integrableOn (hf.abs).integrableOn
                (Eventually.of_forall fun x => le_abs_self _)
          _ ≤ C := by
              rw [hC]
              exact setIntegral_le_integral hf.abs (Eventually.of_forall fun x => abs_nonneg _)
      have hSEle : (μ S).toReal ≤ (μ E).toReal :=
        measureReal_mono hSsubE
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc (n : ℝ) * (μ S).toReal ≤ (n : ℝ) * (μ E).toReal := by gcongr
        _ ≤ ∫ x in E, f x ∂μ := hge
        _ ≤ C := hfle
    
    have hmSnn : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
    have hmS0 : (μ S).toReal = 0 := by
      by_contra hne
      have hpos : 0 < (μ S).toReal := lt_of_le_of_ne hmSnn (Ne.symm hne)
      
      obtain ⟨n, hn⟩ := exists_nat_gt (C / (μ S).toReal)
      have hn1 : 1 ≤ max n 1 := le_max_right _ _
      have hbd := hbound (max n 1) hn1
      have hnle : (n : ℝ) ≤ (max n 1 : ℕ) := by exact_mod_cast le_max_left _ _
      have : C / (μ S).toReal < (max n 1 : ℕ) := lt_of_lt_of_le hn hnle
      rw [div_lt_iff₀ hpos] at this
      nlinarith [hbd, this]
    have hfin : μ S ≠ ∞ := measure_ne_top μ S
    rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at hmS0
  
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) htop
  simp only [not_lt, top_le_iff] at hx
  exact hx



theorem fStarLow_bot_lt_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ⊥ < fStarLow T f x := by
  have h := fStar_lt_top_ae hT (f := -f) hf.neg
  filter_upwards [h] with x hx
  rw [fStarLow_eq_neg_fStar_neg]
  rw [show (⊥ : EReal) = -(⊤ : EReal) from rfl]
  exact EReal.neg_lt_neg_iff.mpr hx





theorem fStarLow_ae_eq_fStar (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    fStarLow T f =ᵐ[μ] fStar T f := by
  
  have hnull : μ {x | fStarLow T f x < fStar T f x} = 0 := by
    refine measure_mono_null
      (t := ⋃ q : {q : ℚ × ℚ // q.1 < q.2}, levelSet T f (q.1.1 : ℝ) (q.1.2 : ℝ)) ?_ ?_
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨b, hub, hbv⟩ := EReal.lt_iff_exists_rat_btwn.mp hx
      obtain ⟨a, hua, hab⟩ := EReal.lt_iff_exists_rat_btwn.mp hub
      have hab' : a < b := by exact_mod_cast (EReal.coe_lt_coe_iff.mp hab)
      exact Set.mem_iUnion.mpr ⟨⟨(a, b), hab'⟩, hua, hbv⟩
    · refine measure_iUnion_null fun q => measure_levelSet_eq_zero hT hf ?_
      exact_mod_cast q.2
  rw [Filter.EventuallyEq, ae_iff]
  
  have hle : ∀ x, fStarLow T f x ≤ fStar T f x := fun x => by
    unfold fStarLow fStar; exact liminf_le_limsup
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact lt_of_le_of_ne (hle x) hx


noncomputable def birkhoffLimit (T : α → α) (f : α → ℝ) (x : α) : ℝ := (fStar T f x).toReal










theorem tendsto_birkhoffAverage_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (birkhoffLimit T f x)) := by
  filter_upwards [fStarLow_ae_eq_fStar hT hf, fStar_lt_top_ae hT hf, fStarLow_bot_lt_ae hT hf]
    with x heq htop hbot
  
  set ℓ : EReal := fStar T f x with hℓ
  have hlow_eq : liminf (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop = ℓ := heq
  have hsup_eq : limsup (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop = ℓ := rfl
  have htend : Tendsto (fun n => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) atTop (𝓝 ℓ) :=
    tendsto_of_liminf_eq_limsup hlow_eq hsup_eq
  have hbot' : (⊥ : EReal) < ℓ := hbot.trans_eq heq
  have hℓr : ℓ = ((ℓ.toReal : ℝ) : EReal) := (EReal.coe_toReal htop.ne hbot'.ne').symm
  rw [hℓr, EReal.tendsto_coe] at htend
  exact htend

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem birkhoffLimit_comp (x : α) : birkhoffLimit T f (T x) = birkhoffLimit T f x := by
  unfold birkhoffLimit; rw [fStar_comp]

omit [IsFiniteMeasure μ] in

theorem aemeasurable_birkhoffLimit (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    AEMeasurable (birkhoffLimit T f) μ :=
  (aemeasurable_fStar hT hf).ereal_toReal



omit [IsFiniteMeasure μ] in


theorem eLpNorm_birkhoffAverage_le (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    eLpNorm (fun x => birkhoffAverage ℝ T f n x) 1 μ ≤ eLpNorm f 1 μ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [birkhoffAverage_zero']
  have hfm : ∀ k, AEStronglyMeasurable (fun x => f (T^[k] x)) μ := by
    intro k
    rw [← memLp_one_iff_integrable] at hf
    exact (hf.comp_measurePreserving (hT.iterate k)).aestronglyMeasurable
  have hsum : eLpNorm (fun x => ∑ k ∈ range n, f (T^[k] x)) 1 μ ≤ (n : ℝ≥0∞) * eLpNorm f 1 μ := by
    have hle := eLpNorm_sum_le (μ := μ) (p := 1) (f := fun k => fun x => f (T^[k] x))
      (s := range n) (fun k _ => hfm k) (le_refl 1)
    have heq1 : (∑ i ∈ range n, (fun k (x : α) => f (T^[k] x)) i)
        = (fun x => ∑ k ∈ range n, f (T^[k] x)) := by funext x; rw [Finset.sum_apply]
    rw [heq1] at hle
    refine hle.trans ?_
    have hcomp : ∑ k ∈ range n, eLpNorm (fun x => f (T^[k] x)) 1 μ
        = ∑ _k ∈ range n, eLpNorm f 1 μ := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (hT.iterate k)
    rw [hcomp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hAdef : (fun x => birkhoffAverage ℝ T f n x)
      = (n : ℝ)⁻¹ • (fun x => ∑ k ∈ range n, f (T^[k] x)) := by
    funext x; simp [birkhoffAverage, birkhoffSum, Pi.smul_apply]
  rw [hAdef]
  calc eLpNorm ((n : ℝ)⁻¹ • fun x => ∑ k ∈ range n, f (T^[k] x)) 1 μ
      ≤ ‖(n : ℝ)⁻¹‖ₑ * eLpNorm (fun x => ∑ k ∈ range n, f (T^[k] x)) 1 μ := eLpNorm_const_smul_le
    _ ≤ ‖(n : ℝ)⁻¹‖ₑ * ((n : ℝ≥0∞) * eLpNorm f 1 μ) := by gcongr
    _ = eLpNorm f 1 μ := by
        rw [← mul_assoc]
        have h1 : ‖(n : ℝ)⁻¹‖ₑ * (n : ℝ≥0∞) = 1 := by
          rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn),
            ENNReal.ofReal_natCast]
          exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)
        rw [h1, one_mul]




theorem integrable_birkhoffLimit (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    Integrable (birkhoffLimit T f) μ := by
  rw [← memLp_one_iff_integrable]
  refine ⟨(aemeasurable_birkhoffLimit hT hf).aestronglyMeasurable, ?_⟩
  have hbound : eLpNorm (birkhoffLimit T f) 1 μ ≤ eLpNorm f 1 μ :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (C := eLpNorm f 1 μ)
      (Eventually.of_forall fun n => eLpNorm_birkhoffAverage_le hT hf n)
      (fun n => (aestronglyMeasurable_birkhoffAverage hT hf n))
      (tendsto_birkhoffAverage_ae hT hf)
  exact lt_of_le_of_lt hbound (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top



omit [MeasurableSpace α] [IsFiniteMeasure μ] in


theorem birkhoffAverage_sub_birkhoffLimit (n : ℕ) (hn : 1 ≤ n) (x : α) :
    birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x
      = birkhoffAverage ℝ T f n x - birkhoffLimit T f x := by
  have hLinv : (birkhoffLimit T f) ∘ T = birkhoffLimit T f := by
    funext y; exact birkhoffLimit_comp y
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [show (fun y => f y - birkhoffLimit T f y) = f - birkhoffLimit T f from rfl,
    birkhoffAverage_sub, Pi.sub_apply, birkhoffAverage_of_comp_eq ℝ hLinv hn0]
  rfl


theorem tendsto_birkhoffAverage_sub_birkhoffLimit_ae (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x)
      atTop (𝓝 0) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT hf] with x hx
  have heq : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x
        = birkhoffAverage ℝ T f n x - birkhoffLimit T f x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact birkhoffAverage_sub_birkhoffLimit n hn x
  rw [tendsto_congr' heq]
  have := hx.sub (tendsto_const_nhds (x := birkhoffLimit T f x))
  rwa [sub_self] at this


theorem fStar_sub_birkhoffLimit_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, fStar T (fun y => f y - birkhoffLimit T f y) x = 0 := by
  filter_upwards [tendsto_birkhoffAverage_sub_birkhoffLimit_ae hT hf] with x hx
  unfold fStar
  have hxe : Tendsto
      (fun n => ((birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hx
  rw [hxe.limsup_eq]; rfl


theorem fStarLow_sub_birkhoffLimit_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, fStarLow T (fun y => f y - birkhoffLimit T f y) x = 0 := by
  filter_upwards [tendsto_birkhoffAverage_sub_birkhoffLimit_ae hT hf] with x hx
  unfold fStarLow
  have hxe : Tendsto
      (fun n => ((birkhoffAverage ℝ T (fun y => f y - birkhoffLimit T f y) n x : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hx
  rw [hxe.liminf_eq]; rfl

omit [IsFiniteMeasure μ] in

theorem ae_mem_setOf_fStarLow_lt {g : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hg0 : ∀ᵐ x ∂μ, fStarLow T g x = 0) : ∀ᵐ x ∂μ, fStarLow T g x < (c : EReal) := by
  filter_upwards [hg0] with x hx
  rw [hx]; exact_mod_cast hc

omit [IsFiniteMeasure μ] in

theorem ae_mem_setOf_lt_fStar {g : α → ℝ} {c : ℝ} (hc : c < 0)
    (hg0 : ∀ᵐ x ∂μ, fStar T g x = 0) : ∀ᵐ x ∂μ, (c : EReal) < fStar T g x := by
  filter_upwards [hg0] with x hx
  rw [hx]; exact_mod_cast hc






theorem setIntegral_birkhoffLimit (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) {E : Set α}
    (hEmeas : MeasurableSet E) (hEinv : IsInvariantSet T E) :
    ∫ x in E, f x ∂μ = ∫ x in E, birkhoffLimit T f x ∂μ := by
  set L := birkhoffLimit T f with hL
  set h : α → ℝ := fun y => f y - L y with hh
  have hLint : Integrable L μ := integrable_birkhoffLimit hT hf
  have hhint : Integrable h μ := hf.sub hLint
  have hlow0 : ∀ᵐ x ∂μ, fStarLow T h x = 0 := fStarLow_sub_birkhoffLimit_ae hT hf
  have hsup0 : ∀ᵐ x ∂μ, fStar T h x = 0 := fStar_sub_birkhoffLimit_ae hT hf
  have hEmeas₀ : NullMeasurableSet E μ := hEmeas.nullMeasurableSet
  
  suffices hzero : ∫ x in E, h x ∂μ = 0 by
    have hsplit : ∫ x in E, h x ∂μ = (∫ x in E, f x ∂μ) - ∫ x in E, L x ∂μ := by
      rw [hh]; exact integral_sub hf.integrableOn hLint.integrableOn
    rw [hsplit] at hzero; linarith [hzero]
  
  have hupper : ∀ ε : ℝ, 0 < ε → ∫ x in E, h x ∂μ ≤ ε * (μ E).toReal := by
    intro ε hε
    set S := E ∩ {x | fStarLow T h x < (ε : EReal)} with hS
    have hSinv : IsInvariantSet T S := by
      intro x; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, fStarLow_comp, hEinv x]
    have hSmeas : NullMeasurableSet S μ :=
      hEmeas₀.inter (nullMeasurableSet_lt (aemeasurable_fStarLow hT hhint) aemeasurable_const)
    have hSeq : S =ᵐ[μ] E := by
      rw [hS, Filter.eventuallyEq_set]
      filter_upwards [ae_mem_setOf_fStarLow_lt hε hlow0] with x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hx, and_true]
    calc ∫ x in E, h x ∂μ = ∫ x in S, h x ∂μ := (setIntegral_congr_set hSeq).symm
      _ ≤ ε * (μ S).toReal :=
          setIntegral_le_of_fStarLow_lt hT hhint hSmeas hSinv (fun x hx => hx.2)
      _ = ε * (μ E).toReal := by rw [measure_congr hSeq]
  have hlower : ∀ ε : ℝ, 0 < ε → -(ε * (μ E).toReal) ≤ ∫ x in E, h x ∂μ := by
    intro ε hε
    set S := E ∩ {x | ((-ε : ℝ) : EReal) < fStar T h x} with hS
    have hSinv : IsInvariantSet T S := by
      intro x; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq, fStar_comp, hEinv x]
    have hSmeas : NullMeasurableSet S μ :=
      hEmeas₀.inter (nullMeasurableSet_lt aemeasurable_const (aemeasurable_fStar hT hhint))
    have hSeq : S =ᵐ[μ] E := by
      rw [hS, Filter.eventuallyEq_set]
      filter_upwards [ae_mem_setOf_lt_fStar (show (-ε : ℝ) < 0 by linarith) hsup0] with x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hx, and_true]
    calc -(ε * (μ E).toReal) = (-ε) * (μ S).toReal := by rw [measure_congr hSeq]; ring
      _ ≤ ∫ x in S, h x ∂μ :=
          setIntegral_ge_of_lt_fStar hT hhint hSmeas hSinv (fun x hx => hx.2)
      _ = ∫ x in E, h x ∂μ := setIntegral_congr_set hSeq
  
  have hmnn : 0 ≤ (μ E).toReal := ENNReal.toReal_nonneg
  by_contra hne
  set I := ∫ x in E, h x ∂μ with hI
  have habs : 0 < |I| := abs_pos.mpr hne
  
  rcases eq_or_lt_of_le hmnn with hm0 | hmpos
  · 
    have h1 := hupper 1 one_pos
    have h2 := hlower 1 one_pos
    rw [← hm0] at h1 h2; simp at h1 h2; exact hne (le_antisymm h1 h2)
  · 
    set ε := |I| / (2 * (μ E).toReal) with hε
    have hεpos : 0 < ε := by positivity
    have h1 := hupper ε hεpos
    have h2 := hlower ε hεpos
    
    have hcancel : ε * (μ E).toReal = |I| / 2 := by
      rw [hε]; field_simp
    rw [hcancel] at h1 h2
    rcases abs_cases I with ⟨hIabs, _⟩ | ⟨hIabs, _⟩ <;> nlinarith [habs]



omit [IsFiniteMeasure μ] in

theorem measurable_birkhoffAverage (hT : Measurable T) {f₀ : α → ℝ} (hf₀ : Measurable f₀) (n : ℕ) :
    Measurable (fun x => birkhoffAverage ℝ T f₀ n x) := by
  have hbs : Measurable (fun x => birkhoffSum T f₀ n x) := by
    simp only [birkhoffSum]
    exact Finset.measurable_sum _ (fun k _ => hf₀.comp (hT.iterate k))
  simp only [birkhoffAverage, smul_eq_mul]
  exact (measurable_const.mul hbs)

omit [IsFiniteMeasure μ] in

theorem measurable_fStar (hT : Measurable T) {f₀ : α → ℝ} (hf₀ : Measurable f₀) :
    Measurable (fStar T f₀) := by
  unfold fStar
  exact Measurable.limsup (fun n =>
    measurable_coe_real_ereal.comp (measurable_birkhoffAverage hT hf₀ n))

omit [IsFiniteMeasure μ] in


theorem measurable_invariants_birkhoffLimit (hT : Measurable T) {f₀ : α → ℝ} (hf₀ : Measurable f₀) :
    Measurable[MeasurableSpace.invariants T] (birkhoffLimit T f₀) := by
  have hcomp : (fStar T f₀) ∘ T = fStar T f₀ := by funext x; exact fStar_comp x
  have hfStar_inv : Measurable[MeasurableSpace.invariants T] (fStar T f₀) := by
    rw [MeasurableSpace.measurable_invariants_dom]
    refine ⟨measurable_fStar hT hf₀, fun s _ => ?_⟩
    rw [hcomp]
  exact measurable_ereal_toReal.comp hfStar_inv






theorem birkhoffLimit_ae_eq_condExp (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    birkhoffLimit T f =ᵐ[μ] μ[f | MeasurableSpace.invariants T] := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace α› := MeasurableSpace.invariants_le T
  
  have hsf : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  
  set f₀ : α → ℝ := hf.1.mk f with hf₀_def
  have hf₀_meas : Measurable f₀ := hf.1.stronglyMeasurable_mk.measurable
  have hff₀ : f =ᵐ[μ] f₀ := hf.1.ae_eq_mk
  have hf₀_int : Integrable f₀ μ := hf.congr hff₀
  
  have hqmp : Measure.QuasiMeasurePreserving T μ μ := hT.quasiMeasurePreserving
  have hLeq : birkhoffLimit T f =ᵐ[μ] birkhoffLimit T f₀ := by
    have hAeq : ∀ᵐ x ∂μ, ∀ n, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T f₀ n x := by
      rw [ae_all_iff]
      exact fun n => Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hqmp hff₀ n
    filter_upwards [hAeq] with x hx
    unfold birkhoffLimit fStar
    congr 1
    exact limsup_congr (Eventually.of_forall fun n => by rw [hx n])
  
  have hgm : AEStronglyMeasurable[MeasurableSpace.invariants T] (birkhoffLimit T f) μ :=
    AEStronglyMeasurable.congr
      (measurable_invariants_birkhoffLimit hT.measurable hf₀_meas).stronglyMeasurable.aestronglyMeasurable
      hLeq.symm
  
  have hgeq : ∀ s : Set α, MeasurableSet[MeasurableSpace.invariants T] s → μ s < ∞ →
      ∫ x in s, birkhoffLimit T f x ∂μ = ∫ x in s, f x ∂μ := by
    intro s hs _
    obtain ⟨hs_meas, hs_inv⟩ := (MeasurableSpace.measurableSet_invariants).mp hs
    have hs_invset : IsInvariantSet T s := fun x => by
      constructor
      · intro hx; rw [← hs_inv] at hx; exact hx
      · intro hx; rw [← hs_inv]; exact hx
    exact (setIntegral_birkhoffLimit hT hf hs_meas hs_invset).symm
  
  exact ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun s _ _ => (integrable_birkhoffLimit hT hf).integrableOn)
    (fun s hs hμs => hgeq s hs hμs) hgm





theorem tendsto_birkhoffAverage_condExp_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop
      (𝓝 ((μ[f | MeasurableSpace.invariants T]) x)) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT hf, birkhoffLimit_ae_eq_condExp hT hf]
    with x hx hxeq
  rwa [hxeq] at hx

end BirkhoffAE

end StatMech
