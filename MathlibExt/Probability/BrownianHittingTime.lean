/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MathlibExt.Probability.BrownianOscillation
import MathlibExt.Probability.Distributions.GaussianCdf
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Law of the Brownian hitting time of a positive level

The probability of hitting a positive level by time `t` is twice the upper Gaussian tail at
that level. Integrating the derivative of this tail gives `IsBrownianReal.measure_hitting_le`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MathlibExt.Probability.BrownianStrongMarkovWanted.IsBrownianReal

section

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}

private def hit (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (u : ℝ≥0) : Set Ω :=
  {ω | ∃ s ≤ u, B s ω = a}

private lemma hit_mono (B : ℝ≥0 → Ω → ℝ) (a : ℝ) : Monotone (hit B a) :=
  fun _ _ huv _ ⟨s, hs, he⟩ ↦ ⟨s, hs.trans huv, he⟩

-- On a compact interval the range of a continuous path is the closure of its values
-- on a countable dense set. This also gives measurability in the past at time `u`.
private lemma measurableSet_hit [MeasurableSpace Ω] (a : ℝ) (u : ℝ≥0)
    (hm : ∀ s ≤ u, Measurable (B s)) (hc : ∀ ω, Continuous fun s ↦ B s ω) :
    MeasurableSet (hit B a u) := by
  let K := Icc (0 : ℝ≥0) u
  have : Nonempty K := ⟨⟨0, le_rfl, zero_le⟩⟩
  let d := TopologicalSpace.denseSeq K
  have hd := TopologicalSpace.denseRange_denseSeq K
  have key (ω : Ω) : ω ∈ hit B a u ↔
      ∀ n : ℕ, ∃ k : ℕ, dist a (B (d k) ω) < 1 / ((n : ℝ) + 1) := by
    let f : K → ℝ := fun s ↦ B s ω
    have hf : Continuous f := (hc ω).comp continuous_subtype_val
    have hr : ω ∈ hit B a u ↔ a ∈ range f :=
      ⟨fun ⟨s, hs, he⟩ ↦ ⟨⟨s, zero_le, hs⟩, he⟩, fun ⟨s, he⟩ ↦ ⟨s, s.2.2, he⟩⟩
    rw [hr, ← Metric.mem_closure_range_iff_nat]
    change a ∈ range f ↔ a ∈ closure (range (f ∘ d))
    rw [range_comp]
    exact ⟨fun h ↦ hf.range_subset_closure_image_dense hd h,
      fun h ↦ closure_minimal (image_subset_range _ _) (isCompact_range hf).isClosed h⟩
  rw [show hit B a u = {ω | ∀ n : ℕ, ∃ k : ℕ, dist a (B (d k) ω) < 1 / ((n : ℝ) + 1)}
    from Set.ext key]
  simp only [ofPred_forall, ofPred_exists]
  exact .iInter fun n ↦ .iUnion fun k ↦
    measurableSet_lt (measurable_const.dist (hm _ (d k).2.2)) measurable_const

private abbrev past (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (s : Iic u) ↦ B s ω) inferInstance

private lemma hit_in_past (a : ℝ) {u v : ℝ≥0} (huv : u ≤ v)
    (hc : ∀ ω, Continuous fun s ↦ B s ω) : MeasurableSet[past B v] (hit B a u) := by
  refine @measurableSet_hit Ω B (past B v) a u ?_ hc
  intro s hs
  have he : Measurable (fun f : Iic v → ℝ ↦ f ⟨s, hs.trans huv⟩) := measurable_pi_apply _
  exact he.comp (Measurable.of_comap_le le_rfl)

variable [MeasurableSpace Ω] {P : Measure Ω}

private lemma measure_pos_increment (hB : IsPreBrownianReal B P) {v w : ℝ≥0} (hvw : v < w)
    {D : Set Ω} (hD : MeasurableSet[past B v] D) :
    P (D ∩ {ω | B v ω < B w ω}) = P D * (1 / 2) := by
  obtain ⟨S, hS, rfl⟩ := hD
  have hi := (hB.indepFun_shift v).symm.measure_inter_preimage_eq_mul S
    {f : ℝ≥0 → ℝ | 0 < f (w - v)} hS ((measurable_pi_apply _) measurableSet_Ioi)
  change P (_ ∩ {ω | 0 < B (v + (w - v)) ω - B v ω}) =
    _ * P {ω | 0 < B (v + (w - v)) ω - B v ω} at hi
  rw [add_tsub_cancel_of_le hvw.le] at hi
  have h := (hB.hasLaw_sub w v).measure_eq (p := fun x : ℝ ↦ 0 < x) measurableSet_Ioi
  have hne : nndist (w : ℝ) (v : ℝ) ≠ 0 := by
    simpa only [ne_eq, nndist_eq_zero, NNReal.coe_inj] using hvw.ne'
  change P {ω | 0 < B w ω - B v ω} = gaussianReal 0 _ (Ioi 0) at h
  have hhalf := h.trans (gaussianReal_Ioi_zero hne)
  simpa only [sub_pos] using hi.trans (congrArg (_ * ·) hhalf)

-- The first grid endpoint by which the level has been hit.
private def cell (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (v : ℕ → ℝ≥0) :=
  disjointed (fun k ↦ hit B a (v k))

omit [MeasurableSpace Ω] in
private lemma union_cell (a : ℝ) {v : ℕ → ℝ≥0} (hv : Monotone v) (N : ℕ) :
    (⋃ k ∈ Finset.range (N + 1), cell B a v k) = hit B a (v N) := by
  rw [cell, biUnion_range_succ_disjointed]
  exact congrFun ((hit_mono B a).comp hv).partialSups_eq N

omit [MeasurableSpace Ω] in
private lemma measurableSet_cell {m : MeasurableSpace Ω} (a : ℝ) (v : ℕ → ℝ≥0) (k : ℕ)
    (hm : ∀ j ≤ k, MeasurableSet[m] (hit B a (v j))) : MeasurableSet[m] (cell B a v k) := by
  rw [cell, disjointed_eq_inter_compl]
  exact (hm k le_rfl).inter (.iInter fun j ↦ .iInter fun hj ↦ (hm j hj.le).compl)

private def sampled (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (v : ℕ → ℝ≥0) (N : ℕ) (w : ℝ≥0) :=
  ⋃ k ∈ Finset.range (N + 1), cell B a v k ∩ {ω | B (v k) ω < B w ω}

private lemma measurableSet_sampled (hm : ∀ s, Measurable (B s))
    (hc : ∀ ω, Continuous fun s ↦ B s ω) (a : ℝ) (v : ℕ → ℝ≥0) (N : ℕ) (w : ℝ≥0) :
    MeasurableSet (sampled B a v N w) :=
  .iUnion fun k ↦ .iUnion fun _ ↦
    (measurableSet_cell a v k fun j _ ↦ measurableSet_hit a (v j) (fun s _ ↦ hm s) hc).inter
      (measurableSet_lt (hm _) (hm _))

private lemma measure_sampled (hB : IsPreBrownianReal B P) (hm : ∀ s, Measurable (B s))
    (hc : ∀ ω, Continuous fun s ↦ B s ω) (a : ℝ) {v : ℕ → ℝ≥0} (hv : Monotone v)
    (N : ℕ) {w : ℝ≥0} (hw : v N < w) : P (sampled B a v N w) = P (hit B a (v N)) * (1 / 2) := by
  have hD : Pairwise (fun i j ↦ Disjoint (cell B a v i) (cell B a v j)) :=
    disjoint_disjointed (fun k ↦ hit B a (v k))
  have mD k := measurableSet_cell a v k fun j _ ↦ measurableSet_hit a (v j) (fun s _ ↦ hm s) hc
  rw [sampled, measure_biUnion_finset, ← union_cell a hv N,
    measure_biUnion_finset (hD.set_pairwise _) (fun k _ ↦ mD k), Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro k hk
    refine measure_pos_increment hB ((hv (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans_lt hw)
      (measurableSet_cell a v k fun j hj ↦ hit_in_past a (hv hj) hc)
  · exact fun i _ j _ hij ↦ (hD hij).mono inter_subset_left inter_subset_left
  · exact fun k _ ↦ (mD k).inter (measurableSet_lt (hm _) (hm _))

-- Round the first actual hit up to a grid point. The increment to a time just beyond
-- the grid is positive on exactly half of every cell, including the last one.
private lemma half_hit (hB : IsPreBrownianReal B P) (hm : ∀ s, Measurable (B s))
    (hc : ∀ ω, Continuous fun s ↦ B s ω) {a : ℝ} (ha : 0 < a) {t : ℝ≥0} (ht : 0 < t) :
    P (hit B a t) * (1 / 2) = P {ω | a < B t ω} := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval t).isProbabilityMeasure
  let d (n : ℕ) := t / (n + 1 : ℝ≥0)
  let v (n k : ℕ) : ℝ≥0 := k * d n
  have mono_v (n : ℕ) : Monotone (v n) := fun _ _ hij ↦
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) zero_le
  have v_end n : v n (n + 1) = t := by simp [v, d, field]
  have hd n : 0 < d n := div_pos ht (by positivity)
  have hdlim : Tendsto d atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    simpa [d, div_eq_mul_inv] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (t : ℝ)
  let A n := sampled B a (v n) (n + 1) (t + d n)
  have hmass n : P (A n) = P (hit B a t) * (1 / 2) := by
    have hw : v n (n + 1) < t + d n := by simp [v_end, hd]
    simpa [A, v_end] using measure_sampled hB hm hc a (mono_v n) (n + 1) hw
  have hne : ∀ᵐ ω ∂P, B t ω ≠ a := by
    have := nullSingletonClass_gaussianReal (μ := 0) ht.ne'
    rw [ae_iff]
    simpa using (hB.hasLaw_eval t).measure_eq (p := fun x ↦ x = a) (measurableSet_singleton a)
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n ↔ a < B t ω := by
    filter_upwards [hB.eval_zero_ae_eq_zero, hne] with ω h0 hne
    have hu n := union_cell (B := B) a (mono_v n) (n + 1)
    simp only [v_end] at hu
    by_cases hh : ω ∈ hit B a t
    · obtain ⟨s, hs, he⟩ := hh
      have hK := isCompact_Icc (α := ℝ≥0) (a := 0) (b := t) |>.inter_right
        (isClosed_eq (hc ω) (continuous_const (y := a)))
      obtain ⟨τ, hτ⟩ := hK.exists_isLeast ⟨s, ⟨zero_le, hs⟩, he⟩
      have hcell n : ∃ k < n + 2, ω ∈ cell B a (v n) k := by
        have hmem : ω ∈ ⋃ k ∈ Finset.range (n + 1 + 1), cell B a (v n) k :=
          (hu n).symm ▸ (show ω ∈ hit B a t from ⟨s, hs, he⟩)
        simpa only [mem_iUnion, exists_prop, Finset.mem_range] using hmem
      choose k hk hmem using hcell
      have htime : Tendsto (fun n ↦ v n (k n)) atTop (𝓝 τ) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (show Tendsto (fun n ↦ τ + d n) atTop (𝓝 τ) by
            simpa using tendsto_const_nhds.add hdlim) (fun n ↦ ?_) (fun n ↦ ?_)
        · obtain ⟨r, hr, her⟩ := disjointed_subset _ _ (hmem n)
          exact (hτ.2 ⟨⟨zero_le, hr.trans ((mono_v n (Nat.le_of_lt_succ (hk n))).trans
            (v_end n).le)⟩, her⟩).trans hr
        · cases hkn : k n with
          | zero => simp [v]
          | succ j =>
            have hprev : ω ∉ hit B a (v n j) := by
              have h := hmem n
              rw [cell, hkn, disjointed_eq_inter_compl] at h
              exact mem_iInter₂.mp h.2 j (Nat.lt_succ_self j)
            have hlt : v n j < τ := lt_of_not_ge fun h ↦ hprev ⟨τ, h, hτ.1.2⟩
            simpa [v, Nat.cast_succ, add_mul] using add_le_add_right hlt.le (d n)
      have hleft : Tendsto (fun n ↦ B (v n (k n)) ω) atTop (𝓝 a) :=
        hτ.1.2 ▸ ((hc ω).tendsto τ).comp htime
      have hright : Tendsto (fun n ↦ B (t + d n) ω) atTop (𝓝 (B t ω)) :=
        ((hc ω).tendsto t).comp (by simpa using tendsto_const_nhds.add hdlim)
      have hiff n : ω ∈ A n ↔ B (v n (k n)) ω < B (t + d n) ω := by
        change (ω ∈ ⋃ j ∈ Finset.range _, cell B a (v n) j ∩ _) ↔ _
        simp only [mem_iUnion, exists_prop, Finset.mem_range, mem_inter_iff, mem_ofPred_eq]
        refine ⟨fun ⟨j, _, hj, hp⟩ ↦ ?_, fun hp ↦ ⟨k n, hk n, hmem n, hp⟩⟩
        have : j = k n := by
          by_contra h
          exact Set.disjoint_left.mp (disjoint_disjointed _ h) hj (hmem n)
        simpa [this] using hp
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · filter_upwards [hright.eventually_lt hleft hlt] with n hn
        simp [hiff, hlt.not_gt, hn.not_gt]
      · filter_upwards [hleft.eventually_lt hright hgt] with n hn
        simp [hiff, hgt, hn]
    · have hle : B t ω ≤ a := le_of_not_gt fun hgt ↦ hh (by
        obtain ⟨r, hr, he⟩ := intermediate_value_Icc (a := 0) (b := t) zero_le
          (hc ω).continuousOn (show a ∈ Icc (B 0 ω) (B t ω) from ⟨h0 ▸ ha.le, hgt.le⟩)
        exact ⟨r, hr.2, he⟩)
      refine Eventually.of_forall fun n ↦ ⟨fun hn ↦ ?_, fun h ↦ (hle.not_gt h).elim⟩
      apply False.elim ∘ hh
      rw [← hu n]
      exact iUnion₂_mono (fun k _ ↦ inter_subset_left) hn
  have hconv := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_lt measurable_const (hm t)) (fun n ↦ measurableSet_sampled hm hc _ _ _ _) hlim
  change Tendsto (fun n ↦ P (A n)) atTop _ at hconv
  simp only [hmass] at hconv
  exact tendsto_nhds_unique tendsto_const_nhds hconv

end

-- Extend the Gaussian tail continuously at zero before applying the fundamental theorem
-- of calculus. Positivity of its derivative then supplies integrability at that endpoint.
private lemma integral_density {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t,
        a / Real.sqrt (2 * Real.pi * s ^ 3) * Real.exp (-a ^ 2 / (2 * s))) =
      2 * (1 - cdf (gaussianReal 0 1) (a / Real.sqrt t)) := by
  let F (s : ℝ) := 2 * (1 - cdf (gaussianReal 0 1) (a / Real.sqrt s))
  let f (s : ℝ) := a / Real.sqrt (2 * Real.pi * s ^ 3) * Real.exp (-a ^ 2 / (2 * s))
  have hder (s : ℝ) (hs : 0 < s) : HasDerivAt F (f s) s := by
    have hr := Real.sqrt_pos.mpr hs
    have hs2 := Real.sq_sqrt hs.le
    have hg := (hasDerivAt_const s a).div (Real.hasDerivAt_sqrt hs.ne') hr.ne'
    have h := ((hasDerivAt_const s 1).sub ((hasDerivAt_stdNormal_cdf _).comp s hg)).const_mul 2
    convert h using 1
    · rfl
    have hroot : Real.sqrt (2 * Real.pi * s ^ 3) =
        Real.sqrt (2 * Real.pi) * Real.sqrt s ^ 3 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      rw [mul_pow, ← pow_mul, mul_comm 3 2, pow_mul, hs2, Real.sq_sqrt (by positivity)]
    dsimp [f, gaussianPDFReal, Pi.div_apply]
    rw [hroot]
    simp only [mul_one, sub_zero, zero_mul, zero_sub, div_pow, hs2]
    have hexp : -(a ^ 2 / s) / 2 = -a ^ 2 / (2 * s) := by ring
    rw [hexp]
    field_simp
    nlinarith [hs2]
  have hzero : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using (Real.continuous_sqrt.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
      · filter_upwards [self_mem_nhdsWithin] with s hs using Real.sqrt_pos.mpr hs
    have hg := hs.inv_tendsto_nhdsGT_zero.const_mul_atTop ha
    have h := (tendsto_cdf_atTop (gaussianReal 0 1)).comp hg
    simpa [F, div_eq_mul_inv, Function.comp_def] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub h).const_mul (2 : ℝ)
  let G := Function.update F 0 0
  have hcont : ContinuousOn G (Icc 0 t) := by
    change ContinuousOn (Function.update F 0 0) _
    rw [continuousOn_update_iff, Icc_sdiff_left]
    exact ⟨fun s hs ↦ (hder s hs.1).continuousAt.continuousWithinAt,
      fun _ ↦ hzero.mono_left (nhdsWithin_mono _ Ioc_subset_Ioi_self)⟩
  have hderG (s : ℝ) (hs : s ∈ Ioo 0 t) : HasDerivAt G (f s) s := by
    apply (hder s hs.1).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs.1] with x hx using Function.update_of_ne (ne_of_gt hx) _ _
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont hderG
    (fun s hs ↦ show 0 ≤ f s by dsimp [f]; positivity)
  simpa [G, F, Function.update_of_ne ht.ne'] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le hcont hderG
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2 hint)

/-- **Law of the hitting time of a level.** For a Brownian motion `B` with continuous paths and
`a > 0`, the hitting time `T_a = inf {t ≥ 0 : B t = a}` has the density
`a / √(2π s³) · exp(-a² / (2s))` on `(0, ∞)`; equivalently, since `T_a ≤ t` exactly when the
path reaches `a` on `[0, t]`, `P(T_a ≤ t) = ∫_0^t a / √(2π s³) · exp(-a² / (2s)) ds` for every
`t ≥ 0` (Le Gall, ENS notes *Intégration, Probabilités et Processus Aléatoires*,
Corollaire 14.5.3). -/
theorem measure_hitting_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) {a : ℝ} (ha : 0 < a) (t : ℝ≥0) :
    P {ω | ∃ s ∈ Set.Icc (0 : ℝ≥0) t, B s ω = a} =
      ENNReal.ofReal (∫ s in (0 : ℝ)..t,
        a / Real.sqrt (2 * Real.pi * s ^ 3) * Real.exp (-a ^ 2 / (2 * s))) := by
  have hevent : {ω | ∃ s ∈ Icc (0 : ℝ≥0) t, B s ω = a} = hit B a t := by
    ext ω
    simp [hit]
  rw [hevent]
  obtain rfl | ht := eq_zero_or_pos t
  · simp only [NNReal.coe_zero, intervalIntegral.integral_same, ENNReal.ofReal_zero]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
    simpa [hit, h0] using ha.ne
  -- Brownian coordinates are measurable on the completion, with the same finite-dimensional laws.
  have hBc : IsPreBrownianReal (Ω := NullMeasurableSpace Ω P) B P.completion := by
    constructor
    intro I
    have hl := hB.hasLaw I
    have hm := hl.aemeasurable.nullMeasurable.measurable'
    refine ⟨hm.aemeasurable, Measure.ext fun S hS ↦ ?_⟩
    exact (Measure.map_apply (μ := P.completion) hm hS).trans
      (hl.measure_eq (p := (· ∈ S)) hS)
  have hhalf : P (hit B a t) * (1 / 2) = P {ω | a < B t ω} :=
    half_hit hBc (fun s ↦ (hB.aemeasurable s).nullMeasurable.measurable') hcont ha ht
  have htail := (hB.hasLaw_eval t).measureReal_eq (p := fun x ↦ a < x) measurableSet_Ioi
  change P.real {ω | a < B t ω} = (gaussianReal 0 t).real (Ioi a) at htail
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_gaussianReal_eq_std 0 a ht.ne', sub_zero] at htail
  have : IsProbabilityMeasure P := (hB.hasLaw_eval t).isProbabilityMeasure
  rw [integral_density ha (NNReal.coe_pos.mpr ht), ← ofReal_measureReal (μ := P)]
  apply congrArg ENNReal.ofReal
  have hr := congrArg ENNReal.toReal hhalf
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  change P.real (hit B a t) * (1 / 2) = P.real {ω | a < B t ω} at hr
  linarith

end MathlibExt.Probability.BrownianStrongMarkovWanted.IsBrownianReal
