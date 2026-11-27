/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ExponentialMoments
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Long-run uptime of alternating renewal cycles -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Reliability.AlternatingRenewal

/-- The time at which the first `n` full up/down cycles have ended. -/
def cycleEnd (U D : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (U i + D i)

/-- The sum of the lengths of the up intervals clipped at time `t`, taken as `0` if the
series is not summable. If the up and down durations are nonnegative and the cycle ends
tend to infinity, only finitely many terms contribute at each `t`, and the sum equals
elapsed uptime in `[0, t)`. -/
noncomputable def upTime (U D : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' i, max (min t (cycleEnd U D i + U i) - cycleEnd U D i) 0

private theorem cycleEnd_succ (U D : ℕ → ℝ) (n : ℕ) :
    cycleEnd U D (n + 1) = cycleEnd U D n + (U n + D n) :=
  Finset.sum_range_succ _ _

private theorem cycleEnd_mono {U D : ℕ → ℝ} (hU : ∀ i, 0 ≤ U i) (hD : ∀ i, 0 ≤ D i) :
    Monotone (cycleEnd U D) :=
  monotone_nat_of_le_succ fun n => by
    rw [cycleEnd_succ]
    exact le_add_of_nonneg_right (add_nonneg (hU n) (hD n))

private theorem cycleEnd_nonneg {U D : ℕ → ℝ} (hU : ∀ i, 0 ≤ U i) (hD : ∀ i, 0 ≤ D i)
    (n : ℕ) : 0 ≤ cycleEnd U D n :=
  Finset.sum_nonneg fun i _ => add_nonneg (hU i) (hD i)

private theorem upTime_eq_sum {U D : ℕ → ℝ} (hU : ∀ i, 0 ≤ U i) (hD : ∀ i, 0 ≤ D i)
    {n : ℕ} {t : ℝ} (ht : t ≤ cycleEnd U D n) :
    upTime U D t = ∑ i ∈ Finset.range n,
      max (min t (cycleEnd U D i + U i) - cycleEnd U D i) 0 := by
  unfold upTime
  apply tsum_eq_sum
  intro i hi
  have hni : n ≤ i := Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h))
  exact max_eq_right (sub_nonpos.mpr ((min_le_left _ _).trans
    (ht.trans (cycleEnd_mono hU hD hni))))

/-- For nonnegative up and down durations whose cycle ends tend to infinity, the clipped
sum equals the Lebesgue length of the union of the up intervals intersected with `[0, t)`.
Zero-length intervals contribute no length, and coincident endpoints do not cause overlap. -/
theorem upTime_eq_volume {U D : ℕ → ℝ} (hU : ∀ i, 0 ≤ U i) (hD : ∀ i, 0 ≤ D i)
    (hT : Tendsto (cycleEnd U D) atTop atTop) (t : ℝ) :
    upTime U D t = volume.real (Ico 0 t ∩ ⋃ i, Ico (cycleEnd U D i) (cycleEnd U D i + U i)) := by
  obtain ⟨n, hn⟩ := (hT.eventually (eventually_ge_atTop t)).exists
  let I := fun i => Ico (cycleEnd U D i) (min t (cycleEnd U D i + U i))
  have hset : Ico 0 t ∩ (⋃ i, Ico (cycleEnd U D i) (cycleEnd U D i + U i)) =
      ⋃ i ∈ Finset.range n, I i := by
    ext x
    simp only [mem_inter_iff, mem_iUnion, mem_Ico, Finset.mem_range, I, lt_min_iff]
    constructor
    · rintro ⟨⟨_, hxt⟩, i, hix, hxu⟩
      refine ⟨i, ?_, hix, hxt, hxu⟩
      by_contra! hin
      exact (not_lt_of_ge (hn.trans ((cycleEnd_mono hU hD hin).trans hix))) hxt
    · rintro ⟨i, _, hix, hxt, hxu⟩
      exact ⟨⟨(cycleEnd_nonneg hU hD i).trans hix, hxt⟩, i, hix, hxu⟩
  have hdis : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint I := by
    intro i _ j _ hij
    have hbefore (k l : ℕ) (hkl : k < l) : Disjoint (I k) (I l) := by
      apply Set.disjoint_left.mpr
      intro x hxk hxl
      have hc : cycleEnd U D k + U k ≤ cycleEnd U D l := by
        refine le_trans ?_ (cycleEnd_mono hU hD (Nat.succ_le_of_lt hkl))
        rw [cycleEnd_succ]
        linarith [hD k]
      exact (not_lt_of_ge (hc.trans hxl.1)) (hxk.2.trans_le (min_le_right _ _))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hbefore i j hlt
    · exact (hbefore j i hgt).symm
  rw [hset, measureReal_biUnion_finset hdis (fun _ _ => measurableSet_Ico)
    (fun i _ => measure_ne_top_of_subset (by intro x hx; exact ⟨
      (cycleEnd_nonneg hU hD i).trans hx.1, hx.2.trans_le (min_le_left _ _)⟩)
      (Real.volume_Ico ▸ ENNReal.ofReal_ne_top : volume (Ico 0 t) ≠ ∞)), upTime_eq_sum hU hD hn]
  simp only [I, Real.volume_real_Ico]

private theorem upTime_bounds {U D : ℕ → ℝ} (hU : ∀ i, 0 ≤ U i) (hD : ∀ i, 0 ≤ D i)
    {n : ℕ} {t : ℝ} (hlo : cycleEnd U D n ≤ t) (hhi : t ≤ cycleEnd U D (n + 1)) :
    (∑ i ∈ Finset.range n, U i) ≤ upTime U D t ∧
      upTime U D t ≤ ∑ i ∈ Finset.range (n + 1), U i := by
  rw [upTime_eq_sum hU hD hhi]
  constructor
  · rw [Finset.sum_range_succ]
    refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) (le_max_right _ _)
    have hle : cycleEnd U D i + U i ≤ t := by
      apply le_trans _ ((cycleEnd_mono hU hD (Finset.mem_range.mp hi)).trans hlo)
      rw [cycleEnd_succ]
      linarith [hD i]
    rw [min_eq_right hle, add_sub_cancel_left, max_eq_left (hU i)]
  · apply Finset.sum_le_sum
    intro i _
    refine max_le ?_ (hU i)
    linarith [min_le_right t (cycleEnd U D i + U i)]

private noncomputable def completed (T : ℕ → ℝ) (t : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, t < T n then Nat.find h - 1 else 0

private theorem completed_bounds {T : ℕ → ℝ} (h0 : T 0 = 0)
    (hT : Tendsto T atTop atTop) {t : ℝ} (ht : 0 ≤ t) :
    T (completed T t) ≤ t ∧ t < T (completed T t + 1) := by
  classical
  have h : ∃ n, t < T n := (hT.eventually (eventually_gt_atTop t)).exists
  have hn : Nat.find h ≠ 0 := by
    intro he
    have := Nat.find_spec h
    rw [he, h0] at this
    exact (not_lt_of_ge ht) this
  have hs : Nat.find h - 1 + 1 = Nat.find h := by omega
  unfold completed
  rw [dite_eq_left h]
  exact ⟨le_of_not_gt (Nat.find_min h (by omega)), hs ▸ Nat.find_spec h⟩

private theorem completed_tendsto {T : ℕ → ℝ} (h0 : T 0 = 0) (hm : Monotone T)
    (hT : Tendsto T atTop atTop) : Tendsto (completed T) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun n => ⟨max 0 (T n), ?_⟩
  intro t ht
  have hb := (completed_bounds h0 hT ((le_max_left _ _).trans ht)).2
  by_contra! h
  exact (not_lt_of_ge ((hm h).trans ((le_max_right _ _).trans ht))) hb

private theorem tendsto_average_succ {f : ℕ → ℝ} {m : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => f (n + 1) / (n : ℝ)) atTop (𝓝 m) := by
  have hfactor : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (hf.comp (tendsto_add_atTop_nat 1)).mul hfactor
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hp : 0 < (n : ℝ) := by exact_mod_cast hn
  change f (n + 1) / ((n + 1 : ℕ) : ℝ) * (1 + 1 / (n : ℝ)) = _
  push_cast
  field_simp [hp.ne', show (n : ℝ) + 1 ≠ 0 by positivity]

/-- For nonnegative up and down durations, suppose the average up duration tends to `mu`
and the average full cycle duration tends to `mc > 0`. Then the elapsed uptime fraction
`upTime U D t / t` tends to `mu / mc` as `t` tends to infinity. -/
theorem tendsto_upTime_div {U D : ℕ → ℝ} (hU : ∀ i, 0 ≤ U i) (hD : ∀ i, 0 ≤ D i)
    {mu mc : ℝ} (hmc : 0 < mc)
    (havgU : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, U i) / n) atTop (𝓝 mu))
    (havgC : Tendsto (fun n : ℕ => cycleEnd U D n / n) atTop (𝓝 mc)) :
    Tendsto (fun t : ℝ => upTime U D t / t) atTop (𝓝 (mu / mc)) := by
  let T := cycleEnd U D
  let R := fun n => ∑ i ∈ Finset.range n, U i
  have hT : Tendsto T atTop atTop := by
    apply (tendsto_natCast_atTop_atTop.atTop_mul_pos hmc havgC).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hp : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change (n : ℝ) * (T n / (n : ℝ)) = T n
    field_simp
  have h0 : T 0 = 0 := Finset.sum_empty
  let N := completed T
  have hN : Tendsto N atTop atTop := completed_tendsto h0 (cycleEnd_mono hU hD) hT
  have hlow : Tendsto (fun t => R (N t) / T (N t + 1)) atTop (𝓝 (mu / mc)) := by
    have h := (havgU.div (tendsto_average_succ havgC) hmc.ne').comp hN
    apply h.congr'
    filter_upwards [hN.eventually (eventually_gt_atTop (0 : ℕ))] with t ht
    have hn : (N t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    change (R (N t) / (N t : ℝ)) / (T (N t + 1) / (N t : ℝ)) = _
    by_cases hh : T (N t + 1) = 0
    · simp [hh]
    · field_simp
  have hhigh : Tendsto (fun t => R (N t + 1) / T (N t)) atTop (𝓝 (mu / mc)) := by
    have h := ((tendsto_average_succ havgU).div havgC hmc.ne').comp hN
    apply h.congr'
    filter_upwards [hN.eventually (eventually_gt_atTop (0 : ℕ))] with t ht
    have hn : (N t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    change (R (N t + 1) / (N t : ℝ)) / (T (N t) / (N t : ℝ)) = _
    by_cases hh : T (N t) = 0
    · simp [hh]
    · field_simp
  have hposT : ∀ᶠ t : ℝ in atTop, 0 < T (N t) :=
    (hT.comp hN).eventually (eventually_gt_atTop 0)
  have hb : ∀ᶠ t : ℝ in atTop, R (N t) / T (N t + 1) ≤ upTime U D t / t ∧
      upTime U D t / t ≤ R (N t + 1) / T (N t) := by
    filter_upwards [hposT, eventually_gt_atTop (0 : ℝ)] with t hp ht
    have h := completed_bounds h0 hT ht.le
    have hb := upTime_bounds hU hD h.1 h.2.le
    have hr (n : ℕ) : 0 ≤ R n := Finset.sum_nonneg fun i _ => hU i
    refine ⟨?_, ?_⟩
    · exact (div_le_div_of_nonneg_left (hr _) ht h.2.le).trans
        (div_le_div_of_nonneg_right hb.1 ht.le)
    · exact (div_le_div_of_nonneg_right hb.2 ht.le).trans
        (div_le_div_of_nonneg_left (hr _) hp h.1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- **Alternating renewal uptime.** For i.i.d. nonnegative up/down pairs with finite means and
positive mean cycle length, the fraction of elapsed time spent up tends almost surely to the
mean up-duration divided by the mean cycle duration. The two durations within a pair need
not be independent. This is the uptime case of Sigman's *Renewal theory, inspection paradox
and renewal reward theorem*, §2, Theorem 2.1. -/
theorem ae_tendsto_upTime_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (U D : ℕ → Ω → ℝ)
    (hind : iIndepFun (fun n ω => (U n ω, D n ω)) P)
    (hident : ∀ n, IdentDistrib (fun ω => (U n ω, D n ω)) (fun ω => (U 0 ω, D 0 ω)) P P)
    (hU : ∀ n, ∀ᵐ ω ∂P, 0 ≤ U n ω) (hD : ∀ n, ∀ᵐ ω ∂P, 0 ≤ D n ω)
    (hiU : Integrable (U 0) P) (hiD : Integrable (D 0) P)
    (hc : 0 < (∫ ω, U 0 ω ∂P) + (∫ ω, D 0 ω ∂P)) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => upTime (fun n => U n ω) (fun n => D n ω) t / t)
      atTop (𝓝 ((∫ ω, U 0 ω ∂P) / ((∫ ω, U 0 ω ∂P) + (∫ ω, D 0 ω ∂P)))) := by
  have hpair : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hu := strong_law_ae_real U hiU (fun _ _ h =>
    (hind.indepFun h).comp measurable_fst measurable_fst) (fun n => (hident n).comp measurable_fst)
  have hc' := strong_law_ae_real (fun n ω => U n ω + D n ω) (hiU.add hiD)
    (fun _ _ h => (hind.indepFun h).comp hpair hpair) (fun n => (hident n).comp hpair)
  rw [← ae_all_iff] at hU hD
  filter_upwards [hU, hD, hu, hc'] with ω hUω hDω huω hcω
  rw [integral_add hiU hiD] at hcω
  exact tendsto_upTime_div hUω hDω hc huω hcω

private theorem ae_nonneg_of_hasLaw_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {r : ℝ} (hX : HasLaw X (expMeasure r) P) : ∀ᵐ ω ∂P, 0 ≤ X ω :=
  (hX.ae_iff (measurableSet_setOfPred.mp measurableSet_Ici)).mpr (ae_nonneg_gammaMeasure 1 r)

/-- Let the cycles be independent and identically distributed, with up durations exponential
at failure rate `λ > 0` and down durations exponential at repair rate `μ > 0`. The up and
down durations within a cycle may be dependent. As `t` tends to infinity, the uptime fraction
tends almost surely to `μ / (λ + μ)`. -/
theorem ae_tendsto_upTime_div_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (U D : ℕ → Ω → ℝ) {fail repair : ℝ}
    (hfail : 0 < fail) (hrepair : 0 < repair)
    (hind : iIndepFun (fun n ω => (U n ω, D n ω)) P)
    (hident : ∀ n, IdentDistrib (fun ω => (U n ω, D n ω)) (fun ω => (U 0 ω, D 0 ω)) P P)
    (hu : HasLaw (U 0) (expMeasure fail) P) (hd : HasLaw (D 0) (expMeasure repair) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => upTime (fun n => U n ω) (fun n => D n ω) t / t)
      atTop (𝓝 (repair / (fail + repair))) := by
  have hu' := hu.integral_eq_inv_of_expMeasure hfail
  have hd' := hd.integral_eq_inv_of_expMeasure hrepair
  have hpos : 0 < (∫ ω, U 0 ω ∂P) + (∫ ω, D 0 ω ∂P) := by
    rw [hu', hd']
    positivity
  have hU (n : ℕ) : ∀ᵐ ω ∂P, 0 ≤ U n ω :=
    ((hident n).comp measurable_fst).symm.ae_snd measurableSet_Ici (ae_nonneg_of_hasLaw_exp hu)
  have hD (n : ℕ) : ∀ᵐ ω ∂P, 0 ≤ D n ω :=
    ((hident n).comp measurable_snd).symm.ae_snd measurableSet_Ici (ae_nonneg_of_hasLaw_exp hd)
  have h := ae_tendsto_upTime_div U D hind hident hU hD
    (hu.integrable_of_expMeasure hfail) (hd.integrable_of_expMeasure hrepair) hpos
  have he : fail⁻¹ / (fail⁻¹ + repair⁻¹) = repair / (fail + repair) := by
    have hinv := add_pos (inv_pos.mpr hfail) (inv_pos.mpr hrepair)
    field_simp [hfail.ne', hrepair.ne', (add_pos hfail hrepair).ne', hinv.ne']
    exact add_comm _ _
  rwa [hu', hd', he] at h

/-- For a component started up that never fails, the elapsed up-time fraction is one at every
positive time. This is the absorbing-up case, not a zero-rate exponential law. -/
theorem alwaysUp_fraction {t : ℝ} (ht : 0 < t) :
    volume.real (Ico 0 t) / t = 1 := by
  rw [Real.volume_real_Ico, sub_zero, max_eq_left ht.le, div_self ht.ne']

/-- For a component that stays down after a single failure at finite time `u ≥ 0`, the fraction
of time up tends to zero. This is the absorbing-down case with no repair. -/
theorem tendsto_noRepair_fraction {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun t : ℝ => volume.real (Ico 0 t ∩ Ico 0 u) / t) atTop (𝓝 0) := by
  apply (tendsto_const_nhds.div_atTop tendsto_id :
    Tendsto (fun t : ℝ => u / t) atTop (𝓝 0)).congr'
  filter_upwards [eventually_ge_atTop u] with t ht
  rw [Ico_inter_Ico, max_self, min_eq_right ht, Real.volume_real_Ico, sub_zero, max_eq_left hu]

end Reliability.AlternatingRenewal
