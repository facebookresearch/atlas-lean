/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The running maximum of Brownian motion has the law of `|B_t|`

The running maximum of a real Brownian motion with measurable coordinates and continuous paths
has the same law as the absolute value of its terminal coordinate at positive times.
The proof uses symmetry after the first crossing on finite grids, continuity of the paths,
and dominated convergence to compare tail probabilities.

## References

* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Théorème 14.5.1, Théorème 14.5.2 and Corollaire 14.5.3.
* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2,
  section "The strong Markov property of Brownian motion".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology ProbabilityTheory

namespace MathlibExt.Probability.BrownianStrongMarkovWanted

private theorem increment_sign_symmetry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P {ω | B t ω - B s ω < 0} = P {ω | 0 < B t ω - B s ω} := by
  have hlaw : HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) P := by
    simpa only [add_tsub_cancel_of_le hst] using (hB.shift s).hasLaw_eval (t - s)
  have hneg : HasLaw (fun ω ↦ -(B t ω - B s ω)) (gaussianReal 0 (t - s)) P := by
    simpa only [neg_zero, Pi.neg_def] using gaussianReal_neg hlaw
  have heq := hlaw.map_eq.trans hneg.map_eq.symm
  have hm : Measurable (fun ω ↦ B t ω - B s ω) := (hBm t).sub (hBm s)
  have h := congrArg (fun μ : Measure ℝ ↦ μ (Set.Ioi 0)) heq
  rw [Measure.map_apply hm measurableSet_Ioi,
    Measure.map_apply (show Measurable (fun ω ↦ -(B t ω - B s ω)) from hm.neg)
      measurableSet_Ioi] at h
  simpa only [Set.preimage, Set.mem_Ioi, neg_pos] using h.symm

private theorem past_increment_sign_symmetry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun ω (u : Set.Iic s) ↦ B u ω) inferInstance] A) :
    P (A ∩ {ω | B t ω < B s ω}) = P (A ∩ {ω | B s ω < B t ω}) := by
  have hi : IndepFun (fun ω ↦ B t ω - B s ω)
      (fun ω (u : Set.Iic s) ↦ B u ω) P := by
    have h := (hB.toIsPreBrownianReal.indepFun_shift s).comp
      (measurable_pi_apply (t - s)) measurable_id
    simpa only [Function.comp_def, add_tsub_cancel_of_le hst, id_eq] using h
  have hm : Measurable[MeasurableSpace.comap
      (fun ω ↦ B t ω - B s ω) inferInstance] (fun ω ↦ B t ω - B s ω) :=
    Measurable.of_comap_le le_rfl
  have hn := hi.symm.meas_inter (t := {ω | B t ω - B s ω < 0}) hA
    (measurableSet_lt hm measurable_const)
  have hp := hi.symm.meas_inter (t := {ω | 0 < B t ω - B s ω}) hA
    (measurableSet_lt measurable_const hm)
  simpa only [sub_neg, sub_pos] using hn.trans
    ((congrArg (P A * ·) (increment_sign_symmetry hB hBm hst)).trans hp.symm)

private def firstCross {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (q : ℕ → ℝ≥0)
    (a : ℝ) (i : ℕ) : Set Ω :=
  {ω | a < B (q i) ω ∧ ∀ j : Fin i, B (q j) ω ≤ a}

private theorem measurable_firstCross {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (q : ℕ → ℝ≥0) (a : ℝ) (i : ℕ) : MeasurableSet (firstCross B q a i) := by
  simp only [firstCross, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_lt measurable_const (hBm (q i))).inter
    (MeasurableSet.iInter fun j : Fin i ↦ measurableSet_le (hBm (q j)) measurable_const)

private theorem measurable_firstCross_past {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {q : ℕ → ℝ≥0} (hq : Monotone q) (a : ℝ) (i : ℕ) :
    MeasurableSet[MeasurableSpace.comap (fun ω (u : Set.Iic (q i)) ↦ B u ω)
      inferInstance] (firstCross B q a i) := by
  have hm (j : ℕ) (hj : j ≤ i) : Measurable[MeasurableSpace.comap
      (fun ω (u : Set.Iic (q i)) ↦ B u ω) inferInstance] (B (q j)) := by
    simpa only [Function.comp_def] using
      (measurable_pi_apply (⟨q j, hq hj⟩ : Set.Iic (q i))).comp
        (comap_measurable (fun ω (u : Set.Iic (q i)) ↦ B u ω))
  simp only [firstCross, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_lt measurable_const (hm i le_rfl)).inter
    (MeasurableSet.iInter fun j : Fin i ↦ measurableSet_le (hm j j.isLt.le) measurable_const)

private theorem disjoint_firstCross {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    (q : ℕ → ℝ≥0) (a : ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (firstCross B q a i) (firstCross B q a j) := by
  rw [Set.disjoint_left]
  intro ω hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hj.2 ⟨i, h⟩)) hi.1
  · exact (not_lt_of_ge (hi.2 ⟨j, h⟩)) hj.1

private theorem finite_crossing_symmetry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {q : ℕ → ℝ≥0} (hq : Monotone q)
    {t : ℝ≥0} (n : ℕ) (hqt : ∀ i ≤ n, q i ≤ t) (a : ℝ) :
    P (⋃ i ∈ Finset.range (n + 1), firstCross B q a i ∩ {ω | B t ω < B (q i) ω}) =
      P (⋃ i ∈ Finset.range (n + 1), firstCross B q a i ∩ {ω | B (q i) ω < B t ω}) := by
  rw [measure_biUnion_finset, measure_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro i hi
    exact past_increment_sign_symmetry hB hBm (hqt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
      (measurable_firstCross_past hq a i)
  · intro i hi j hj hij
    exact (disjoint_firstCross q a hij).mono Set.inter_subset_left Set.inter_subset_left
  · intro i hi
    exact (measurable_firstCross hBm q a i).inter (measurableSet_lt (hBm (q i)) (hBm t))
  · intro i hi j hj hij
    exact (disjoint_firstCross q a hij).mono Set.inter_subset_left Set.inter_subset_left
  · intro i hi
    exact (measurable_firstCross hBm q a i).inter (measurableSet_lt (hBm t) (hBm (q i)))

private noncomputable def grid (t : ℝ≥0) (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) * t / (n + 1)

private theorem grid_mono (t : ℝ≥0) (n : ℕ) : Monotone (grid t n) := by
  intro i j hij
  dsimp [grid]
  gcongr

private theorem grid_le (t : ℝ≥0) (n : ℕ) {i : ℕ} (hi : i ≤ n + 1) : grid t n i ≤ t := by
  dsimp [grid]
  rw [div_le_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)]
  calc
    (i : ℝ≥0) * t ≤ (n + 1) * t := by gcongr; exact_mod_cast hi
    _ = t * (n + 1) := mul_comm _ _

private theorem grid_dist (t : ℝ≥0) (n : ℕ) {i : ℕ} (hi : 0 < i) :
    dist (grid t n i) (grid t n (i - 1)) = (t : ℝ) / (n + 1) := by
  change dist (grid t n i : ℝ) (grid t n (i - 1) : ℝ) = _
  have hd : (grid t n i : ℝ) - (grid t n (i - 1) : ℝ) = (t : ℝ) / (n + 1) := by
    simp only [grid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi.ne'), Nat.cast_one]
    ring
  rw [Real.dist_eq, hd, abs_of_nonneg (by positivity)]

private theorem grid_mesh_tendsto (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ (t : ℝ) / (n + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp h)

private theorem grid_floor_tendsto {t : ℝ≥0} (ht : 0 < t) (s : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ grid t n ⌊(s : ℝ) / t * ((n : ℝ) + 1)⌋₊) atTop (𝓝 s) := by
  apply NNReal.tendsto_coe.mp
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim := (tendsto_nat_floor_mul_div_atTop (show (0 : ℝ) ≤ (s : ℝ) / t by positivity)).comp h
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  simpa only [grid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_one, div_mul_cancel₀ _ ht', Function.comp_def, div_mul_eq_mul_div] using
    hlim.mul_const (t : ℝ)

private theorem grid_floor_le {t : ℝ≥0} (ht : 0 < t) {s : ℝ≥0} (hs : s ≤ t) (n : ℕ) :
    ⌊(s : ℝ) / t * ((n : ℝ) + 1)⌋₊ ≤ n + 1 := by
  apply Nat.floor_le_of_le
  have hst : (s : ℝ) / t ≤ 1 := (div_le_one (by exact_mod_cast ht)).mpr (by exact_mod_cast hs)
  have h := mul_le_mul_of_nonneg_right hst (show 0 ≤ (n : ℝ) + 1 by positivity)
  simpa using h

private theorem crossing_overshoot_eventually {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t ↦ B t ω)
    (ω : Ω) {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (h0 : B 0 ω < a)
    (hs : ∃ s : Set.Icc (0 : ℝ≥0) t, a < B s ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ i ≤ n + 1,
      ω ∈ firstCross B (grid t n) a i ∧ B (grid t n i) ω < a + ε := by
  obtain ⟨s, hs⟩ := hs
  have hlim := ((hcont ω).tendsto s).comp (grid_floor_tendsto ht s)
  have hsample := hlim.eventually (Ioi_mem_nhds hs)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (hcont ω).continuousOn) ε hε
  have hmesh := (grid_mesh_tendsto t).eventually (Iio_mem_nhds hδ)
  filter_upwards [hsample, hmesh] with n hn hdn
  have hex : ∃ i : ℕ, a < B (grid t n i) ω := ⟨_, hn⟩
  let i := Nat.find hex
  have hic : a < B (grid t n i) ω := Nat.find_spec hex
  have hib : i ≤ n + 1 := (Nat.find_min' hex hn).trans (grid_floor_le ht s.2.2 n)
  have hip : 0 < i := by
    by_contra h
    have hiz : i = 0 := Nat.eq_zero_of_not_pos h
    simp only [hiz, grid, Nat.cast_zero, zero_mul, zero_div] at hic
    exact (not_lt_of_ge h0.le) hic
  have hcross : ω ∈ firstCross B (grid t n) a i := by
    refine ⟨hic, ?_⟩
    intro j
    exact le_of_not_gt (Nat.find_min hex j.isLt)
  have hprev : B (grid t n (i - 1)) ω ≤ a :=
    le_of_not_gt (Nat.find_min hex (Nat.sub_lt hip (by decide)))
  have hm1 : grid t n i ∈ Set.Icc (0 : ℝ≥0) t := ⟨bot_le, grid_le t n hib⟩
  have hm2 : grid t n (i - 1) ∈ Set.Icc (0 : ℝ≥0) t :=
    ⟨bot_le, grid_le t n ((Nat.sub_le i 1).trans hib)⟩
  have hd := huc _ hm1 _ hm2 (by simpa only [grid_dist t n hip] using hdn)
  have hdiff := (abs_lt.mp (show |B (grid t n i) ω - B (grid t n (i - 1)) ω| < ε from hd)).2
  exact ⟨i, hib, hcross, by linarith⟩

private theorem bounded_path {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) (ω : Ω) (t : ℝ≥0) :
    BddAbove (Set.range fun s : Set.Icc (0 : ℝ≥0) t ↦ B s ω) := by
  have hc : Continuous fun s : Set.Icc (0 : ℝ≥0) t ↦ B s ω :=
    (hcont ω).comp continuous_subtype_val
  simpa only [Set.image_univ] using isCompact_univ.bddAbove_image hc.continuousOn

private noncomputable def crossingLeft {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : ℝ)
    (n : ℕ) : Set Ω :=
  ⋃ i ∈ Finset.range (n + 2), firstCross B (grid t n) a i ∩ {ω | B t ω < B (grid t n i) ω}

private noncomputable def crossingRight {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : ℝ)
    (n : ℕ) : Set Ω :=
  ⋃ i ∈ Finset.range (n + 2), firstCross B (grid t n) a i ∩ {ω | B (grid t n i) ω < B t ω}

private theorem crossing_events_eventually {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t ↦ B t ω)
    (ω : Ω) {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (h0 : B 0 ω < a) (hBt : B t ω ≠ a) :
    ∀ᶠ n : ℕ in atTop,
      (ω ∈ crossingLeft B t a n ↔ a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a) ∧
      (ω ∈ crossingRight B t a n ↔ a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ a < B t ω) := by
  classical
  have : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, bot_le, bot_le⟩⟩
  by_cases hS : a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω
  · have hs := (lt_ciSup_iff (bounded_path hcont ω t)).mp hS
    have heps : 0 < |B t ω - a| := abs_pos.mpr (sub_ne_zero.mpr hBt)
    filter_upwards [crossing_overshoot_eventually hcont ω ht h0 hs heps] with n hn
    obtain ⟨i, hib, hic, hiv⟩ := hn
    have huniq {j : ℕ} (hj : ω ∈ firstCross B (grid t n) a j) : j = i := by
      by_contra h
      exact Set.disjoint_left.mp (disjoint_firstCross (grid t n) a h) hj hic
    have hL : ω ∈ crossingLeft B t a n ↔ B t ω < B (grid t n i) ω := by
      simp only [crossingLeft, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨j, hjb, hjc, hjv⟩
        simpa only [huniq hjc, Set.mem_ofPred_eq] using hjv
      · intro h
        exact ⟨i, Finset.mem_range.mpr (by omega), hic, h⟩
    have hR : ω ∈ crossingRight B t a n ↔ B (grid t n i) ω < B t ω := by
      simp only [crossingRight, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨j, hjb, hjc, hjv⟩
        simpa only [huniq hjc, Set.mem_ofPred_eq] using hjv
      · intro h
        exact ⟨i, Finset.mem_range.mpr (by omega), hic, h⟩
    rw [hL, hR]
    rcases lt_or_gt_of_ne hBt with h | h
    · have hi := hic.1
      exact ⟨by simp [hS, h, h.trans hi], by simp [hS, h.not_gt, (h.trans hi).not_gt]⟩
    · have hi : B (grid t n i) ω < B t ω := by
        rw [abs_of_pos (sub_pos.mpr h)] at hiv
        linarith
      exact ⟨by simp [hS, h.not_gt, hi.not_gt], by simp [hS, h, hi]⟩
  · apply Eventually.of_forall
    intro n
    have hnone {i : ℕ} (hi : i ∈ Finset.range (n + 2)) : ω ∉ firstCross B (grid t n) a i := by
      intro hc
      have hib : i ≤ n + 1 := by have := Finset.mem_range.mp hi; omega
      have hle := le_ciSup (bounded_path hcont ω t)
        (⟨grid t n i, bot_le, grid_le t n hib⟩ : Set.Icc (0 : ℝ≥0) t)
      exact hS (hc.1.trans_le hle)
    constructor <;> simp only [hS, false_and, iff_false, crossingLeft, crossingRight,
      Set.mem_iUnion, Set.mem_inter_iff, not_exists, not_and]
    all_goals intro i hi hc; exact (hnone hi hc).elim

private theorem measurable_sup {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) (t : ℝ≥0) :
    Measurable fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω := by
  obtain ⟨T, hTcount, hTsub, hTdense⟩ :=
    TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ≥0) t)
  have h0mem : (0 : ℝ≥0) ∈ Set.Icc (0 : ℝ≥0) t := Set.mem_Icc.mpr ⟨le_rfl, by positivity⟩
  have : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, h0mem⟩⟩
  have hTne : T.Nonempty := by
    have h0c : (0 : ℝ≥0) ∈ closure T := hTdense h0mem
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at h0c
    simp at h0c
  obtain ⟨xT, hxT⟩ := hTne
  have : Nonempty T := ⟨⟨xT, hxT⟩⟩
  have : Countable T := hTcount
  have hTeq : ∀ ω, (⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) = ⨆ q : T, B q ω := by
    intro ω
    apply le_antisymm
    · apply ciSup_le
      intro s
      obtain ⟨u, huT, hulim⟩ := mem_closure_iff_seq_limit.mp (hTdense s.2)
      have hlim : Filter.Tendsto (fun n ↦ B (u n) ω) Filter.atTop (nhds (B s ω)) :=
        ((hcont ω).tendsto s).comp hulim
      have hbdd : BddAbove (Set.range fun q : T ↦ B q ω) := by
        apply BddAbove.mono _ (bounded_path hcont ω t)
        intro y hy
        obtain ⟨q, rfl⟩ := hy
        exact Set.mem_range_self (⟨q, hTsub q.2⟩ : Set.Icc (0 : ℝ≥0) t)
      have hev : ∀ᶠ n in Filter.atTop, (fun n ↦ B (u n) ω) n ≤ ⨆ q : T, B q ω := by
        apply Filter.Eventually.of_forall
        intro n
        exact le_ciSup hbdd ⟨u n, huT n⟩
      exact le_of_tendsto hlim hev
    · apply ciSup_le
      intro q
      exact le_ciSup (bounded_path hcont ω t) ⟨q, hTsub q.2⟩
  have heq : (fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) = fun ω ↦ ⨆ q : T, B q ω :=
    funext hTeq
  rw [heq]
  exact Measurable.iSup fun q ↦ hBm q

private theorem tendsto_measure_of_eventually_mem {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {A : ℕ → Set Ω} {C : Set Ω}
    (hA : ∀ n, MeasurableSet (A n)) (hC : MeasurableSet C)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n ↔ ω ∈ C) :
    Tendsto (fun n ↦ P (A n)) atTop (𝓝 (P C)) := by
  classical
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (A n).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω)
      atTop (𝓝 (C.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω)) := by
    filter_upwards [h] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    simp only [Set.indicator_apply, hn]
  have hbound (n : ℕ) : (A n).indicator (fun _ ↦ (1 : ℝ≥0∞)) ≤ᵐ[P] fun _ ↦ 1 := by
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ A n <;> simp [hω]
  have hi := tendsto_lintegral_of_dominated_convergence (μ := P) (fun _ ↦ 1)
    (fun n ↦ measurable_const.indicator (hA n)) hbound (by simp) hlim
  simpa only [lintegral_indicator (hA _), lintegral_indicator hC, lintegral_const,
    Measure.restrict_apply_univ, one_mul] using hi

private theorem strict_reflection_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t ↦ B t ω)
    {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (ha : 0 < a) :
    P {ω | a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a} = P {ω | a < B t ω} := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval t).isProbabilityMeasure
  have : NullSingletonClass (gaussianReal 0 t) := nullSingletonClass_gaussianReal ht.ne'
  have hnull : P {ω | B t ω = a} = 0 := by
    simpa only [Set.ofPred_eq_eq_singleton, measure_singleton] using
      (hB.hasLaw_eval t).measure_eq (p := fun x ↦ x = a) (measurableSet_singleton a)
  have hne : ∀ᵐ ω ∂P, B t ω ≠ a := by
    simpa only [ae_iff, not_not] using hnull
  have hae : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (ω ∈ crossingLeft B t a n ↔ a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a) ∧
      (ω ∈ crossingRight B t a n ↔ a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ a < B t ω) := by
    filter_upwards [hB.eval_zero_ae_eq_zero, hne] with ω h0 hω
    exact crossing_events_eventually hcont ω ht (by simpa only [h0] using ha) hω
  have hml (n : ℕ) : MeasurableSet (crossingLeft B t a n) := by
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro hi
    exact (measurable_firstCross hBm (grid t n) a i).inter
      (measurableSet_lt (hBm t) (hBm (grid t n i)))
  have hmr (n : ℕ) : MeasurableSet (crossingRight B t a n) := by
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro hi
    exact (measurable_firstCross hBm (grid t n) a i).inter
      (measurableSet_lt (hBm (grid t n i)) (hBm t))
  have hms : MeasurableSet {ω | a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω} :=
    measurableSet_lt measurable_const (measurable_sup hBm hcont t)
  have hL := tendsto_measure_of_eventually_mem hml
    (hms.inter (measurableSet_lt (hBm t) measurable_const))
    (hae.mono fun _ h ↦ h.mono fun _ hn ↦ hn.1)
  have hR := tendsto_measure_of_eventually_mem (P := P) hmr
    (hms.inter (measurableSet_lt measurable_const (hBm t)))
    (hae.mono fun _ h ↦ h.mono fun _ hn ↦ hn.2)
  have heq (n : ℕ) : P (crossingLeft B t a n) = P (crossingRight B t a n) := by
    exact finite_crossing_symmetry hB hBm (grid_mono t n) (n + 1) (fun i hi ↦ grid_le t n hi) a
  have hL' : Tendsto (fun n ↦ P (crossingRight B t a n)) atTop
      (𝓝 (P {ω | a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a})) := by
    simpa only [heq, ← Set.ofPred_and] using hL
  have hres := tendsto_nhds_unique hL' hR
  have hset : {ω | a < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ a < B t ω} = {ω | a < B t ω} := by
    ext ω
    constructor
    · exact And.right
    · intro hω
      exact ⟨hω.trans_le (le_ciSup (bounded_path hcont ω t) ⟨t, bot_le, le_rfl⟩), hω⟩
  simpa only [← Set.ofPred_and, hset] using hres

private theorem positive_reflection_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t ↦ B t ω)
    {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (ha : 0 < a) :
    P {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a} = P {ω | a ≤ B t ω} := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval t).isProbabilityMeasure
  let c (n : ℕ) : ℝ := a - a / (n + 2)
  have hpos (n : ℕ) : 0 < c n := by
    exact sub_pos.mpr (div_lt_self ha (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hlt (n : ℕ) : c n < a := sub_lt_self _ (div_pos ha (by positivity))
  have hlim : Tendsto c atTop (𝓝 a) := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hm := (tendsto_inv_atTop_zero.comp hn).const_mul a
    simpa only [c, div_eq_mul_inv, Function.comp_def, mul_zero, sub_zero] using
      tendsto_const_nhds.sub hm
  have hu (x : ℝ) : ∀ᶠ n in atTop, c n < x ↔ a ≤ x := by
    by_cases hx : a ≤ x
    · exact Eventually.of_forall fun n ↦ iff_of_true ((hlt n).trans_le hx) hx
    · filter_upwards [hlim.eventually (Ioi_mem_nhds (lt_of_not_ge hx))] with n hn
      exact iff_of_false (not_lt_of_ge hn.le) hx
  have hl (x : ℝ) : ∀ᶠ n in atTop, x < c n ↔ x < a := by
    by_cases hx : x < a
    · filter_upwards [hlim.eventually (Ioi_mem_nhds hx)] with n hn
      exact iff_of_true hn hx
    · exact Eventually.of_forall fun n ↦ iff_of_false
        (not_lt_of_ge ((hlt n).le.trans (le_of_not_gt hx))) hx
  have hleft : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ {ω | c n < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < c n} ↔
      ω ∈ {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a} := by
    apply Eventually.of_forall
    intro ω
    filter_upwards [hu (⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω), hl (B t ω)] with n hn hm
    exact and_congr hn hm
  have hmS := measurable_sup hBm hcont t
  have hL := tendsto_measure_of_eventually_mem
    (A := fun n ↦ {ω | c n < ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < c n})
    (C := {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a})
    (fun n ↦ (measurableSet_lt measurable_const hmS).inter
      (measurableSet_lt (hBm t) measurable_const))
    ((measurableSet_le measurable_const hmS).inter
      (measurableSet_lt (hBm t) measurable_const)) hleft
  have hR := tendsto_measure_of_eventually_mem (P := P)
    (A := fun n ↦ {ω | c n < B t ω}) (C := {ω | a ≤ B t ω})
    (fun n ↦ measurableSet_lt measurable_const (hBm t))
    (measurableSet_le measurable_const (hBm t)) (Eventually.of_forall fun ω ↦ hu (B t ω))
  have heq (n : ℕ) := strict_reflection_tail hB hBm hcont ht (hpos n)
  have hL' : Tendsto (fun n ↦ P {ω | c n < B t ω}) atTop
      (𝓝 (P {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a})) := by
    simpa only [heq] using hL
  exact tendsto_nhds_unique hL' hR

private theorem measurable_abs {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    Measurable fun ω ↦ |B t ω| :=
  continuous_abs.measurable.comp (hBm t)

private theorem measure_neg_bt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (a : ℝ) :
    P {ω | B t ω ≤ -a} = P {ω | a ≤ B t ω} := by
  have h1 : P.map (B t) = gaussianReal 0 t :=
    (hB.toIsPreBrownianReal.hasLaw_eval t).map_eq
  have h2 : P.map (-B t) = gaussianReal 0 t := by
    have hneg := gaussianReal_neg (hB.toIsPreBrownianReal.hasLaw_eval t)
    rw [neg_zero] at hneg
    exact hneg.map_eq
  have hsymm : P.map (-B t) = P.map (B t) := by rw [h1, h2]
  have hneg : Measurable (-B t) := (hBm t).neg
  have hset1 : (-B t) ⁻¹' Set.Ici a = {ω | B t ω ≤ -a} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq, Pi.neg_apply]
    exact le_neg.symm
  have hset2 : (B t) ⁻¹' Set.Ici a = {ω | a ≤ B t ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq]
  have hleft : P {ω | B t ω ≤ -a} = P.map (-B t) (Set.Ici a) := by
    rw [Measure.map_apply hneg measurableSet_Ici, hset1]
  have hright : P {ω | a ≤ B t ω} = P.map (B t) (Set.Ici a) := by
    rw [Measure.map_apply (hBm t) measurableSet_Ici, hset2]
  rw [hleft, hright, hsymm]

/-- **The running maximum has the law of `|B_t|`.** For a Brownian motion `B` with continuous
paths and measurable coordinates and `t > 0`, `S_t = sup_{s ≤ t} B s` has the same law as
`|B_t|` (Le Gall, ENS notes *Intégration, Probabilités et Processus Aléatoires*,
Théorème 14.5.2, second assertion). -/
theorem IsBrownianReal.map_iSup_eq_map_abs {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) {t : ℝ≥0} (ht : 0 < t) :
    P.map (fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) = P.map (fun ω ↦ |B t ω|)
    := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval t).isProbabilityMeasure
  apply Measure.ext_of_Ici
  intro a
  rw [Measure.map_apply (measurable_sup hBm hcont t) measurableSet_Ici,
    Measure.map_apply (measurable_abs hBm t) measurableSet_Ici]
  have hBtle : ∀ ω, B t ω ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω := fun ω ↦
    le_ciSup (bounded_path hcont ω t) ⟨t, Set.mem_Icc.mpr ⟨by positivity, le_rfl⟩⟩
  rcases le_or_gt a 0 with ha | ha
  · have hR : (fun ω ↦ |B t ω|) ⁻¹' Set.Ici a = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
      exact le_trans ha (abs_nonneg _)
    have hL : P ((fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) ⁻¹' Set.Ici a) = 1 := by
      have hmeas : MeasurableSet ((fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) ⁻¹' Set.Ici a) :=
        (measurable_sup hBm hcont t) measurableSet_Ici
      rw [← prob_compl_eq_zero_iff hmeas]
      have hsub : ((fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) ⁻¹' Set.Ici a)ᶜ
          ⊆ {ω | B 0 ω ≠ 0} := by
        intro ω hω
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Ici, not_le] at hω
        have hle : B 0 ω ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω :=
          le_ciSup (bounded_path hcont ω t) ⟨0, Set.mem_Icc.mpr ⟨le_rfl, by positivity⟩⟩
        simp only [Set.mem_ofPred_eq]
        exact ne_of_lt (lt_of_le_of_lt hle (lt_of_lt_of_le hω ha))
      have h0 : P {ω | B 0 ω ≠ 0} = 0 :=
        ae_iff.mp hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
      exact measure_mono_null hsub h0
    rw [hL, hR, measure_univ]
  · have hsplit : (fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) ⁻¹' Set.Ici a
        = (B t ⁻¹' Set.Ici a) ∪ {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · intro h
        rcases le_or_gt a (B t ω) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | ⟨h, -⟩)
        · exact le_trans h (hBtle ω)
        · exact h
    have hdisj : Disjoint (B t ⁻¹' Set.Ici a)
        {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a} := by
      rw [Set.disjoint_left]
      rintro ω h1 h2
      simp only [Set.mem_preimage, Set.mem_Ici] at h1
      simp only [Set.mem_ofPred_eq] at h2
      exact lt_irrefl _ (lt_of_le_of_lt h1 h2.2)
    have hmeas2 : MeasurableSet {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a} := by
      have h1 : MeasurableSet {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω} :=
        (measurable_sup hBm hcont t) measurableSet_Ici
      have h2 : MeasurableSet {ω | B t ω < a} := measurableSet_lt (hBm t) measurable_const
      exact h1.inter h2
    have hmid : P {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω < a}
        = P (B t ⁻¹' Set.Ici a) :=
      positive_reflection_tail hB hBm hcont ht ha
    have hE1 : P ((fun ω ↦ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω) ⁻¹' Set.Ici a)
        = 2 * P (B t ⁻¹' Set.Ici a) := by
      rw [hsplit, measure_union hdisj hmeas2, hmid, two_mul]
    have hsplitA : (fun ω ↦ |B t ω|) ⁻¹' Set.Ici a
        = (B t ⁻¹' Set.Ici a) ∪ (B t ⁻¹' Set.Iic (-a)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_union, Set.mem_Iic]
      constructor
      · intro h
        rcases le_abs.mp h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (le_neg.mp h')
      · rintro (h | h)
        · exact le_trans h (le_abs_self _)
        · have h' : a ≤ -(B t ω) := by linarith
          exact le_trans h' (neg_le_abs _)
    have hdisjA : Disjoint (B t ⁻¹' Set.Ici a) (B t ⁻¹' Set.Iic (-a)) := by
      rw [Set.disjoint_left]
      rintro ω h1 h2
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic] at h1 h2
      linarith
    have hsymm : P (B t ⁻¹' Set.Iic (-a)) = P (B t ⁻¹' Set.Ici a) := measure_neg_bt hB hBm t a
    have hE2 : P ((fun ω ↦ |B t ω|) ⁻¹' Set.Ici a) = 2 * P (B t ⁻¹' Set.Ici a) := by
      rw [hsplitA, measure_union hdisjA ((hBm t) measurableSet_Iic), hsymm, two_mul]
    rw [hE1, hE2]

end MathlibExt.Probability.BrownianStrongMarkovWanted
