/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.Birkhoff
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Birkhoff's ergodic theorem in `L¹` (ergodic case)

For an ergodic measure-preserving transformation `T` of a probability space
and an integrable observable `g`, the Birkhoff averages
`(1/n) ∑_{k<n} g ∘ T^[k]` converge to the space average `∫ g` in `L¹`.

Source: `v1/Atlas/TheoryOfProbability/code/BirkhoffErgodic.lean`,
`birkhoff_ergodic_theorem_L1` (Lecture 33, Birkhoff's ergodic theorem).
In `v1` the theorem is stated for a general measure-preserving `T` with
limit the conditional expectation onto the invariant `σ`-algebra, and its
proof is left unproved in v1. Here we prove the ergodic case, where the invariant
`σ`-algebra is trivial and the limit is the constant `∫ g`; this is the
case already available in `MathlibExt` in a.s. form
(`MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic`).
The general non-ergodic `L¹` statement is not claimed.

The proof is the standard density argument: Birkhoff averages are
`L¹`-contractions, so it suffices to prove `L¹` convergence for bounded
observables, where it follows from a.s. convergence plus dominated
convergence; general integrable observables are approximated in `L¹` by
their truncations.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Topology

namespace MathlibExt.Probability.BirkhoffErgodicL1

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {T : α → α}

/-- Birkhoff sums of an integrable observable under a measure-preserving
transformation are integrable. -/
theorem integrable_birkhoffSum_of_measurePreserving
    (hmp : MeasurePreserving T μ μ) {g : α → ℝ} (hg : Integrable g μ) (n : ℕ) :
    Integrable (birkhoffSum T g n) μ := by
  induction n with
  | zero => simp [birkhoffSum_zero]
  | succ n ih =>
    rw [birkhoffSum_succ']
    exact hg.add (hmp.integrable_comp_of_integrable ih)

/-- Birkhoff averages of an integrable observable under a measure-preserving
transformation are integrable. -/
theorem integrable_birkhoffAverage_of_measurePreserving
    (hmp : MeasurePreserving T μ μ) {g : α → ℝ} (hg : Integrable g μ) (n : ℕ) :
    Integrable (birkhoffAverage ℝ T g n) μ := by
  have h := integrable_birkhoffSum_of_measurePreserving hmp hg n
  exact Integrable.smul ((n : ℝ)⁻¹) h

/-- The integral of an observable is unchanged by precomposition with an
iterate of a measure-preserving transformation. -/
theorem integral_comp_iterate_of_measurePreserving
    (hmp : MeasurePreserving T μ μ) {u : α → ℝ} (hu : Integrable u μ) (k : ℕ) :
    ∫ x, u (T^[k] x) ∂μ = ∫ x, u x ∂μ := by
  have hmpk := hmp.iterate k
  have haes : AEStronglyMeasurable u (Measure.map (T^[k]) μ) := by
    rw [hmpk.map_eq]
    exact hu.aestronglyMeasurable
  have h1 : ∫ y, u y ∂(Measure.map (T^[k]) μ) = ∫ x, u (T^[k] x) ∂μ :=
    integral_map hmpk.measurable.aemeasurable haes
  rw [hmpk.map_eq] at h1
  exact h1.symm

/-- For `0 < n`, the integral of the `n`-th Birkhoff average of `u` equals
the integral of `u` (each orbit point contributes equally, by invariance). -/
theorem integral_birkhoffAverage_of_measurePreserving
    (hmp : MeasurePreserving T μ μ) {u : α → ℝ} (hu : Integrable u μ)
    {n : ℕ} (hn : 0 < n) :
    ∫ x, birkhoffAverage ℝ T u n x ∂μ = ∫ x, u x ∂μ := by
  have hsum : ∫ x, birkhoffSum T u n x ∂μ = (n : ℝ) * ∫ x, u x ∂μ := by
    have hint : ∀ k ∈ Finset.range n,
        Integrable (fun x => u (T^[k] x)) μ := by
      intro k _
      exact (hmp.iterate k).integrable_comp_of_integrable hu
    rw [show (fun x => birkhoffSum T u n x) = fun x => ∑ k ∈ Finset.range n, u (T^[k] x)
      from rfl]
    rw [integral_finsetSum _ hint]
    simp_rw [integral_comp_iterate_of_measurePreserving hmp hu]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have havg : ∫ x, birkhoffAverage ℝ T u n x ∂μ
      = (n : ℝ)⁻¹ • ∫ x, birkhoffSum T u n x ∂μ :=
    integral_smul ((n : ℝ)⁻¹) (birkhoffSum T u n)
  rw [havg, hsum, smul_eq_mul]
  exact inv_mul_cancel_left₀ (by exact_mod_cast hn.ne') _

omit [MeasurableSpace α] in
/-- Pointwise: the norm of a Birkhoff average is at most the Birkhoff average
of the pointwise norm. -/
theorem norm_birkhoffAverage_le_birkhoffAverage_norm
    {u : α → ℝ} (n : ℕ) (x : α) :
    ‖birkhoffAverage ℝ T u n x‖ ≤ birkhoffAverage ℝ T (fun y => ‖u y‖) n x := by
  by_cases hn : n = 0
  · subst hn
    simp [birkhoffAverage]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    show ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, u (T^[k] x)‖ ≤
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, ‖u (T^[k] x)‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn'.le), smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_sum_le (Finset.range n) (fun k => u (T^[k] x)))
      (inv_nonneg.mpr hn'.le)

omit [MeasurableSpace α] in
/-- Birkhoff averages are monotone in the observable. -/
theorem birkhoffAverage_le_birkhoffAverage
    {u v : α → ℝ} (h : ∀ y, u y ≤ v y) (n : ℕ) (x : α) :
    birkhoffAverage ℝ T u n x ≤ birkhoffAverage ℝ T v n x := by
  by_cases hn : n = 0
  · subst hn
    simp [birkhoffAverage]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    show (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, u (T^[k] x) ≤
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, v (T^[k] x)
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h _)
      (inv_nonneg.mpr hn'.le)

omit [MeasurableSpace α] in
/-- If `g` is bounded by `M ≥ 0` everywhere, so is every Birkhoff average. -/
theorem norm_birkhoffAverage_le_of_bounded
    {g : α → ℝ} {M : ℝ} (hM : 0 ≤ M) (hgb : ∀ x, ‖g x‖ ≤ M) (n : ℕ) (x : α) :
    ‖birkhoffAverage ℝ T g n x‖ ≤ M := by
  refine (norm_birkhoffAverage_le_birkhoffAverage_norm n x).trans ?_
  refine (birkhoffAverage_le_birkhoffAverage hgb n x).trans ?_
  by_cases hn : n = 0
  · subst hn
    simp [birkhoffAverage, hM]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hcomp : (fun _ : α => M) ∘ T = fun _ : α => M := rfl
    have h := birkhoffAverage_apply_of_comp_eq ℝ hcomp hn' x
    exact h.le

/-- Birkhoff averages are `L¹`-contractions: the `L¹` distance between two
averages is at most the `L¹` distance between the observables. -/
theorem integral_norm_birkhoffAverage_sub_le
    (hmp : MeasurePreserving T μ μ) {g h : α → ℝ}
    (hg : Integrable g μ) (hh : Integrable h μ) (n : ℕ) :
    ∫ x, ‖birkhoffAverage ℝ T g n x - birkhoffAverage ℝ T h n x‖ ∂μ ≤
      ∫ x, ‖g x - h x‖ ∂μ := by
  by_cases hn : n = 0
  · subst hn
    simp only [birkhoffAverage_zero_apply, sub_self, norm_zero, integral_zero]
    exact integral_nonneg (fun x => norm_nonneg _)
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hpoint : ∀ x, ‖birkhoffAverage ℝ T g n x - birkhoffAverage ℝ T h n x‖
        ≤ birkhoffAverage ℝ T (fun y => ‖(g - h) y‖) n x := by
      intro x
      rw [← birkhoffAverage_sub_apply]
      exact norm_birkhoffAverage_le_birkhoffAverage_norm n x
    have hL : Integrable (fun x => ‖birkhoffAverage ℝ T g n x
        - birkhoffAverage ℝ T h n x‖) μ :=
      ((integrable_birkhoffAverage_of_measurePreserving hmp hg n).sub
        (integrable_birkhoffAverage_of_measurePreserving hmp hh n)).norm
    have hR : Integrable (birkhoffAverage ℝ T (fun y => ‖(g - h) y‖) n) μ :=
      integrable_birkhoffAverage_of_measurePreserving hmp (hg.sub hh).norm n
    calc ∫ x, ‖birkhoffAverage ℝ T g n x - birkhoffAverage ℝ T h n x‖ ∂μ
        ≤ ∫ x, birkhoffAverage ℝ T (fun y => ‖(g - h) y‖) n x ∂μ :=
          integral_mono_ae hL hR (Filter.Eventually.of_forall hpoint)
      _ = ∫ x, ‖(g - h) x‖ ∂μ :=
          integral_birkhoffAverage_of_measurePreserving hmp (hg.sub hh).norm hn'
      _ = ∫ x, ‖g x - h x‖ ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Pi.sub_apply])

/-- Birkhoff's ergodic theorem in `L¹` for bounded observables: if `g` is
bounded by `M`, the `L¹` distance between the Birkhoff averages of `g` and
the space average `∫ g` tends to `0`. This follows from the a.s. theorem
plus dominated convergence. -/
theorem tendsto_integral_norm_birkhoffAverage_of_bounded
    [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) {g : α → ℝ} (hg : Integrable g μ)
    {M : ℝ} (hM : 0 ≤ M) (hgb : ∀ x, ‖g x‖ ≤ M) :
    Tendsto (fun n => ∫ x, ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖ ∂μ)
      atTop (𝓝 0) := by
  have hInt : ‖∫ y, g y ∂μ‖ ≤ M := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := M)
      (Filter.Eventually.of_forall hgb)
    rwa [probReal_univ, mul_one] at h
  have hDCT := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖)
    (f := fun _ => (0 : ℝ)) (bound := fun _ => 2 * M)
    (fun n => ((integrable_birkhoffAverage_of_measurePreserving
      hT.toMeasurePreserving hg n).sub (integrable_const _)).norm.aestronglyMeasurable)
    (integrable_const (2 * M))
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      calc ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖
          ≤ ‖birkhoffAverage ℝ T g n x‖ + ‖∫ y, g y ∂μ‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add
            (norm_birkhoffAverage_le_of_bounded hM hgb n x) hInt
        _ = 2 * M := by ring)
    (by
      filter_upwards [MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic
        hT hg] with x hx
      have hlim : Tendsto (fun n => birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ)
          atTop (𝓝 (∫ y, g y ∂μ - ∫ y, g y ∂μ)) :=
        hx.sub tendsto_const_nhds
      rw [sub_self] at hlim
      simpa using hlim.norm)
  simpa using hDCT

/-- **Birkhoff's ergodic theorem in `L¹` (ergodic case).** Let `T` be an
ergodic measure-preserving transformation of a probability space and let
`g` be integrable. Then the Birkhoff averages of `g` converge to the space
average `∫ g` in `L¹`:
`∫ ‖(1/n) ∑_{k<n} g ∘ T^[k] - ∫ g‖ → 0`. -/
theorem birkhoff_ergodic_theorem_L1
    [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) {g : α → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖ ∂μ)
      atTop (𝓝 0) := by
  classical
  -- Reduce to a measurable representative of `g`.
  obtain ⟨g', hg'meas, hg'ae, hg'int⟩ :
      ∃ g' : α → ℝ, Measurable g' ∧ g =ᵐ[μ] g' ∧ Integrable g' μ :=
    ⟨hg.aestronglyMeasurable.mk, hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hg.aestronglyMeasurable.ae_eq_mk, hg.congr hg.aestronglyMeasurable.ae_eq_mk⟩
  have htransfer : ∀ n, (∫ x, ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖ ∂μ)
      = ∫ x, ‖birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ‖ ∂μ := by
    intro n
    have hint : ∫ y, g y ∂μ = ∫ y, g' y ∂μ := integral_congr_ae hg'ae
    have havg : (fun x => ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖)
        =ᵐ[μ] fun x => ‖birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ‖ := by
      filter_upwards
        [MeasureTheory.Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ
          hT.toMeasurePreserving.quasiMeasurePreserving hg'ae n] with x hx
      rw [hx, hint]
    exact integral_congr_ae havg
  simp_rw [htransfer]
  -- Now `g'` is measurable. Argue by truncation.
  -- Truncations of `g'`.
  set htrunc : ℕ → α → ℝ := fun k x => max (-(k : ℝ)) (min (k : ℝ) (g' x)) with htrunc_def
  have htrunc_meas : ∀ k, Measurable (htrunc k) := by
    intro k
    exact measurable_const.max (measurable_const.min hg'meas)
  have htrunc_norm : ∀ k x, ‖htrunc k x‖ ≤ ‖g' x‖ := by
    intro k x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : -|g' x| ≤ htrunc k x := by
      refine le_trans ?_ (le_max_right _ _)
      exact le_min (by linarith [abs_nonneg (g' x)]) (neg_abs_le _)
    have h2 : htrunc k x ≤ |g' x| := by
      refine max_le ?_ ?_
      · linarith [abs_nonneg (g' x)]
      · exact (min_le_right _ _).trans (le_abs_self _)
    exact abs_le.mpr ⟨h1, h2⟩
  have htrunc_bound : ∀ k x, ‖htrunc k x‖ ≤ (k : ℝ) := by
    intro k x
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : -(k : ℝ) ≤ htrunc k x := le_max_left _ _
    have h2 : htrunc k x ≤ (k : ℝ) := max_le (by linarith) (min_le_left _ _)
    exact abs_le.mpr ⟨h1, h2⟩
  have htrunc_int : ∀ k, Integrable (htrunc k) μ := by
    intro k
    exact Integrable.mono hg'int (htrunc_meas k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => htrunc_norm k x)
  have htrunc_eq_of_le : ∀ (k : ℕ) (x : α), ‖g' x‖ ≤ (k : ℝ) → htrunc k x = g' x := by
    intro k x hxk
    have hxk' : |g' x| ≤ (k : ℝ) := by rwa [Real.norm_eq_abs] at hxk
    have h1 : -(k : ℝ) ≤ g' x := by
      have hneg := neg_abs_le (g' x)
      linarith
    have h2 : g' x ≤ (k : ℝ) := le_trans (le_abs_self _) hxk'
    rw [htrunc_def]
    simp only
    rw [min_eq_right h2, max_eq_right h1]
  have htrunc_L1 : Tendsto (fun k => ∫ x, ‖g' x - htrunc k x‖ ∂μ) atTop (𝓝 0) := by
    have hDCT := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun k x => ‖g' x - htrunc k x‖) (f := fun _ => (0 : ℝ))
      (bound := fun x => 2 * ‖g' x‖)
      (fun k => (hg'int.sub (htrunc_int k)).norm.aestronglyMeasurable)
      (hg'int.norm.const_mul 2)
      (fun k => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        calc ‖g' x - htrunc k x‖
            ≤ ‖g' x‖ + ‖htrunc k x‖ := norm_sub_le _ _
          _ ≤ ‖g' x‖ + ‖g' x‖ := add_le_add (le_refl _) (htrunc_norm k x)
          _ = 2 * ‖g' x‖ := by ring)
      (by
        filter_upwards with x
        obtain ⟨K, hK⟩ := exists_nat_ge ‖g' x‖
        refine tendsto_atTop_of_eventually_const (i₀ := K) (fun k hk => ?_)
        have hxk : ‖g' x‖ ≤ (k : ℝ) := le_trans hK (by exact_mod_cast hk)
        rw [htrunc_eq_of_le k x hxk, sub_self, norm_zero])
    simpa using hDCT
  -- `ε/3` argument.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨K, hKall⟩ := Metric.tendsto_atTop.mp htrunc_L1 (ε / 3) hε3
  have hK := hKall K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (integral_nonneg (fun x => norm_nonneg _))] at hK
  have hBoundedK := tendsto_integral_norm_birkhoffAverage_of_bounded hT (htrunc_int K)
    (Nat.cast_nonneg K) (fun x => htrunc_bound K x)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hBoundedK (ε / 3) hε3
  refine ⟨N, fun n hn => ?_⟩
  have hN' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (integral_nonneg (fun x => norm_nonneg _))] at hN'
  -- Three-term triangle estimate.
  have htri : ∀ x, ‖birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ‖
      ≤ ‖birkhoffAverage ℝ T g' n x - birkhoffAverage ℝ T (htrunc K) n x‖
        + ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖
        + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖ := by
    intro x
    have heq : birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ
        = (birkhoffAverage ℝ T g' n x - birkhoffAverage ℝ T (htrunc K) n x)
          + (birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ)
          + (∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  have hL : Integrable (fun x => ‖birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ‖) μ :=
    ((integrable_birkhoffAverage_of_measurePreserving hT.toMeasurePreserving hg'int n).sub
      (integrable_const _)).norm
  have hR1 : Integrable (fun x => ‖birkhoffAverage ℝ T g' n x
      - birkhoffAverage ℝ T (htrunc K) n x‖) μ :=
    ((integrable_birkhoffAverage_of_measurePreserving hT.toMeasurePreserving hg'int n).sub
      (integrable_birkhoffAverage_of_measurePreserving hT.toMeasurePreserving
        (htrunc_int K) n)).norm
  have hR2 : Integrable (fun x => ‖birkhoffAverage ℝ T (htrunc K) n x
      - ∫ y, htrunc K y ∂μ‖) μ :=
    ((integrable_birkhoffAverage_of_measurePreserving hT.toMeasurePreserving
      (htrunc_int K) n).sub (integrable_const _)).norm
  have hR3 : Integrable (fun _ => ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖) μ :=
    integrable_const _
  have hIntTri : ∫ x, ‖birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ‖ ∂μ
      ≤ ∫ x, ‖birkhoffAverage ℝ T g' n x - birkhoffAverage ℝ T (htrunc K) n x‖ ∂μ
        + ∫ x, ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖ ∂μ
        + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖ := by
    have hR : Integrable (fun x => ‖birkhoffAverage ℝ T g' n x
        - birkhoffAverage ℝ T (htrunc K) n x‖
        + ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖
        + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖) μ :=
      (hR1.add hR2).add hR3
    have hmono := integral_mono_ae hL hR (Filter.Eventually.of_forall htri)
    have hsplit : ∫ x, (‖birkhoffAverage ℝ T g' n x
        - birkhoffAverage ℝ T (htrunc K) n x‖
        + ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖
        + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖) ∂μ
        = ∫ x, ‖birkhoffAverage ℝ T g' n x - birkhoffAverage ℝ T (htrunc K) n x‖ ∂μ
          + ∫ x, ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖ ∂μ
          + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖ := by
      have e1 : ∫ x, (‖birkhoffAverage ℝ T g' n x
          - birkhoffAverage ℝ T (htrunc K) n x‖
          + ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖
          + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖) ∂μ
          = ∫ x, (‖birkhoffAverage ℝ T g' n x
              - birkhoffAverage ℝ T (htrunc K) n x‖
            + ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖) ∂μ
            + ∫ _, ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖ ∂μ :=
        integral_add (hR1.add hR2) hR3
      have e2 : ∫ x, (‖birkhoffAverage ℝ T g' n x
          - birkhoffAverage ℝ T (htrunc K) n x‖
          + ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖) ∂μ
          = ∫ x, ‖birkhoffAverage ℝ T g' n x - birkhoffAverage ℝ T (htrunc K) n x‖ ∂μ
            + ∫ x, ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖ ∂μ :=
        integral_add hR1 hR2
      rw [e1, e2, integral_const, probReal_univ, one_smul]
    rw [hsplit] at hmono
    exact hmono
  have hContract := integral_norm_birkhoffAverage_sub_le hT.toMeasurePreserving hg'int
    (htrunc_int K) n
  have hMean : ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖ ≤ ∫ x, ‖g' x - htrunc K x‖ ∂μ := by
    have hsub : ∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ
        = ∫ y, (htrunc K y - g' y) ∂μ := (integral_sub (htrunc_int K) hg'int).symm
    rw [hsub]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_ae ((htrunc_int K).sub hg'int).norm (hg'int.sub (htrunc_int K)).norm
      (Filter.Eventually.of_forall fun x => ?_)
    exact (norm_sub_rev _ _).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (integral_nonneg (fun x => norm_nonneg _))]
  calc ∫ x, ‖birkhoffAverage ℝ T g' n x - ∫ y, g' y ∂μ‖ ∂μ
      ≤ ∫ x, ‖birkhoffAverage ℝ T g' n x - birkhoffAverage ℝ T (htrunc K) n x‖ ∂μ
        + ∫ x, ‖birkhoffAverage ℝ T (htrunc K) n x - ∫ y, htrunc K y ∂μ‖ ∂μ
        + ‖∫ y, htrunc K y ∂μ - ∫ y, g' y ∂μ‖ := hIntTri
    _ ≤ ∫ x, ‖g' x - htrunc K x‖ ∂μ + ε / 3 + ∫ x, ‖g' x - htrunc K x‖ ∂μ := by
        exact add_le_add (add_le_add hContract (le_of_lt hN') ) hMean
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [hK]
    _ = ε := by ring

end MathlibExt.Probability.BirkhoffErgodicL1
