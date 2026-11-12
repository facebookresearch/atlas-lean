/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.FunctionalCLT
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Aldous's tightness criterion and the functional CLT for martingale arrays

Row `n` of a triangular array `ξ n 0, ξ n 1, …, ξ n (n-1)` is observed at the times `k / n`;
its partial sums `S n k = ∑_{i < k} ξ n i` give a step path in `D([0,1])` (`arrayStepProcess`)
and a polygonal path in `C([0,1])` (`arrayPolygon`). Row `n` is filtered by `𝓕 n`.

## Main definitions

* `arrayStepProcess n ξ`: `t ↦ ∑_{i < ⌊n t⌋} ξ n i`, T43's `skorokhodStepProcess` without the
  `1/√n` normalization.
* `arrayPolygon n ξ`: the linear interpolation of the partial sums, Donsker's `donskerProcess`
  without the `1/√n` normalization.
* `AldousCondition 𝓕 ξ μ`: Aldous's condition in the two-stopping-time form of Jacod–Shiryaev
  VI.4.5 (ii), for grid stopping times.

## Main results

* `isTightMeasureSet_of_modulus`: tightness in `C([0,1])` from a modulus-of-continuity bound
  for paths pinned at `0` (Billingsley 1999, Theorem 7.3).
* `isTightMeasureSet_arrayPolygon_of_aldousCondition` (**Aldous's criterion**): Aldous's
  condition plus asymptotically negligible jumps implies tightness of the polygons in
  `C([0,1])` (Jacod–Shiryaev VI.4.5 with VI.3.26).
* `aldousCondition_of_martingaleDifference`: a square-integrable martingale difference array
  whose predictable quadratic variation converges to `t` at every time satisfies Aldous's
  condition (Rebolledo's argument, Jacod–Shiryaev VI.4.13, through a discrete Lenglart bound).
* `tendsto_measure_exists_abs_gt_of_lindeberg`: Lindeberg implies negligible jumps.
* `tendstoInDistribution_arrayStepProcess` (**functional CLT for martingale arrays**):
  quadratic-variation convergence, Lindeberg, and the finite-dimensional convergence from T81
  (McLeish's CLT, an explicit hypothesis `hT81`) imply convergence of the step processes in the
  Skorokhod J1 topology on `D([0,1])`, through T43's transfer theorem
  `tendstoInDistribution_skorokhod_of_tight_of_fdd`.

## What is weakened or deferred

* **T81 is a hypothesis.** The finite-dimensional convergence of the step process to `Z`
  (McLeish's martingale CLT, roadmap task T81, not yet in the library) is the hypothesis `hT81`
  of `tendstoInDistribution_arrayStepProcess`. The limit `Z` is an arbitrary continuous
  process; it is Brownian motion exactly when `hT81` is McLeish's conclusion.
* **Aldous's criterion is proved in its continuous-limit form.** The conclusion is tightness of
  the polygons in `C([0,1])`, not tightness of the step processes in `D([0,1])`: T43's J1
  structure has no Prokhorov theory (completeness, separability, Arzelà–Ascoli for `D` are not
  available), so the general `D`-valued criterion (Jacod–Shiryaev VI.4.5 for processes with
  non-vanishing jumps) is not formalized. Under negligible jumps, `C`-tightness of the polygons
  is what T43's transfer theorem consumes.
* **Equally spaced time grid.** Row `n` has `n` increments at times `k/n`; general row lengths
  `k_n` and random time changes are not treated.
* **Unconditional Lindeberg.** Jump control uses `LindebergConditionTriangular`
  (`∑_i E[ξ n i² 1{|ξ n i| > ε}] → 0`), which implies the conditional Lindeberg condition used by
  Jacod–Shiryaev.
* The limit of the quadratic variation is the identity `t`; a general continuous increasing
  limit `A t` (limit `W ∘ A`) is not treated.

Sources: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), §§7, 18.
J. Jacod, A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer (2003),
§§I.3, VI.3, VI.4, VIII.3. D. Aldous, *Stopping times and tightness*, Ann. Probab. 6 (1978)
335–340. R. Rebolledo, *Central limit theorems for local martingales*, Z. Wahrsch. Verw. Gebiete
51 (1980) 269–286. D. L. McLeish, *Dependent central limit theorems and invariance principles*,
Ann. Probab. 2 (1974) 620–628.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open MathlibExt.Probability.DonskerWanted
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

variable {Ω : Type*}

/-! ### Step and polygonal paths of a triangular array -/

/-- The **step process** of a triangular array in `D([0,1])`: row `n` uses the increments
`ξ n 0, …, ξ n (n-1)` placed at times `1/n, …, 1`, so the path is
`t ↦ ∑_{i < ⌊n t⌋} ξ n i` (`arrayStepProcess_apply`). It is T43's `skorokhodStepProcess` with
the `1/√n` normalization undone, because an array row carries its own scaling. -/
def arrayStepProcess (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) : SkorokhodSpace 1 :=
  skorokhodStepProcess n (fun i ω => Real.sqrt n * ξ n i ω) ω

/-- Explicit partial-sum formula for `arrayStepProcess`. -/
theorem arrayStepProcess_apply (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) (t : Set.Icc (0 : ℝ) 1) :
    arrayStepProcess n ξ ω t = ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω := by
  rw [arrayStepProcess, skorokhodStepProcess_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hs]

/-- The **polygonal process** of a triangular array in `C([0,1])`: the linear interpolation of
the partial sums `k ↦ ∑_{i < k} ξ n i` at the grid times `k / n` (`arrayPolygon_apply`). It is
Donsker's `donskerProcess` with the `1/√n` normalization undone. -/
def arrayPolygon (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  donskerProcess n (fun i ω => Real.sqrt n * ξ n i ω) ω

/-- Explicit interpolation formula for `arrayPolygon`: the partial sum up to `⌊n t⌋` plus the
fractional part of the next increment. -/
theorem arrayPolygon_apply (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) (t : Set.Icc (0 : ℝ) 1) :
    arrayPolygon n ξ ω t = (∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω) +
      if ⌊(n : ℝ) * t.1⌋₊ < n then
        ξ n ⌊(n : ℝ) * t.1⌋₊ ω * ((n : ℝ) * t.1 - ⌊(n : ℝ) * t.1⌋₊) else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [arrayPolygon, donskerProcess]
  rw [arrayPolygon, donskerProcess_apply_eq _ _ _ _ hn.ne']
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [← Finset.mul_sum]
  split_ifs
  · field_simp
  · rw [add_zero, add_zero, mul_div_cancel_left₀ _ hs]

/-- The step process is a measurable `D([0,1])`-valued random variable. -/
theorem measurable_arrayStepProcess [MeasurableSpace Ω] (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ n i)) : Measurable (arrayStepProcess n ξ) :=
  measurable_skorokhodStepProcess n _ fun i => (hξ i).const_mul _

/-- The polygon is a measurable `C([0,1])`-valued random variable. -/
theorem measurable_arrayPolygon [MeasurableSpace Ω] (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ n i)) : Measurable (arrayPolygon n ξ) := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  simp_rw [arrayPolygon_apply]
  refine (Finset.measurable_sum _ fun i _ => hξ i).add ?_
  split_ifs
  · exact (hξ _).mul_const _
  · exact measurable_const

/-- The polygon starts at `0`. -/
theorem arrayPolygon_zero (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) :
    arrayPolygon n ξ ω ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  rw [arrayPolygon_apply]
  simp

/-- The polygon and the step path differ by at most the largest increment of the row. -/
theorem abs_arrayStepProcess_sub_arrayPolygon_le (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    {c : ℝ} (hc : 0 ≤ c) (hξ : ∀ i < n, |ξ n i ω| ≤ c) (t : Set.Icc (0 : ℝ) 1) :
    |arrayStepProcess n ξ ω t - arrayPolygon n ξ ω t| ≤ c := by
  rw [arrayStepProcess_apply, arrayPolygon_apply]
  split_ifs with h
  · have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
    have hf0 := Nat.zero_le_self_sub_floor ha0
    have hf1 := (Nat.self_sub_floor_lt_one ((n : ℝ) * t.1)).le
    rw [sub_add_cancel_left, abs_neg, abs_mul, abs_of_nonneg hf0]
    calc |ξ n _ ω| * _ ≤ c * 1 := mul_le_mul (hξ _ h) hf1 hf0 hc
      _ = c := mul_one c
  · simpa using hc

/-! ### Tightness in `C([0,1])` from a modulus-of-continuity bound -/

/- The helpers `isCompact_equicontinuous'`, `isCompact_closure_of_bounded_equicontinuous'`,
`compact_capture'`, `goodFamily` and `goodFamily_compact` are private copies (the last two
adapted) of the private Donsker lemmas `donsker_isCompact_equicontinuous` (`Donsker.lean:2229`),
`donsker_isCompact_closure_of_bounded_equicontinuous` (:2250), `donsker_compact_capture` (:2295),
`donskerGoodFamily` (:2343) and `donsker_good_family_compact` (:2350). Follow-up: make the Donsker
versions public and delete these copies. -/

private lemma isCompact_equicontinuous'
    {C : Set C(Set.Icc (0 : ℝ) 1, ℝ)} (hC : IsCompact C) :
    Equicontinuous ((↑) : C → Set.Icc (0 : ℝ) 1 → ℝ) := by
  have hcompact : IsCompact (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))) :=
    hC.prod isCompact_univ
  have heval : Continuous (fun p : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1 =>
      p.1 p.2) := continuous_eval
  have huc := hcompact.uniformContinuousOn_of_continuous heval.continuousOn
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  refine ⟨δ, hδ, fun y hy f => ?_⟩
  have hp : ((f.1, x) : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1) ∈
      C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := ⟨f.2, Set.mem_univ _⟩
  have hq : ((f.1, y) : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1) ∈
      C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := ⟨f.2, Set.mem_univ _⟩
  apply hcontrol (f.1, x) hp (f.1, y) hq
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  simpa only [dist_comm] using hy

private lemma isCompact_closure_of_bounded_equicontinuous'
    {A : Set C(Set.Icc (0 : ℝ) 1, ℝ)} {R : ℝ}
    (hbound : ∀ f ∈ A, ‖f‖ ≤ R)
    (hequi : Equicontinuous ((↑) : A → Set.Icc (0 : ℝ) 1 → ℝ)) :
    IsCompact (closure A) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ
  let D : Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) := e '' A
  have hin (g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
      (x : Set.Icc (0 : ℝ) 1) (hg : g ∈ D) : g x ∈ Metric.closedBall 0 R := by
    obtain ⟨f, hf, rfl⟩ := hg
    have hfx := (ContinuousMap.norm_coe_le_norm f x).trans (hbound f hf)
    change f x ∈ Metric.closedBall 0 R
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, Real.norm_eq_abs] using hfx
  let u : D → A := fun g => ⟨e.symm g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    have : e.symm g.1 = f := by
      calc
        e.symm g.1 = e.symm (e f) := congrArg e.symm hfg.symm
        _ = f := e.symm_apply_apply f
    rwa [this]⟩
  have hequiD : Equicontinuous ((↑) : D → Set.Icc (0 : ℝ) 1 → ℝ) := by
    have h := hequi.comp u
    have hfun :
        (fun g : D => fun x => (u g).1 x) = (fun g : D => fun x => g.1 x) := by
      funext g x
      rfl
    rw [← hfun]
    exact h
  have hD : IsCompact (closure D) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) R)
      (isCompact_closedBall (0 : ℝ) R) D hin hequiD
  have himage : e '' closure A = closure D := by
    have h := e.toHomeomorph.image_closure A
    change e '' closure A = closure (e '' A) at h
    simpa only [D] using h
  have heq : e.symm '' closure D = closure A := by
    rw [← himage]
    apply Set.Subset.antisymm
    · rintro f ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      simpa only [e.symm_apply_apply] using hg
    · intro f hf
      exact ⟨e f, ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩
  rw [← heq]
  exact hD.image e.symm.continuous

private lemma compact_capture' [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → C(Set.Icc (0 : ℝ) 1, ℝ)} (hW : Measurable W) {b : ℝ} (hb : 0 < b) :
    ∃ C : Set C(Set.Icc (0 : ℝ) 1, ℝ), IsCompact C ∧ P.real {ω | W ω ∉ C} ≤ b := by
  let _ : IsFiniteMeasure (P.map W) := P.isFiniteMeasure_map W
  have htight : IsTightMeasureSet {P.map W} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨C, hC, hbound⟩ := htight (ENNReal.ofReal b) (ENNReal.ofReal_pos.2 hb)
  refine ⟨C, hC, ?_⟩
  have hmap := hbound (P.map W) (Set.mem_singleton _)
  rw [Measure.map_apply_of_aemeasurable hW.aemeasurable hC.isClosed.measurableSet.compl] at hmap
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).2 hmap
  change (P (W ⁻¹' Cᶜ)).toReal ≤ b
  simpa only [ENNReal.toReal_ofReal hb.le] using hreal

/-- A continuous path on `[0,1]` vanishing at `0` whose increments over time gaps `≤ δ` are
`≤ 1` is bounded by `⌈1/δ⌉`: chain `m = ⌈1/δ⌉` steps of length `t/m ≤ δ` from `0` to `t`. -/
private lemma norm_le_of_modulus (f : C(Set.Icc (0 : ℝ) 1, ℝ))
    (hf0 : f ⟨0, le_rfl, zero_le_one⟩ = 0) {δ : ℝ} (hδ : 0 < δ)
    (hosc : ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ → dist (f s) (f t) ≤ 1) :
    ‖f‖ ≤ ⌈1 / δ⌉₊ := by
  refine (ContinuousMap.norm_le f (Nat.cast_nonneg _)).2 fun t => ?_
  set m := ⌈1 / δ⌉₊ with hm
  have hm0 : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  let p : ℕ → Set.Icc (0 : ℝ) 1 := fun k =>
    ⟨min ((k : ℝ) / m) 1 * t.1, mul_nonneg (le_min (by positivity) zero_le_one) t.2.1,
      by
        have := t.2.2
        have h1 : min ((k : ℝ) / m) 1 ≤ 1 := min_le_right _ _
        nlinarith [t.2.1, le_min (by positivity : (0 : ℝ) ≤ (k : ℝ) / m) zero_le_one]⟩
  have hp0 : p 0 = ⟨0, le_rfl, zero_le_one⟩ := by ext; simp [p]
  have hpm : p m = t := by ext; simp [p, div_self hmR.ne']
  have hstep : ∀ k, dist (p (k + 1)) (p k) ≤ δ := by
    intro k
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [p]
    have hδm : 1 / (m : ℝ) ≤ δ := by
      rw [div_le_iff₀ hmR]
      have := Nat.le_ceil (1 / δ)
      rw [← hm] at this
      calc (1 : ℝ) = (1 / δ) * δ := by field_simp
        _ ≤ m * δ := mul_le_mul_of_nonneg_right this hδ.le
        _ = δ * m := mul_comm _ _
    have hmono : min ((k : ℝ) / m) 1 ≤ min (((k + 1 : ℕ) : ℝ) / m) 1 :=
      min_le_min_right _ (div_le_div_of_nonneg_right (by push_cast; linarith) hmR.le)
    have hgap : min (((k + 1 : ℕ) : ℝ) / m) 1 - min ((k : ℝ) / m) 1 ≤ 1 / m := by
      have h1 : min (((k + 1 : ℕ) : ℝ) / m) 1 ≤ min ((k : ℝ) / m + 1 / m) 1 := by
        refine min_le_min_right _ (le_of_eq ?_); push_cast; ring
      have h2 : min ((k : ℝ) / m + 1 / m) 1 ≤ min ((k : ℝ) / m) 1 + 1 / m := by
        rcases le_total ((k : ℝ) / m) 1 with h | h
        · rw [min_eq_left h]; exact min_le_left _ _
        · rw [min_eq_right h]; exact (min_le_right _ _).trans (by simp)
      linarith
    rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hmono), abs_of_nonneg t.2.1]
    calc _ ≤ 1 / (m : ℝ) * 1 := mul_le_mul hgap t.2.2 t.2.1 (by positivity)
      _ ≤ δ := by rw [mul_one]; exact hδm
  have hchain : ∀ k, |f (p k)| ≤ k := by
    intro k
    induction k with
    | zero => simp [hp0, hf0]
    | succ k ih =>
      have := hosc _ _ (hstep k)
      rw [Real.dist_eq] at this
      push_cast
      calc |f (p (k + 1))| ≤ |f (p (k + 1)) - f (p k)| + |f (p k)| := by
            have := abs_add_le (f (p (k + 1)) - f (p k)) (f (p k))
            rwa [sub_add_cancel] at this
        _ ≤ 1 + k := add_le_add this ih
        _ = k + 1 := add_comm _ _
  have := hchain m
  rw [hpm] at this
  exact this

private def goodFamily (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ)) (δ : ℕ → ℝ) (N : ℕ → ℕ) :
    Set C(Set.Icc (0 : ℝ) 1, ℝ) :=
  {f | ∃ n, f ∈ C n ∧ f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
    ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j →
      dist (f s) (f t) < 1 / ((j : ℝ) + 1)}

private lemma goodFamily_compact (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ))
    (hC : ∀ n, IsCompact (C n)) (δ : ℕ → ℝ) (N : ℕ → ℕ) (hδ : ∀ j, 0 < δ j) :
    IsCompact (closure (goodFamily C δ N)) := by
  let CEarly : Set C(Set.Icc (0 : ℝ) 1, ℝ) := ⋃ n ∈ Finset.range (N 0), C n
  have hCEarly : IsCompact CEarly := (Finset.range (N 0)).isCompact_biUnion fun n _ => hC n
  obtain ⟨S, hS⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : C(Set.Icc (0 : ℝ) 1, ℝ))).mp hCEarly.isBounded
  have hbound (f : C(Set.Icc (0 : ℝ) 1, ℝ)) (hf : f ∈ goodFamily C δ N) :
      ‖f‖ ≤ max (⌈1 / δ 0⌉₊ : ℝ) S := by
    obtain ⟨n, hfn, hf0, hosc⟩ := hf
    by_cases hn : N 0 ≤ n
    · refine (norm_le_of_modulus f hf0 (hδ 0) fun s t hst => ?_).trans (le_max_left _ _)
      have := hosc 0 hn s t hst
      norm_num at this
      exact this.le
    · have hfearly : f ∈ CEarly :=
        Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (lt_of_not_ge hn), hfn⟩⟩
      have hfball := hS hfearly
      rw [Metric.mem_closedBall, dist_zero_right] at hfball
      exact hfball.trans (le_max_right _ _)
  have hequi : Equicontinuous ((↑) : goodFamily C δ N → Set.Icc (0 : ℝ) 1 → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    let CSmall : Set C(Set.Icc (0 : ℝ) 1, ℝ) := ⋃ n ∈ Finset.range (N j), C n
    have hCSmall : IsCompact CSmall := (Finset.range (N j)).isCompact_biUnion fun n _ => hC n
    have hearlyAt := isCompact_equicontinuous' hCSmall x
    rw [Metric.equicontinuousAt_iff] at hearlyAt
    obtain ⟨d, hd, hcontrol⟩ := hearlyAt ε hε
    refine ⟨min d (δ j), lt_min hd (hδ j), fun y hy f => ?_⟩
    obtain ⟨n, hfn, _, hosc⟩ := f.2
    by_cases hjn : N j ≤ n
    · have hxy : dist x y ≤ δ j := by
        rw [dist_comm]
        exact (hy.trans_le (min_le_right _ _)).le
      exact (hosc j hjn x y hxy).trans hj
    · have hfsmall : f.1 ∈ CSmall :=
        Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (lt_of_not_ge hjn), hfn⟩⟩
      exact hcontrol y (hy.trans_le (min_le_left _ _)) ⟨f.1, hfsmall⟩
  exact isCompact_closure_of_bounded_equicontinuous' hbound hequi

/-- **Tightness in `C([0,1])` from a modulus-of-continuity bound** (Billingsley 1999,
Theorem 7.3, with the paths pinned at `0`). If every `W n` vanishes at time `0` and, for all
`ε, b > 0`, there is `δ > 0` such that eventually
`P(∃ s t, |s - t| ≤ δ, |W n s - W n t| ≥ ε) ≤ b`, then the laws of `W n` are tight.

The proof is Arzelà–Ascoli: the paths outside a small exceptional set lie in a closed
uniformly bounded equicontinuous family (the bound comes from chaining the modulus from `0`),
and the finitely many early laws are tight individually because `C([0,1])` is Polish. -/
theorem isTightMeasureSet_of_modulus [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : ℕ → Ω → C(Set.Icc (0 : ℝ) 1, ℝ))
    (hW : ∀ n, Measurable (W n)) (hzero : ∀ n ω, W n ω ⟨0, le_rfl, zero_le_one⟩ = 0)
    (hosc : ∀ ε : ℝ, 0 < ε → ∀ b : ℝ, 0 < b → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ ∧ ε ≤ dist (W n ω s) (W n ω t)} ≤
        b) :
    IsTightMeasureSet (Set.range fun n => P.map (W n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ζ hζ
  by_cases hζtop : ζ = ∞
  · exact ⟨∅, isCompact_empty, by simp only [hζtop, le_top, implies_true]⟩
  set b := ζ.toReal with hb_def
  have hb : 0 < b := ENNReal.toReal_pos hζ.ne' hζtop
  have hcapture (n : ℕ) : ∃ C : Set C(Set.Icc (0 : ℝ) 1, ℝ), IsCompact C ∧
      P.real {ω | W n ω ∉ C} ≤ b / 2 :=
    compact_capture' (hW n) (div_pos hb (by norm_num))
  choose C hC hCprob using hcapture
  have hdata (j : ℕ) : ∃ δ > 0, ∃ N : ℕ, j ≤ N ∧ ∀ n, N ≤ n →
      P.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ ∧
        1 / ((j : ℝ) + 1) ≤ dist (W n ω s) (W n ω t)} ≤ b / 4 * (1 / 2 : ℝ) ^ j := by
    obtain ⟨δ, hδ, hev⟩ := hosc (1 / ((j : ℝ) + 1)) (by positivity)
      (b / 4 * (1 / 2 : ℝ) ^ j) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨δ, hδ, max N j, le_max_right _ _, fun n hn => hN n ((le_max_left _ _).trans hn)⟩
  choose δ hδ N hjN hprob using hdata
  let K := closure (goodFamily C δ N)
  have hK : IsCompact K := goodFamily_compact C hC δ N hδ
  refine ⟨K, hK, ?_⟩
  rintro μ ⟨n, rfl⟩
  let oscFail : ℕ → Set Ω := fun j =>
    {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j ∧
      1 / ((j : ℝ) + 1) ≤ dist (W n ω s) (W n ω t)}
  let J := (Finset.range (n + 1)).filter fun j => N j ≤ n
  have hpre : W n ⁻¹' Kᶜ ⊆ {ω | W n ω ∉ C n} ∪ ⋃ j ∈ J, oscFail j := by
    intro ω hω
    by_cases hCω : W n ω ∈ C n
    · by_cases hoscω : ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1,
          dist s t ≤ δ j → dist (W n ω s) (W n ω t) < 1 / ((j : ℝ) + 1)
      · exact absurd (subset_closure (show W n ω ∈ goodFamily C δ N from
          ⟨n, hCω, hzero n ω, hoscω⟩)) hω
      · push Not at hoscω
        obtain ⟨j, hjn, s, t, hst, hbad⟩ := hoscω
        have hjJ : j ∈ J := by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le ((hjN j).trans hjn), hjn⟩
        exact Or.inr (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjJ, s, t, hst, hbad⟩⟩)
    · exact Or.inl hCω
  have hoscUnion : P.real (⋃ j ∈ J, oscFail j) ≤ b / 2 := by
    calc P.real (⋃ j ∈ J, oscFail j) ≤ ∑ j ∈ J, P.real (oscFail j) :=
          measureReal_biUnion_finset_le J oscFail
      _ ≤ ∑ j ∈ J, b / 4 * (1 / 2 : ℝ) ^ j :=
          Finset.sum_le_sum fun j hj => hprob j n (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.range (n + 1), b / 4 * (1 / 2 : ℝ) ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => by positivity
      _ = b / 4 * ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ b / 4 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = b / 2 := by ring
  have hreal : P.real (W n ⁻¹' Kᶜ) ≤ b :=
    calc P.real (W n ⁻¹' Kᶜ) ≤ P.real ({ω | W n ω ∉ C n} ∪ ⋃ j ∈ J, oscFail j) :=
          measureReal_mono hpre (measure_ne_top P _)
      _ ≤ P.real {ω | W n ω ∉ C n} + P.real (⋃ j ∈ J, oscFail j) := measureReal_union_le _ _
      _ ≤ b / 2 + b / 2 := add_le_add (hCprob n) hoscUnion
      _ = b := by ring
  rw [Measure.map_apply_of_aemeasurable (hW n).aemeasurable hK.isClosed.measurableSet.compl]
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) hζtop).1
  simpa only [measureReal_def, b] using hreal

/-! ### Oscillation times of a discrete path -/

open scoped Classical in
/-- First index `j ∈ (a, n]` at which the path `s` is more than `ε` away from `s a`, or `n` if
there is none. -/
private def exitIndex (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (a : ℕ) : ℕ :=
  if h : ∃ j, a < j ∧ j ≤ n ∧ ε < |s j - s a| then Nat.find h else n

/-- The successive `ε`-oscillation times `0 = τ 0 ≤ τ 1 ≤ ⋯ ≤ n` of the path `s`. -/
private def oscTime (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => exitIndex s n ε (oscTime s n ε k)

private lemma exitIndex_le (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (a : ℕ) : exitIndex s n ε a ≤ n := by
  unfold exitIndex
  split_ifs with h
  · exact (Nat.find_spec h).2.1
  · exact le_rfl

private lemma lt_exitIndex (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) {a : ℕ} (ha : a < n) :
    a < exitIndex s n ε a := by
  unfold exitIndex
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact ha

private lemma le_exitIndex (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) {a : ℕ} (ha : a ≤ n) :
    a ≤ exitIndex s n ε a := by
  rcases ha.lt_or_eq with ha | rfl
  · exact (lt_exitIndex s n ε ha).le
  · unfold exitIndex
    split_ifs with h
    · exact (Nat.find_spec h).1.le
    · exact le_rfl

private lemma abs_sub_le_of_lt_exitIndex (s : ℕ → ℝ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) {a j : ℕ}
    (haj : a ≤ j) (hj : j < exitIndex s n ε a) : |s j - s a| ≤ ε := by
  rcases haj.lt_or_eq with haj | rfl
  · by_contra hcon
    push Not at hcon
    unfold exitIndex at hj
    split_ifs at hj with h
    · exact absurd hj (not_lt.2 (Nat.find_min' h ⟨haj, hj.le.trans (Nat.find_spec h).2.1, hcon⟩))
    · exact h ⟨j, haj, hj.le, hcon⟩
  · simpa using hε

private lemma lt_abs_sub_of_exitIndex_lt (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (a : ℕ)
    (h : exitIndex s n ε a < n) : ε < |s (exitIndex s n ε a) - s a| := by
  unfold exitIndex at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Nat.find_spec hex).2.2
  · exact absurd h (lt_irrefl n)

private lemma exitIndex_le_iff (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (a i : ℕ) :
    exitIndex s n ε a ≤ i ↔ n ≤ i ∨ ∃ j, a < j ∧ j ≤ i ∧ j ≤ n ∧ ε < |s j - s a| := by
  constructor
  · intro hle
    unfold exitIndex at hle
    split_ifs at hle with h
    · exact Or.inr ⟨Nat.find h, (Nat.find_spec h).1, hle, (Nat.find_spec h).2⟩
    · exact Or.inl hle
  · rintro (hn | ⟨j, haj, hji, hjn, hj⟩)
    · exact (exitIndex_le s n ε a).trans hn
    · unfold exitIndex
      split_ifs with h
      · exact (Nat.find_min' h ⟨haj, hjn, hj⟩).trans hji
      · exact absurd ⟨j, haj, hjn, hj⟩ h

/-- Within one oscillation block, including its right end, the path moves at most `2ε` when
all single steps are at most `ε`. -/
private lemma abs_sub_le_of_le_exitIndex (s : ℕ → ℝ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hjump : ∀ j < n, |s (j + 1) - s j| ≤ ε) {a j : ℕ} (haj : a ≤ j)
    (hj : j ≤ exitIndex s n ε a) : |s j - s a| ≤ 2 * ε := by
  rcases hj.lt_or_eq with hj | hj
  · linarith [abs_sub_le_of_lt_exitIndex s n hε haj hj]
  · rcases haj.lt_or_eq with haj' | rfl
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj'n : j' < n := by have := exitIndex_le s n ε a; omega
      have h1 := hjump j' hj'n
      have h2 := abs_sub_le_of_lt_exitIndex s n hε (show a ≤ j' by omega) (by omega)
      calc |s (j' + 1) - s a| = |(s (j' + 1) - s j') + (s j' - s a)| := by ring_nf
        _ ≤ |s (j' + 1) - s j'| + |s j' - s a| := abs_add_le _ _
        _ ≤ 2 * ε := by linarith
    · simp; linarith

private lemma oscTime_le (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (k : ℕ) : oscTime s n ε k ≤ n := by
  cases k with
  | zero => exact Nat.zero_le n
  | succ k => exact exitIndex_le s n ε _

private lemma oscTime_succ (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (k : ℕ) :
    oscTime s n ε (k + 1) = exitIndex s n ε (oscTime s n ε k) := rfl

private lemma oscTime_le_succ (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (k : ℕ) :
    oscTime s n ε k ≤ oscTime s n ε (k + 1) :=
  le_exitIndex s n ε (oscTime_le s n ε k)

private lemma oscTime_mono (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) : Monotone (oscTime s n ε) :=
  monotone_nat_of_le_succ (oscTime_le_succ s n ε)

/-- **Deterministic core of Aldous's criterion.** If the single steps of `s` are at most `ε`,
the first `q` oscillation times exhaust `[0, n]`, and every genuine oscillation block (one
ending before `n`) is longer than `L`, then `s` moves at most `5ε` over any index window of
length `L`. -/
private lemma abs_sub_le_of_oscTime (s : ℕ → ℝ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (L q : ℕ)
    (hjump : ∀ j < n, |s (j + 1) - s j| ≤ ε)
    (hgap : ∀ k < q, oscTime s n ε (k + 1) < n →
      oscTime s n ε k + L < oscTime s n ε (k + 1))
    (hq : oscTime s n ε q = n) {j j' : ℕ} (hjj' : j ≤ j') (hj'L : j' ≤ j + L) (hj'n : j' ≤ n) :
    |s j' - s j| ≤ 5 * ε := by
  set τ := oscTime s n ε with hτ
  rcases (show j ≤ n by omega).lt_or_eq with hjn | rfl
  swap
  · have : j' = j := by omega
    subst this; simp; linarith
  have hex : ∃ k, j < τ k := ⟨q, by omega⟩
  set k0 := Nat.find hex with hk0
  have hk0spec : j < τ k0 := Nat.find_spec hex
  have hk0pos : k0 ≠ 0 := by
    intro h
    rw [h] at hk0spec
    simp [τ, oscTime] at hk0spec
  obtain ⟨k, hk⟩ : ∃ k, k0 = k + 1 := ⟨k0 - 1, by omega⟩
  have hkj : τ k ≤ j := by
    by_contra h
    exact Nat.find_min hex (show k < k0 by omega) (not_le.1 h)
  have hjk1 : j < τ (k + 1) := hk ▸ hk0spec
  have hτkn : τ k ≤ n := oscTime_le s n ε k
  have h1 : |s j - s (τ k)| ≤ ε :=
    abs_sub_le_of_lt_exitIndex s n hε hkj (by rw [← oscTime_succ]; exact hjk1)
  by_cases hj'k : j' ≤ τ (k + 1)
  · have h2 := abs_sub_le_of_le_exitIndex s n hε hjump (hkj.trans hjj')
      (by rw [← oscTime_succ]; exact hj'k)
    calc |s j' - s j| = |(s j' - s (τ k)) - (s j - s (τ k))| := by ring_nf
      _ ≤ |s j' - s (τ k)| + |s j - s (τ k)| := abs_sub _ _
      _ ≤ 5 * ε := by linarith
  · push Not at hj'k
    have hk1n : τ (k + 1) < n := by omega
    have hk1q : k + 1 < q := by
      by_contra h
      have := oscTime_mono s n ε (show q ≤ k + 1 by omega)
      rw [← hτ, hq] at this
      omega
    have hj'k2 : j' ≤ τ (k + 1 + 1) := by
      rcases (oscTime_le s n ε (k + 1 + 1)).lt_or_eq with h | h
      · have := hgap (k + 1) hk1q h
        omega
      · rw [hτ, h]; exact hj'n
    have h2 := abs_sub_le_of_le_exitIndex s n hε hjump hj'k.le
      (by rw [← oscTime_succ]; exact hj'k2)
    have h3 := abs_sub_le_of_le_exitIndex s n hε hjump (oscTime_le_succ s n ε k) le_rfl
    calc |s j' - s j| = |(s j' - s (τ (k + 1))) + (s (τ (k + 1)) - s (τ k)) -
          (s j - s (τ k))| := by ring_nf
      _ ≤ |s j' - s (τ (k + 1))| + |s (τ (k + 1)) - s (τ k)| + |s j - s (τ k)| :=
          (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ 5 * ε := by linarith

/-- **Counting short blocks.** If the `q`-th oscillation time is still before `n` and
`2n ≤ q (L + 1)`, then at least half of the first `q` blocks have length at most `L`: the
blocks longer than `L` have total length below `n`. -/
private lemma le_two_mul_card_short (s : ℕ → ℝ) (n : ℕ) (ε : ℝ) (L q : ℕ)
    (hq : oscTime s n ε q < n) (hqL : 2 * n ≤ q * (L + 1)) :
    q ≤ 2 * ((Finset.range q).filter
      fun k => oscTime s n ε (k + 1) ≤ oscTime s n ε k + L).card := by
  set τ := oscTime s n ε
  set A := (Finset.range q).filter fun k => τ (k + 1) ≤ τ k + L
  set B := (Finset.range q).filter fun k => τ k + L < τ (k + 1)
  have hcard : A.card + B.card = q := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range q)
      (p := fun k => τ (k + 1) ≤ τ k + L)
    simp only [Finset.card_range, not_le] at this
    exact this
  have hsum : ∑ k ∈ Finset.range q, (τ (k + 1) - τ k) = τ q := by
    rw [Finset.sum_range_tsub (oscTime_mono s n ε)]
    simp [τ, oscTime]
  have hB : B.card * (L + 1) ≤ τ q := by
    rw [← hsum]
    calc B.card * (L + 1) = ∑ _k ∈ B, (L + 1) := by simp
      _ ≤ ∑ k ∈ B, (τ (k + 1) - τ k) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have := (Finset.mem_filter.1 hk).2
          omega
      _ ≤ ∑ k ∈ Finset.range q, (τ (k + 1) - τ k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
            Nat.zero_le _
  have h1 : 2 * (B.card * (L + 1)) < q * (L + 1) := by omega
  have h2 : 2 * B.card < q := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul_right (L + 1) h
    rw [mul_assoc] at this
    omega
  omega

/-! ### Discrete stopping times -/

/-- An `ℕ`-valued random time, viewed in `WithTop ℕ`, is a stopping time iff each `{σ ≤ i}` is
`f i`-measurable. -/
theorem isStoppingTime_natCast_iff {m : MeasurableSpace Ω} {f : Filtration ℕ m} {σ : Ω → ℕ} :
    IsStoppingTime f (fun ω => (σ ω : WithTop ℕ)) ↔ ∀ i, MeasurableSet[f i] {ω | σ ω ≤ i} := by
  simp only [IsStoppingTime, Nat.cast_withTop, WithTop.coe_le_coe]

private lemma measurableSet_eq_of_natCast {m : MeasurableSpace Ω} {f : Filtration ℕ m}
    {σ : Ω → ℕ} (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℕ))) (i : ℕ) :
    MeasurableSet[f i] {ω | σ ω = i} := by
  have := hσ.measurableSet_eq i
  simpa only [Nat.cast_withTop, WithTop.coe_eq_coe] using this

private lemma measurable_of_natCast {m : MeasurableSpace Ω} {f : Filtration ℕ m}
    {σ : Ω → ℕ} (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℕ))) : Measurable[m] σ :=
  measurable_to_countable' fun i => f.le i _ (measurableSet_eq_of_natCast hσ i)

private lemma isStoppingTime_natCast_min {m : MeasurableSpace Ω} {f : Filtration ℕ m}
    {σ ρ : Ω → ℕ} (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℕ)))
    (hρ : IsStoppingTime f (fun ω => (ρ ω : WithTop ℕ))) :
    IsStoppingTime f (fun ω => ((min (σ ω) (ρ ω) : ℕ) : WithTop ℕ)) := by
  rw [isStoppingTime_natCast_iff] at *
  intro i
  have : {ω | min (σ ω) (ρ ω) ≤ i} = {ω | σ ω ≤ i} ∪ {ω | ρ ω ≤ i} := by
    ext ω; simp [min_le_iff]
  rw [this]
  exact (hσ i).union (hρ i)

private lemma isStoppingTime_natCast_add_const {m : MeasurableSpace Ω} {f : Filtration ℕ m}
    {σ : Ω → ℕ} (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℕ))) (L : ℕ) :
    IsStoppingTime f (fun ω => ((σ ω + L : ℕ) : WithTop ℕ)) := by
  rw [isStoppingTime_natCast_iff] at *
  intro i
  by_cases hL : L ≤ i
  · have : {ω | σ ω + L ≤ i} = {ω | σ ω ≤ i - L} := by ext ω; simp; omega
    rw [this]
    exact f.mono (Nat.sub_le i L) _ (hσ (i - L))
  · have : {ω | σ ω + L ≤ i} = ∅ := by ext ω; simp; omega
    rw [this]
    exact @MeasurableSet.empty _ (f i)

/-! ### Aldous's condition -/

/-- **Aldous's condition** for the partial sums `S n k = ∑_{i < k} ξ n i` of a triangular array,
row `n` filtered by `𝓕 n` and observed at the times `k / n`: for every `ε, η > 0` there is a
window `θ > 0` such that, for all large `n` and all pairs of `𝓕 n`-stopping times
`σ ≤ ρ ≤ σ + nθ` (with `ρ ≤ n`), `P(|S n ρ - S n σ| ≥ ε) ≤ η`.

This is the two-stopping-time form of Aldous's condition in Jacod–Shiryaev, *Limit Theorems
for Stochastic Processes*, 2nd ed. (2003), Theorem VI.4.5 (ii):
`lim_{θ↓0} limsup_n sup_{S ≤ T ≤ S + θ} P(|X^n_T - X^n_S| ≥ ε) = 0`, written for the grid
stopping times of the step process `t ↦ S n ⌊n t⌋` on the horizon `[0, 1]`. Aldous's original
form (D. Aldous, *Stopping times and tightness*, Ann. Probab. 6 (1978) 335–340) has a
deterministic shift `δ_n → 0` after one stopping time; the two-stopping-time form is the one
used to prove tightness. -/
def AldousCondition {m : MeasurableSpace Ω} (𝓕 : ℕ → Filtration ℕ m) (ξ : ℕ → ℕ → Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ σ ρ : Ω → ℕ, IsStoppingTime (𝓕 n) (fun ω => (σ ω : WithTop ℕ)) →
      IsStoppingTime (𝓕 n) (fun ω => (ρ ω : WithTop ℕ)) →
      (∀ ω, σ ω ≤ ρ ω ∧ ρ ω ≤ σ ω + ⌊(n : ℝ) * θ⌋₊ ∧ ρ ω ≤ n) →
      μ {ω | ε ≤ |∑ i ∈ Finset.range (ρ ω), ξ n i ω - ∑ i ∈ Finset.range (σ ω), ξ n i ω|} ≤
        ENNReal.ofReal η

private lemma measurable_partialSum {m : MeasurableSpace Ω} {f : Filtration ℕ m}
    {x : ℕ → Ω → ℝ} (hx : ∀ i, Measurable[f (i + 1)] (x i)) {k i : ℕ} (hki : k ≤ i) :
    Measurable[f i] (fun ω => ∑ l ∈ Finset.range k, x l ω) := by
  refine Finset.measurable_sum _ fun l hl => ?_
  exact (hx l).mono (f.mono (by simp at hl; omega)) le_rfl

/-- The oscillation times of the partial-sum path of an adapted row are stopping times. -/
private lemma isStoppingTime_oscTime {m : MeasurableSpace Ω} {f : Filtration ℕ m}
    {x : ℕ → Ω → ℝ} (hx : ∀ i, Measurable[f (i + 1)] (x i)) (n : ℕ) (ε : ℝ) (k : ℕ) :
    IsStoppingTime f
      (fun ω => (oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε k : WithTop ℕ)) := by
  induction k with
  | zero =>
    rw [isStoppingTime_natCast_iff]
    intro i
    simp only [oscTime, Nat.zero_le, Set.ofPred_true]
    exact @MeasurableSet.univ _ (f i)
  | succ k ih =>
    rw [isStoppingTime_natCast_iff]
    intro i
    set S : ℕ → Ω → ℝ := fun j ω => ∑ l ∈ Finset.range j, x l ω with hS
    have hset : {ω | oscTime (fun j => S j ω) n ε (k + 1) ≤ i} =
        {_ω | n ≤ i} ∪ ⋃ a ∈ Finset.range (i + 1), ⋃ j ∈ Finset.range (i + 1),
          ({ω | oscTime (fun j => S j ω) n ε k = a} ∩ ({_ω | a < j ∧ j ≤ n} ∩
            (fun ω => |S j ω - S a ω|) ⁻¹' Set.Ioi ε)) := by
      ext ω
      simp only [oscTime_succ, exitIndex_le_iff, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi,
        exists_prop]
      constructor
      · rintro (h | ⟨j, haj, hji, hjn, hj⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, by omega, j, by omega, rfl, ⟨haj, hjn⟩, hj⟩
      · rintro (h | ⟨a, _, j, _, rfl, ⟨haj, hjn⟩, hj⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, haj, by omega, hjn, hj⟩
    rw [hset]
    refine (MeasurableSet.const _).union ?_
    refine Finset.measurableSet_biUnion _ fun a ha => Finset.measurableSet_biUnion _ fun j hj => ?_
    simp only [Finset.mem_range] at ha hj
    refine MeasurableSet.inter ?_ ((MeasurableSet.const _).inter ?_)
    · exact f.mono (show a ≤ i by omega) _ (measurableSet_eq_of_natCast ih a)
    · have hmeas : Measurable[f i] (fun ω => |S j ω - S a ω|) :=
        continuous_abs.measurable.comp ((measurable_partialSum hx (show j ≤ i by omega)).sub
          (measurable_partialSum hx (show a ≤ i by omega)))
      exact hmeas measurableSet_Ioi

/-- One short genuine oscillation block is an increment over a stopping-time window of length
`L`, so its probability is controlled by the row's Aldous bound. -/
private lemma measure_shortBlock_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Filtration ℕ m} {x : ℕ → Ω → ℝ} (hx : ∀ i, Measurable[f (i + 1)] (x i))
    (n : ℕ) (ε : ℝ) (L : ℕ) (η : ℝ≥0∞)
    (hA : ∀ σ ρ : Ω → ℕ, IsStoppingTime f (fun ω => (σ ω : WithTop ℕ)) →
      IsStoppingTime f (fun ω => (ρ ω : WithTop ℕ)) →
      (∀ ω, σ ω ≤ ρ ω ∧ ρ ω ≤ σ ω + L ∧ ρ ω ≤ n) →
      μ {ω | ε ≤ |∑ i ∈ Finset.range (ρ ω), x i ω - ∑ i ∈ Finset.range (σ ω), x i ω|} ≤ η)
    (k : ℕ) :
    μ {ω | oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε (k + 1) < n ∧
      oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε (k + 1) ≤
        oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε k + L} ≤ η := by
  set τ : ℕ → Ω → ℕ := fun k ω => oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε k
    with hτ
  have hst := isStoppingTime_oscTime hx n ε
  refine le_trans (measure_mono ?_) (hA (τ k) (fun ω => min (τ (k + 1) ω) (τ k ω + L))
    (hst k) (isStoppingTime_natCast_min (hst (k + 1)) (isStoppingTime_natCast_add_const
      (hst k) L)) fun ω => ⟨le_min (oscTime_le_succ _ n ε k) (Nat.le_add_right _ _),
        min_le_right _ _, (min_le_left _ _).trans (oscTime_le _ n ε _)⟩)
  intro ω ⟨hlt, hle⟩
  simp only [Set.mem_ofPred_eq]
  rw [min_eq_left hle]
  exact (lt_abs_sub_of_exitIndex_lt _ n ε _ hlt).le

/-- **The number of oscillations is controlled.** If `2n ≤ q (L + 1)` and every short genuine
block has probability at most `η`, the `q`-th oscillation time falls before `n` with
probability at most `2η` (Markov's inequality on the number of short blocks). -/
private lemma measure_oscTime_lt_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Filtration ℕ m} {x : ℕ → Ω → ℝ} (hx : ∀ i, Measurable[f (i + 1)] (x i))
    (n : ℕ) (ε : ℝ) (L q : ℕ) (hq : 0 < q) (hqL : 2 * n ≤ q * (L + 1)) (η : ℝ≥0∞)
    (hB : ∀ k, μ {ω | oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε (k + 1) < n ∧
      oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε (k + 1) ≤
        oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε k + L} ≤ η) :
    μ {ω | oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε q < n} ≤ 2 * η := by
  set τ : ℕ → Ω → ℕ := fun k ω => oscTime (fun j => ∑ l ∈ Finset.range j, x l ω) n ε k
    with hτ
  have hmeas : ∀ k, Measurable (τ k) := fun k =>
    measurable_of_natCast (isStoppingTime_oscTime hx n ε k)
  set B : ℕ → Set Ω := fun k => {ω | τ (k + 1) ω < n ∧ τ (k + 1) ω ≤ τ k ω + L} with hB_def
  have hBmeas : ∀ k, MeasurableSet (B k) := fun k =>
    (measurableSet_lt (hmeas (k + 1)) measurable_const).inter
      (measurableSet_le (hmeas (k + 1)) ((hmeas k).add_const L))
  set F : Ω → ℝ≥0∞ := fun ω => ∑ k ∈ Finset.range q, (B k).indicator 1 ω with hF
  have hFmeas : Measurable F :=
    Finset.measurable_sum _ fun k _ => measurable_const.indicator (hBmeas k)
  have hsub : {ω | τ q ω < n} ⊆ {ω | (q : ℝ≥0∞) ≤ 2 * F ω} := by
    intro ω hω
    have h := le_two_mul_card_short (fun j => ∑ l ∈ Finset.range j, x l ω) n ε L q hω hqL
    have hcard : (((Finset.range q).filter fun k => τ (k + 1) ω ≤ τ k ω + L).card : ℝ≥0∞) =
        F ω := by
      simp only [hF, Set.indicator_apply, Pi.one_apply]
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : τ (k + 1) ω < n := lt_of_le_of_lt
        (oscTime_mono _ n ε (show k + 1 ≤ q by simp at hk; omega)) hω
      simp only [hB_def, Set.mem_ofPred_eq, hk1, true_and]
    simp only [Set.mem_ofPred_eq]
    rw [← hcard]
    exact_mod_cast h
  calc μ {ω | τ q ω < n} ≤ μ {ω | (q : ℝ≥0∞) ≤ 2 * F ω} := measure_mono hsub
    _ ≤ (∫⁻ ω, 2 * F ω ∂μ) / q :=
        meas_ge_le_lintegral_div (hFmeas.const_mul 2).aemeasurable
          (by exact_mod_cast hq.ne') (ENNReal.natCast_ne_top q)
    _ ≤ 2 * η := by
        refine ENNReal.div_le_of_le_mul ?_
        have hint : ∫⁻ ω, F ω ∂μ = ∑ k ∈ Finset.range q, μ (B k) := by
          rw [hF, lintegral_finsetSum (f := fun k ω => (B k).indicator 1 ω) _ fun k _ =>
            measurable_const.indicator (hBmeas k)]
          exact Finset.sum_congr rfl fun k _ => lintegral_indicator_one (hBmeas k)
        rw [lintegral_const_mul _ hFmeas, hint]
        calc 2 * ∑ k ∈ Finset.range q, μ (B k) ≤ 2 * ∑ _k ∈ Finset.range q, η := by
              gcongr with k; exact hB k
          _ = 2 * η * q := by simp; ring

/-- On a good path (few oscillations, long genuine blocks, small steps) the polygon has small
continuous-time oscillation. -/
private lemma dist_arrayPolygon_le (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) {ε δ δ' : ℝ}
    (hε : 0 ≤ ε) (q : ℕ) (hδ : (n : ℝ) * δ + 1 ≤ n * δ')
    (hjump : ∀ i < n, |ξ n i ω| ≤ ε)
    (hgap : ∀ k < q, oscTime (fun j => ∑ l ∈ Finset.range j, ξ n l ω) n ε (k + 1) < n →
      oscTime (fun j => ∑ l ∈ Finset.range j, ξ n l ω) n ε k + ⌊(n : ℝ) * δ'⌋₊ <
        oscTime (fun j => ∑ l ∈ Finset.range j, ξ n l ω) n ε (k + 1))
    (hq : oscTime (fun j => ∑ l ∈ Finset.range j, ξ n l ω) n ε q = n)
    (s t : Set.Icc (0 : ℝ) 1) (hst : dist s t ≤ δ) :
    dist (arrayPolygon n ξ ω s) (arrayPolygon n ξ ω t) ≤ 7 * ε := by
  set S : ℕ → ℝ := fun j => ∑ l ∈ Finset.range j, ξ n l ω with hS
  have hstep : ∀ j < n, |S (j + 1) - S j| ≤ ε := by
    intro j hj
    simp only [hS, Finset.sum_range_succ, add_sub_cancel_left]
    exact hjump j hj
  have hpoly : ∀ u : Set.Icc (0 : ℝ) 1, |arrayPolygon n ξ ω u - S ⌊(n : ℝ) * u.1⌋₊| ≤ ε := by
    intro u
    have := abs_arrayStepProcess_sub_arrayPolygon_le n ξ ω hε hjump u
    rw [arrayStepProcess_apply, abs_sub_comm] at this
    exact this
  have hfloor_le : ∀ u : Set.Icc (0 : ℝ) 1, ⌊(n : ℝ) * u.1⌋₊ ≤ n := fun u =>
    Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_left u.2.2 (Nat.cast_nonneg n))
  have key : ∀ u v : Set.Icc (0 : ℝ) 1, dist u v ≤ δ →
      ⌊(n : ℝ) * u.1⌋₊ ≤ ⌊(n : ℝ) * v.1⌋₊ →
      |S ⌊(n : ℝ) * v.1⌋₊ - S ⌊(n : ℝ) * u.1⌋₊| ≤ 5 * ε := by
    intro u v huv hle
    refine abs_sub_le_of_oscTime S n hε _ q hstep hgap hq hle ?_ (hfloor_le v)
    have hu0 : 0 ≤ (n : ℝ) * u.1 := mul_nonneg (Nat.cast_nonneg n) u.2.1
    have hv0 : 0 ≤ (n : ℝ) * v.1 := mul_nonneg (Nat.cast_nonneg n) v.2.1
    have h1 : ((⌊(n : ℝ) * v.1⌋₊ : ℕ) : ℝ) ≤ n * v.1 := Nat.floor_le hv0
    have h2 : (n : ℝ) * u.1 < ⌊(n : ℝ) * u.1⌋₊ + 1 := Nat.lt_floor_add_one _
    have h3 : v.1 - u.1 ≤ δ := by
      rw [Subtype.dist_eq, Real.dist_eq] at huv
      exact (le_abs_self _).trans (by rw [abs_sub_comm]; exact huv)
    have h4 : (n : ℝ) * (v.1 - u.1) ≤ n * δ := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
    have h5 : ((⌊(n : ℝ) * v.1⌋₊ - ⌊(n : ℝ) * u.1⌋₊ : ℕ) : ℝ) ≤ n * δ' := by
      rw [Nat.cast_sub hle]
      nlinarith
    have h6 := Nat.le_floor h5
    omega
  rw [Real.dist_eq]
  rcases le_total ⌊(n : ℝ) * s.1⌋₊ ⌊(n : ℝ) * t.1⌋₊ with h | h
  · have hk := key s t hst h
    have hs := hpoly s
    have ht := hpoly t
    calc |arrayPolygon n ξ ω s - arrayPolygon n ξ ω t|
        = |(arrayPolygon n ξ ω s - S ⌊(n : ℝ) * s.1⌋₊) -
            (S ⌊(n : ℝ) * t.1⌋₊ - S ⌊(n : ℝ) * s.1⌋₊) -
            (arrayPolygon n ξ ω t - S ⌊(n : ℝ) * t.1⌋₊)| := by ring_nf
      _ ≤ |arrayPolygon n ξ ω s - S ⌊(n : ℝ) * s.1⌋₊| +
            |S ⌊(n : ℝ) * t.1⌋₊ - S ⌊(n : ℝ) * s.1⌋₊| +
            |arrayPolygon n ξ ω t - S ⌊(n : ℝ) * t.1⌋₊| :=
          (abs_sub _ _).trans (by gcongr; exact abs_sub _ _)
      _ ≤ 7 * ε := by linarith
  · have hk := key t s (by rw [dist_comm]; exact hst) h
    have hs := hpoly s
    have ht := hpoly t
    calc |arrayPolygon n ξ ω s - arrayPolygon n ξ ω t|
        = |(arrayPolygon n ξ ω s - S ⌊(n : ℝ) * s.1⌋₊) +
            (S ⌊(n : ℝ) * s.1⌋₊ - S ⌊(n : ℝ) * t.1⌋₊) -
            (arrayPolygon n ξ ω t - S ⌊(n : ℝ) * t.1⌋₊)| := by ring_nf
      _ ≤ |arrayPolygon n ξ ω s - S ⌊(n : ℝ) * s.1⌋₊| +
            |S ⌊(n : ℝ) * s.1⌋₊ - S ⌊(n : ℝ) * t.1⌋₊| +
            |arrayPolygon n ξ ω t - S ⌊(n : ℝ) * t.1⌋₊| :=
          (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ 7 * ε := by linarith

/-- **Aldous's tightness criterion** (continuous-limit form, for triangular arrays).

Let row `n` of the array `ξ` be adapted to the filtration `𝓕 n` (`ξ n i` is
`𝓕 n (i + 1)`-measurable). If the largest increment of row `n` tends to `0` in probability and
the partial sums satisfy Aldous's condition (`AldousCondition`), then the laws of the polygonal
processes `arrayPolygon n ξ` on `C([0,1])` are tight.

Source: Jacod–Shiryaev (2003), Theorem VI.4.5 (Aldous's criterion for tightness in `D`) together
with Proposition VI.3.26 (tightness in `D` plus vanishing jumps is `C`-tightness); Aldous (1978).
The paths start at `0`, so the compact-containment condition (i) of VI.4.5 is not needed.
The proof follows Jacod–Shiryaev's: the successive `ε`-oscillation times are stopping times;
Aldous's condition makes each short oscillation block unlikely, Markov's inequality on the number
of short blocks bounds the number of oscillations, and a path with few oscillations, long blocks
and small steps has a small modulus of continuity (`isTightMeasureSet_of_modulus`). -/
theorem isTightMeasureSet_arrayPolygon_of_aldousCondition {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, Measurable[𝓕 n (i + 1)] (ξ n i))
    (hjump : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ i < n, ε < |ξ n i ω|}) atTop (𝓝 0))
    (hA : AldousCondition 𝓕 ξ μ) :
    IsTightMeasureSet (Set.range fun n => μ.map (arrayPolygon n ξ)) := by
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i => (hξ n i).mono ((𝓕 n).le _) le_rfl
  refine isTightMeasureSet_of_modulus _ (fun n => measurable_arrayPolygon n ξ (hξm n))
    (fun n ω => arrayPolygon_zero n ξ ω) ?_
  intro ε hε b hb
  set ε' := ε / 8 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨θ, hθ, N1, hN1⟩ := hA ε' hε'0 (b / 8) (by positivity)
  set q : ℕ := ⌈2 / θ⌉₊ + 1 with hq
  have hqpos : 0 < q := Nat.succ_pos _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  obtain ⟨δ', hδ', N2, hN2⟩ := hA ε' hε'0 (b / (8 * q)) (by positivity)
  have hJ := (tendsto_order.1 (hjump ε' hε'0)).2 (ENNReal.ofReal (b / 8))
    (ENNReal.ofReal_pos.2 (by positivity))
  refine ⟨δ' / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop N2, hJ,
    eventually_ge_atTop ⌈2 / δ'⌉₊] with n hn1 hn2 hn3 hn4
  set τ : ℕ → Ω → ℕ := fun k ω => oscTime (fun j => ∑ l ∈ Finset.range j, ξ n l ω) n ε' k
    with hτ
  set L := ⌊(n : ℝ) * θ⌋₊ with hL
  set L' := ⌊(n : ℝ) * δ'⌋₊ with hL'
  have hqL : 2 * n ≤ q * (L + 1) := by
    have h1 : (2 / θ : ℝ) ≤ q := by
      rw [hq]; push_cast; linarith [Nat.le_ceil (2 / θ)]
    have h2 : (n : ℝ) * θ < L + 1 := Nat.lt_floor_add_one _
    have : ((2 * n : ℕ) : ℝ) ≤ ((q * (L + 1) : ℕ) : ℝ) := by
      push_cast
      calc 2 * (n : ℝ) = (2 / θ) * (n * θ) := by field_simp
        _ ≤ q * (L + 1) := mul_le_mul h1 h2.le (by positivity) (by positivity)
    exact_mod_cast this
  -- the three bad events
  set E1 : Set Ω := {ω | τ q ω < n} with hE1
  set E2 : Set Ω := ⋃ k ∈ Finset.range q, {ω | τ (k + 1) ω < n ∧ τ (k + 1) ω ≤ τ k ω + L'}
    with hE2
  set E3 : Set Ω := {ω | ∃ i < n, ε' < |ξ n i ω|} with hE3
  have hE1le : μ E1 ≤ 2 * ENNReal.ofReal (b / 8) :=
    measure_oscTime_lt_le (fun i => hξ n i) n ε' L q hqpos hqL _
      (measure_shortBlock_le (fun i => hξ n i) n ε' L _ (hN1 n hn1))
  have hE2le : μ E2 ≤ ENNReal.ofReal (b / 8) := by
    calc μ E2 ≤ ∑ k ∈ Finset.range q,
          μ {ω | τ (k + 1) ω < n ∧ τ (k + 1) ω ≤ τ k ω + L'} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.range q, ENNReal.ofReal (b / (8 * q)) := Finset.sum_le_sum fun k _ =>
          measure_shortBlock_le (fun i => hξ n i) n ε' L' _ (hN2 n hn2) k
      _ = ENNReal.ofReal (b / 8) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg q)]
          congr 1
          field_simp
  have hbad : μ (E1 ∪ E2 ∪ E3) ≤ ENNReal.ofReal (b / 2) := by
    calc μ (E1 ∪ E2 ∪ E3) ≤ μ E1 + μ E2 + μ E3 :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ ≤ 2 * ENNReal.ofReal (b / 8) + ENNReal.ofReal (b / 8) + ENNReal.ofReal (b / 8) :=
          add_le_add (add_le_add hE1le hE2le) hn3.le
      _ = ENNReal.ofReal (b / 2) := by
          rw [two_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
          · congr 1; ring
          all_goals positivity
  have hsub : {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ' / 2 ∧
      ε ≤ dist (arrayPolygon n ξ ω s) (arrayPolygon n ξ ω t)} ⊆ E1 ∪ E2 ∪ E3 := by
    intro ω ⟨s, t, hst, hbig⟩
    by_contra hω
    simp only [Set.mem_union, not_or, hE1, hE2, hE3, Set.mem_ofPred_eq, not_lt, Set.mem_iUnion,
      Finset.mem_range, not_exists, not_and, not_le] at hω
    obtain ⟨⟨hq1, hgap⟩, hjmp⟩ := hω
    have hδ : (n : ℝ) * (δ' / 2) + 1 ≤ n * δ' := by
      have : (2 / δ' : ℝ) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn4)
      have : 2 ≤ (n : ℝ) * δ' := by
        rw [div_le_iff₀ hδ'] at this; linarith
      linarith
    have := dist_arrayPolygon_le n ξ ω hε'0.le q hδ (fun i hi => hjmp i hi)
      (fun k hk h => hgap k hk h) (le_antisymm (oscTime_le _ n ε' q) hq1) s t hst
    linarith
  calc μ.real {ω | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ' / 2 ∧
        ε ≤ dist (arrayPolygon n ξ ω s) (arrayPolygon n ξ ω t)}
      ≤ μ.real (E1 ∪ E2 ∪ E3) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ b / 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
    _ ≤ b := by linarith

/-! ### Martingale difference arrays satisfy Aldous's condition -/

/-- If `h` has zero conditional expectation given `m'`, it is orthogonal to every
`m'`-measurable `g` with `g * h` integrable. -/
private lemma integral_mul_eq_zero_of_condExp_eq_zero {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Filtration ℕ m) (k : ℕ) {g h : Ω → ℝ}
    (hg : StronglyMeasurable[f k] g) (hgh : Integrable (g * h) μ) (hh : Integrable h μ)
    (hce : μ[h | f k] =ᵐ[μ] 0) : ∫ ω, (g * h) ω ∂μ = 0 := by
  rw [← integral_condExp (f.le k)]
  calc ∫ ω, (μ[g * h | f k]) ω ∂μ = ∫ ω, (g * μ[h | f k]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg hgh hh)
    _ = 0 := by
        rw [integral_congr_ae (show g * μ[h | f k] =ᵐ[μ] 0 by
          filter_upwards [hce] with ω hω; simp [hω])]
        simp

/-- **Discrete Itô isometry for predictable indicator transforms.** For a square-integrable
martingale difference sequence `x` (`x i` is `f (i+1)`-measurable, `E[x i | f i] = 0`) and sets
`A i ∈ f i`, `E[(∑_{i<k} 1_{A i} x i)²] = ∑_{i<k} E[1_{A i} E[x i² | f i]]`. -/
private lemma integral_sq_sum_indicator {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Filtration ℕ m} {x : ℕ → Ω → ℝ}
    (hx : ∀ i, StronglyMeasurable[f (i + 1)] (x i)) (hmds : ∀ i, μ[x i | f i] =ᵐ[μ] 0)
    (hL2 : ∀ i, MemLp (x i) 2 μ) {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet[f i] (A i)) (k : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range k, (A i).indicator (x i) ω) ^ 2 ∂μ =
      ∑ i ∈ Finset.range k, ∫ ω, (A i).indicator (μ[fun ω => x i ω ^ 2 | f i]) ω ∂μ := by
  have hAm : ∀ i, MeasurableSet (A i) := fun i => f.le i _ (hA i)
  have hM2 : ∀ k, MemLp (fun ω => ∑ i ∈ Finset.range k, (A i).indicator (x i) ω) 2 μ :=
    fun k => memLp_finsetSum _ fun i _ => (hL2 i).indicator (hAm i).nullMeasurableSet
  have hMmeas : ∀ k, StronglyMeasurable[f k]
      (fun ω => ∑ i ∈ Finset.range k, (A i).indicator (x i) ω) := by
    intro k
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
    have hi' : i + 1 ≤ k := by simp at hi; omega
    exact ((hx i).mono (f.mono hi')).indicator (f.mono (show i ≤ k by omega) _ (hA i))
  induction k with
  | zero => simp
  | succ k ih =>
    set M := fun ω => ∑ i ∈ Finset.range k, (A i).indicator (x i) ω with hM
    have hexp : (fun ω => (∑ i ∈ Finset.range (k + 1), (A i).indicator (x i) ω) ^ 2) =
        fun ω => M ω ^ 2 + 2 * ((M * (A k).indicator (1 : Ω → ℝ)) * x k) ω +
          (A k).indicator (fun ω => x k ω ^ 2) ω := by
      funext ω
      by_cases hω : ω ∈ A k
      · simp [Finset.sum_range_succ, hM, hω]; ring
      · simp [Finset.sum_range_succ, hM, hω]
    have hgk : StronglyMeasurable[f k] (M * (A k).indicator (1 : Ω → ℝ)) :=
      (hMmeas k).mul (stronglyMeasurable_const.indicator (hA k))
    have hgL2 : MemLp (M * (A k).indicator (1 : Ω → ℝ)) 2 μ := by
      have : M * (A k).indicator (1 : Ω → ℝ) = (A k).indicator M := by
        funext ω; by_cases hω : ω ∈ A k <;> simp [hω]
      rw [this]; exact (hM2 k).indicator (hAm k).nullMeasurableSet
    have hint1 : Integrable (fun ω => M ω ^ 2) μ := (hM2 k).integrable_sq
    have hint2 : Integrable ((M * (A k).indicator (1 : Ω → ℝ)) * x k) μ :=
      hgL2.integrable_mul (hL2 k)
    have hint3 : Integrable (fun ω => x k ω ^ 2) μ := (hL2 k).integrable_sq
    rw [hexp, integral_add ?_ (hint3.indicator (hAm k)), integral_add hint1 (hint2.const_mul 2),
      integral_const_mul,
      integral_mul_eq_zero_of_condExp_eq_zero f k hgk hint2 ((hL2 k).integrable one_le_two)
        (hmds k), ih, Finset.sum_range_succ, integral_indicator (hAm k),
      integral_indicator (hAm k), setIntegral_condExp (f.le k) hint3 (hA k)]
    · ring
    · exact hint1.add (hint2.const_mul 2)

/-- Pointwise core of the Lenglart-type bound: the predictable truncation keeps the summed
conditional variances below `η₀`. -/
private lemma sum_indicator_le_of_nonneg (c : ℕ → ℝ) (σ ρ n : ℕ) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hc : ∀ j < n, 0 ≤ c j) :
    ∑ i ∈ Finset.range n,
      (if σ ≤ i ∧ i < ρ ∧ ∑ j ∈ Finset.Ico σ (i + 1), c j ≤ η₀ then c i else 0) ≤ η₀ := by
  have key : ∀ I : Finset ℕ, (∀ i ∈ I, i < n ∧ σ ≤ i ∧ ∑ j ∈ Finset.Ico σ (i + 1), c j ≤ η₀) →
      ∑ i ∈ I, c i ≤ η₀ := by
    intro I hIp
    rcases I.eq_empty_or_nonempty with hI | hI
    · rw [hI, Finset.sum_empty]; exact hη₀
    set i₀ := I.max' hI
    have hi₀ := hIp i₀ (I.max'_mem hI)
    calc ∑ i ∈ I, c i ≤ ∑ j ∈ Finset.Ico σ (i₀ + 1), c j := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j hj _ => ?_
          · intro i hi
            have hle : i ≤ i₀ := I.le_max' i hi
            have := (hIp i hi).2.1
            simp only [Finset.mem_Ico]; omega
          · have := hi₀.1
            simp only [Finset.mem_Ico] at hj
            exact hc j (by omega)
      _ ≤ η₀ := hi₀.2.2
  rw [← Finset.sum_filter]
  refine key _ fun i hi => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨hi.1, hi.2.1, hi.2.2.2⟩

/-- On the event where the summed conditional variances over `[σ, ρ)` are at most `η₀`, the
truncated transform is the whole increment `S ρ - S σ`. -/
private lemma sum_indicator_eq_of_le (x c : ℕ → ℝ) (σ ρ n : ℕ) {η₀ : ℝ}
    (hσρ : σ ≤ ρ) (hρn : ρ ≤ n) (hc : ∀ j < n, 0 ≤ c j)
    (hsmall : ∑ j ∈ Finset.Ico σ ρ, c j ≤ η₀) :
    ∑ i ∈ Finset.range n,
      (if σ ≤ i ∧ i < ρ ∧ ∑ j ∈ Finset.Ico σ (i + 1), c j ≤ η₀ then x i else 0) =
      ∑ i ∈ Finset.range ρ, x i - ∑ i ∈ Finset.range σ, x i := by
  have hcond : ∀ i, (σ ≤ i ∧ i < ρ ∧ ∑ j ∈ Finset.Ico σ (i + 1), c j ≤ η₀) ↔ (σ ≤ i ∧ i < ρ) := by
    intro i
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, le_trans ?_ hsmall⟩
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
        fun j hj _ => hc j ?_
      simp only [Finset.mem_Ico] at hj; omega
  simp_rw [hcond]
  rw [← Finset.sum_filter, ← Finset.sum_range_add_sum_Ico _ hσρ, add_sub_cancel_left]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma sum_Ico_eq_sum_indicator (c : ℕ → Ω → ℝ) (σ : Ω → ℕ) (i : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.Ico (σ ω) (i + 1), c j ω =
      ∑ j ∈ Finset.range (i + 1), {ω' | σ ω' ≤ j}.indicator (c j) ω := by
  have : ∀ j, {ω' | σ ω' ≤ j}.indicator (c j) ω = if σ ω ≤ j then c j ω else 0 := by
    intro j
    by_cases h : σ ω ≤ j <;> simp [h]
  simp_rw [this]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
  omega

/-- **Lenglart-type bound for a martingale difference row.** For stopping times `σ ≤ ρ ≤ n`,
`P(|S ρ - S σ| ≥ ε) ≤ P(∑_{σ ≤ j < ρ} E[x j² | f j] > η₀) + η₀ / ε²`.
Proof: truncate the transform `∑ 1_{σ ≤ i < ρ} x i` predictably once the summed conditional
variances would exceed `η₀`; the discrete Itô isometry bounds its second moment by `η₀`, and the
truncation is inactive on the event where the conditional variances stay below `η₀`. This is
the discrete form of Lenglart's domination inequality (E. Lenglart, *Relation de domination
entre deux processus*, Ann. IHP 13 (1977) 171–179) used by Jacod–Shiryaev, Lemma I.3.30. -/
private lemma measure_abs_sub_ge_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Filtration ℕ m} {x : ℕ → Ω → ℝ}
    (hx : ∀ i, StronglyMeasurable[f (i + 1)] (x i)) (hmds : ∀ i, μ[x i | f i] =ᵐ[μ] 0)
    (hL2 : ∀ i, MemLp (x i) 2 μ) {σ ρ : Ω → ℕ}
    (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℕ)))
    (hρ : IsStoppingTime f (fun ω => (ρ ω : WithTop ℕ))) (n : ℕ)
    (hσρ : ∀ ω, σ ω ≤ ρ ω) (hρn : ∀ ω, ρ ω ≤ n) {ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    μ {ω | ε ≤ |∑ i ∈ Finset.range (ρ ω), x i ω - ∑ i ∈ Finset.range (σ ω), x i ω|} ≤
      μ {ω | η₀ < ∑ j ∈ Finset.Ico (σ ω) (ρ ω), (μ[fun ω => x j ω ^ 2 | f j]) ω} +
        ENNReal.ofReal (η₀ / ε ^ 2) := by
  set c : ℕ → Ω → ℝ := fun j => μ[fun ω => x j ω ^ 2 | f j] with hc_def
  set A : ℕ → Set Ω := fun i =>
    {ω | σ ω ≤ i ∧ i < ρ ω ∧ ∑ j ∈ Finset.Ico (σ ω) (i + 1), c j ω ≤ η₀} with hA_def
  have hσle := isStoppingTime_natCast_iff.1 hσ
  have hρle := isStoppingTime_natCast_iff.1 hρ
  have hAmeas : ∀ i, MeasurableSet[f i] (A i) := by
    intro i
    have hset : A i = {ω | σ ω ≤ i} ∩ ({ω | ρ ω ≤ i}ᶜ ∩
        (fun ω => ∑ j ∈ Finset.range (i + 1), {ω' | σ ω' ≤ j}.indicator (c j) ω) ⁻¹'
          Set.Iic η₀) := by
      ext ω
      simp only [hA_def, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_preimage, Set.mem_Iic, not_le, sum_Ico_eq_sum_indicator c σ i ω]
    rw [hset]
    refine (hσle i).inter ((hρle i).compl.inter ?_)
    have hg : Measurable[f i]
        (fun ω => ∑ j ∈ Finset.range (i + 1), {ω' | σ ω' ≤ j}.indicator (c j) ω) := by
      refine Finset.measurable_sum _ fun j hj => ?_
      have hji : j ≤ i := by simp at hj; omega
      exact (stronglyMeasurable_condExp.measurable.mono (f.mono hji) le_rfl).indicator
        (f.mono hji _ (hσle j))
    exact hg measurableSet_Iic
  set Y : Ω → ℝ := fun ω => ∑ i ∈ Finset.range n, (A i).indicator (x i) ω with hY
  have hind : ∀ (g : ℕ → Ω → ℝ) i ω, (A i).indicator (g i) ω =
      if σ ω ≤ i ∧ i < ρ ω ∧ ∑ j ∈ Finset.Ico (σ ω) (i + 1), c j ω ≤ η₀ then g i ω else 0 := by
    intro g i ω
    by_cases h : σ ω ≤ i ∧ i < ρ ω ∧ ∑ j ∈ Finset.Ico (σ ω) (i + 1), c j ω ≤ η₀
    · exact (Set.indicator_of_mem (show ω ∈ A i from h) (g i)).trans
        (ite_eq_left_of_eq_true _ _ (eq_true h)).symm
    · exact (Set.indicator_of_notMem (show ω ∉ A i from h) (g i)).trans
        (ite_eq_right_of_eq_false _ _ (eq_false h)).symm
  have hcnn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ c j ω := by
    rw [ae_all_iff]
    intro j
    exact condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (x j ω))
  -- second moment of the truncated transform
  have hY2 : ∫ ω, Y ω ^ 2 ∂μ ≤ η₀ := by
    rw [hY, integral_sq_sum_indicator hx hmds hL2 hAmeas n,
      ← integral_finsetSum _ fun i _ => integrable_condExp.indicator (f.le i _ (hAmeas i))]
    calc ∫ ω, ∑ i ∈ Finset.range n, (A i).indicator (c i) ω ∂μ ≤ ∫ _ω, η₀ ∂μ := by
          refine integral_mono_ae (integrable_finsetSum _ fun i _ =>
            integrable_condExp.indicator (f.le i _ (hAmeas i))) (integrable_const _) ?_
          filter_upwards [hcnn] with ω hω
          simp_rw [hind c]
          exact sum_indicator_le_of_nonneg (fun j => c j ω) (σ ω) (ρ ω) n hη₀.le
            fun j _ => hω j
      _ = η₀ := by simp
  have hYint : Integrable (fun ω => Y ω ^ 2) μ :=
    (memLp_finsetSum _ fun i _ => (hL2 i).indicator
      (f.le i _ (hAmeas i)).nullMeasurableSet).integrable_sq
  have hcheb : μ {ω | ε ^ 2 ≤ Y ω ^ 2} ≤ ENNReal.ofReal (η₀ / ε ^ 2) := by
    have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg (Y ω))
      hYint (ε ^ 2)
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h.trans hY2
  calc μ {ω | ε ≤ |∑ i ∈ Finset.range (ρ ω), x i ω - ∑ i ∈ Finset.range (σ ω), x i ω|}
      ≤ μ ({ω | η₀ < ∑ j ∈ Finset.Ico (σ ω) (ρ ω), c j ω} ∪ {ω | ε ^ 2 ≤ Y ω ^ 2}) := by
        refine measure_mono_ae ?_
        filter_upwards [hcnn] with ω hω hmem
        by_cases hsmall : η₀ < ∑ j ∈ Finset.Ico (σ ω) (ρ ω), c j ω
        · exact Or.inl hsmall
        · right
          push Not at hsmall
          have heq : Y ω = ∑ i ∈ Finset.range (ρ ω), x i ω - ∑ i ∈ Finset.range (σ ω), x i ω := by
            simp only [hY]
            simp_rw [hind x]
            exact sum_indicator_eq_of_le (fun i => x i ω) (fun j => c j ω) (σ ω) (ρ ω) n
              (hσρ ω) (hρn ω) (fun j _ => hω j) hsmall
          simp only [Set.mem_ofPred_eq] at hmem ⊢
          rw [heq, ← sq_abs (_ - _)]
          exact pow_le_pow_left₀ hε.le hmem 2
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hcheb)

/-- **Grid control of a nondecreasing sequence.** If `V` is nondecreasing on `[0, n]` and is
within `Δ` of the identity at the grid times `s_j = min (j / M) 1`, then its increment over any
index window of length `⌊n / M⌋` is at most `2 / M + 2Δ`. -/
private lemma sub_le_of_grid (V : ℕ → ℝ) (n M : ℕ) (hM : 0 < M) (hn : 0 < n)
    (hmono : ∀ a b, a ≤ b → b ≤ n → V a ≤ V b) {Δ : ℝ}
    (hdev : ∀ j < M + 3,
      |V ⌊(n : ℝ) * min ((j : ℝ) / M) 1⌋₊ - min ((j : ℝ) / M) 1| ≤ Δ)
    {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) (hbL : b ≤ a + ⌊(n : ℝ) * (1 / M)⌋₊) :
    V b - V a ≤ 2 / M + 2 * Δ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set j := a * M / n with hj
  have hjM : j ≤ M := by
    rw [hj]; exact Nat.div_le_of_le_mul (by nlinarith)
  have hjn : j * n ≤ a * M := Nat.div_mul_le_self _ _
  have hjlt : a * M < (j + 1) * n := by
    rw [hj, add_mul, one_mul]
    have := Nat.div_add_mod (a * M) n
    have := Nat.mod_lt (a * M) hn
    nlinarith
  have hfl : ⌊(n : ℝ) * (1 / M)⌋₊ = n / M := by
    rw [mul_one_div]; exact Nat.floor_div_eq_div n M
  have hbM : b * M ≤ a * M + n := by
    have h1 : b * M ≤ (a + n / M) * M := Nat.mul_le_mul_right M (hfl ▸ hbL)
    have h2 : n / M * M ≤ n := Nat.div_mul_le_self n M
    nlinarith
  set s : ℕ → ℝ := fun j => min ((j : ℝ) / M) 1 with hs
  have hsj : s j = (j : ℝ) / M := by
    simp only [hs]; rw [min_eq_left]; rw [div_le_one hMR]; exact_mod_cast hjM
  have hlow : ⌊(n : ℝ) * s j⌋₊ ≤ a := by
    rw [hsj]
    refine Nat.floor_le_of_le ?_
    rw [mul_div_assoc', div_le_iff₀ hMR]
    exact_mod_cast (show n * j ≤ a * M by linarith [hjn])
  have hhigh : b ≤ ⌊(n : ℝ) * s (j + 2)⌋₊ := by
    by_cases hj2 : j + 2 ≤ M
    · have : s (j + 2) = ((j + 2 : ℕ) : ℝ) / M := by
        simp only [hs]; rw [min_eq_left]; rw [div_le_one hMR]; exact_mod_cast hj2
      rw [this]
      refine Nat.le_floor ?_
      rw [mul_div_assoc', le_div_iff₀ hMR]
      have : b * M ≤ n * (j + 2) := by nlinarith
      exact_mod_cast this
    · have : s (j + 2) = 1 := by
        simp only [hs]; rw [min_eq_right]; rw [one_le_div hMR]; push_cast
        exact_mod_cast (show M ≤ j + 2 by omega)
      rw [this, mul_one, Nat.floor_natCast]; exact hbn
  have hsle : ∀ k, s k ≤ 1 := fun k => min_le_right _ _
  have hfloor_n : ∀ k, ⌊(n : ℝ) * s k⌋₊ ≤ n := fun k =>
    Nat.floor_le_of_le (by nlinarith [hsle k])
  have h1 := hdev j (by omega)
  have h2 := hdev (j + 2) (by omega)
  have hgap : s (j + 2) - s j ≤ 2 / M := by
    rw [hsj]
    have : s (j + 2) ≤ ((j + 2 : ℕ) : ℝ) / M := min_le_left _ _
    have : ((j + 2 : ℕ) : ℝ) / M - (j : ℝ) / M = 2 / M := by push_cast; ring
    linarith
  have hVb := hmono b _ hhigh (hfloor_n _)
  have hVa : V ⌊(n : ℝ) * s j⌋₊ ≤ V a := hmono _ a hlow (hab.trans hbn)
  have := abs_le.1 h1
  have := abs_le.1 h2
  simp only [hs] at *
  linarith

/-- **Martingale difference arrays satisfy Aldous's condition.** Let row `n` of `ξ` be a
square-integrable martingale difference sequence for `𝓕 n` (`ξ n i` is `𝓕 n (i+1)`-measurable,
`E[ξ n i | 𝓕 n i] = 0`). If the predictable quadratic variation at each time converges in
probability to the identity, `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] → t` for every `t ∈ [0,1]`, then
the partial sums satisfy `AldousCondition`.

Source: Jacod–Shiryaev (2003), Theorem VI.4.13 (Rebolledo's criterion: tightness of the
predictable quadratic variations implies Aldous's condition for locally square-integrable
martingales), via Lenglart's inequality; here the limit of the quadratic variation is the
continuous deterministic function `t`, and pointwise convergence upgrades to uniform control
over windows because the quadratic variation is nondecreasing (`sub_le_of_grid`). -/
theorem aldousCondition_of_martingaleDifference {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t)) :
    AldousCondition 𝓕 ξ μ := by
  intro ε hε η hη
  set η₀ := ε ^ 2 * η / 2 with hη₀
  have hη₀pos : 0 < η₀ := by positivity
  set M : ℕ := ⌈8 / η₀⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have h2M : 2 / (M : ℝ) ≤ η₀ / 4 := by
    rw [div_le_iff₀ hMR]
    have : 8 / η₀ ≤ (M : ℝ) := by rw [hM]; push_cast; linarith [Nat.le_ceil (8 / η₀)]
    rw [div_le_iff₀ hη₀pos] at this
    linarith
  set Δ := η₀ / 4 with hΔ
  set s : ℕ → ℝ := fun j => min ((j : ℝ) / M) 1 with hs
  have hsI : ∀ j, s j ∈ Set.Icc (0 : ℝ) 1 := fun j =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  set V : ℕ → ℕ → Ω → ℝ := fun n k ω =>
    ∑ j ∈ Finset.range k, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω with hV
  set G : ℕ → Set Ω := fun n => ⋃ j ∈ Finset.range (M + 3),
    {ω | ENNReal.ofReal Δ ≤ edist (V n ⌊(n : ℝ) * s j⌋₊ ω) (s j)} with hG
  have hGlim : Tendsto (fun n => ∑ j ∈ Finset.range (M + 3),
      μ {ω | ENNReal.ofReal Δ ≤ edist (V n ⌊(n : ℝ) * s j⌋₊ ω) (s j)}) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _j ∈ Finset.range (M + 3), (0 : ℝ≥0∞) by simp]
    exact tendsto_finsetSum _ fun j _ => hQV (s j) (hsI j) (ENNReal.ofReal Δ)
      (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hGlim).2 (ENNReal.ofReal (η / 2))
    (ENNReal.ofReal_pos.2 (by positivity)))
  refine ⟨1 / M, by positivity, max N 1, fun n hn σ ρ hσ hρ hσρ => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hn)
  have hL := measure_abs_sub_ge_le (fun i => hξ n i) (hmds n) (hL2 n) hσ hρ n
    (fun ω => (hσρ ω).1) (fun ω => (hσρ ω).2.2) hε hη₀pos
  have hcnn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω := by
    rw [ae_all_iff]
    exact fun j => condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (ξ n j ω))
  have hsub : μ {ω | η₀ < ∑ j ∈ Finset.Ico (σ ω) (ρ ω), (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω} ≤
      μ (G n) := by
    refine measure_mono_ae ?_
    filter_upwards [hcnn] with ω hω hbig
    by_contra hG'
    simp only [hG, Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, not_exists,
      not_le] at hG'
    have hmono : ∀ a b, a ≤ b → b ≤ n → V n a ω ≤ V n b ω := by
      intro a b hab _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hab)
        fun j _ _ => hω j
    have hgrid := sub_le_of_grid (fun k => V n k ω) n M hMpos hn1 hmono (Δ := Δ)
      (fun j hj => by
        have := (edist_lt_ofReal.1 (hG' j hj)).le
        rw [Real.dist_eq] at this
        exact this) (hσρ ω).1 (hσρ ω).2.2 (hσρ ω).2.1
    rw [Finset.sum_Ico_eq_sub _ (hσρ ω).1] at hbig
    simp only [hV] at hgrid
    linarith
  have hGle : μ (G n) ≤ ENNReal.ofReal (η / 2) :=
    (measure_biUnion_finset_le _ _).trans (hN n ((le_max_left _ _).trans hn)).le
  calc _ ≤ _ := hL
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
        refine add_le_add (hsub.trans hGle) (le_of_eq ?_)
        congr 1
        rw [hη₀]; field_simp
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-! ### Jump control from the Lindeberg condition -/

/-- **Lindeberg implies asymptotically negligible jumps.** Under the (unconditional) Lindeberg
condition `LindebergConditionTriangular`, the largest increment of row `n` tends to `0` in
probability: by the union bound and Chebyshev's inequality,
`P(max_{i<n} |ξ n i| > ε) ≤ ε⁻² ∑_{i<n} E[ξ n i² 1{|ξ n i| > ε}]`. -/
theorem tendsto_measure_exists_abs_gt_of_lindeberg {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ξ : ℕ → ℕ → Ω → ℝ} (hξm : ∀ n i, Measurable (ξ n i))
    (hL2 : ∀ n i, MemLp (ξ n i) 2 μ) (hLind : LindebergConditionTriangular ξ μ)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ∃ i < n, ε < |ξ n i ω|}) atTop (𝓝 0) := by
  set a : ℕ → ℕ → ℝ := fun n i =>
    ∫ ω, (ξ n i ω) ^ 2 * Set.indicator {ω' | ε < |ξ n i ω'|} 1 ω ∂μ with ha
  have hset : ∀ n i, MeasurableSet {ω' | ε < |ξ n i ω'|} := fun n i =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hξm n i))
  have ha0 : ∀ n i, 0 ≤ a n i := fun n i =>
    integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (by simp) _)
  have hbound : ∀ n i, μ {ω | ε < |ξ n i ω|} ≤ ENNReal.ofReal (a n i / ε ^ 2) := by
    intro n i
    have hint : Integrable (fun ω => (ξ n i ω) ^ 2 * Set.indicator {ω' | ε < |ξ n i ω'|} 1 ω)
        μ := by
      have : (fun ω => (ξ n i ω) ^ 2 * Set.indicator {ω' | ε < |ξ n i ω'|} 1 ω) =
          Set.indicator {ω' | ε < |ξ n i ω'|} (fun ω => (ξ n i ω) ^ 2) := by
        funext ω
        by_cases h : ε < |ξ n i ω| <;> simp [h]
      rw [this]
      exact (hL2 n i).integrable_sq.indicator (hset n i)
    have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω =>
      mul_nonneg (sq_nonneg (ξ n i ω)) (Set.indicator_nonneg (by simp) ω)) hint (ε ^ 2)
    have hsub : {ω | ε < |ξ n i ω|} ⊆
        {ω | ε ^ 2 ≤ (ξ n i ω) ^ 2 * Set.indicator {ω' | ε < |ξ n i ω'|} 1 ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [Set.indicator_of_mem (show ω ∈ {ω' | ε < |ξ n i ω'|} from hω), Pi.one_apply,
        mul_one]
      exact (pow_le_pow_left₀ hε.le hω.le 2).trans (sq_abs _).le
    calc μ {ω | ε < |ξ n i ω|} ≤ μ {ω | ε ^ 2 ≤
          (ξ n i ω) ^ 2 * Set.indicator {ω' | ε < |ξ n i ω'|} 1 ω} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {ω | ε ^ 2 ≤
          (ξ n i ω) ^ 2 * Set.indicator {ω' | ε < |ξ n i ω'|} 1 ω}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (a n i / ε ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ (by positivity), mul_comm]
          exact h
  have hupper : ∀ n, μ {ω | ∃ i < n, ε < |ξ n i ω|} ≤
      ENNReal.ofReal ((∑ i ∈ Finset.range n, a n i) / ε ^ 2) := by
    intro n
    have : {ω | ∃ i < n, ε < |ξ n i ω|} = ⋃ i ∈ Finset.range n, {ω | ε < |ξ n i ω|} := by
      ext ω; simp
    rw [this, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg fun i _ => by
      have := ha0 n i; positivity]
    exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => hbound n i)
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∑ i ∈ Finset.range n, a n i) / ε ^ 2)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero, show (0 : ℝ) = 0 / ε ^ 2 by simp]
    exact ENNReal.tendsto_ofReal ((hLind ε hε).div_const _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hupper

/-! ### The functional CLT for martingale difference arrays -/

/-- **Functional CLT for martingale difference arrays in `D([0,1])`** (McLeish's invariance
principle with tightness from Aldous's criterion).

Let row `n` of `ξ` be a square-integrable martingale difference sequence for the filtration
`𝓕 n`, with
* predictable quadratic variation converging to the identity: for every `t ∈ [0,1]`,
  `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] → t` in probability;
* the Lindeberg condition `LindebergConditionTriangular ξ μ`;
* (**T81, taken as a hypothesis**) finite-dimensional convergence of the step process to a
  continuous process `Z`: for every finite set of times `I ⊆ [0,1]`,
  `(∑_{i < ⌊n t⌋} ξ n i)_{t ∈ I} → (Z t)_{t ∈ I}` in distribution. This is the conclusion of
  McLeish's martingale CLT (roadmap task T81: quadratic-variation convergence + Lindeberg ⇒
  finite-dimensional convergence to Brownian motion), which is not yet in the library; `Z` is
  meant to be Brownian motion on `[0,1]`.

Then the step processes `arrayStepProcess n ξ` converge in distribution to `Z` in the Skorokhod
J1 topology on `D([0,1])`.

Proof: T43's transfer theorem `tendstoInDistribution_skorokhod_of_tight_of_fdd` applied to the
step processes and their polygonal interpolations `arrayPolygon n ξ`. Tightness of the polygons
is Aldous's criterion (`isTightMeasureSet_arrayPolygon_of_aldousCondition`), whose condition
comes from the martingale structure and quadratic-variation convergence
(`aldousCondition_of_martingaleDifference`); the jumps vanish by Lindeberg
(`tendsto_measure_exists_abs_gt_of_lindeberg`), which also transfers the finite-dimensional
convergence from the step process to the polygon (Slutsky).

Sources: McLeish (1974), §3; Jacod–Shiryaev (2003), Theorems VI.4.5 and VI.4.13 and §VIII.3;
Billingsley (1999), §18. -/
theorem tendstoInDistribution_arrayStepProcess {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ)
    (Z : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hZ : AEMeasurable Z P')
    (hT81 : ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω))
      atTop (fun ω => I.restrict (fun t => Z ω t)) (fun _ => μ) P') :
    TendstoInDistribution (fun n => arrayStepProcess n ξ) atTop
      (fun ω => SkorokhodSpace.ofContinuous (Z ω)) (fun _ => μ) P' := by
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i =>
    ((hξ n i).mono ((𝓕 n).le _)).measurable
  have hjump := tendsto_measure_exists_abs_gt_of_lindeberg hξm hL2 hLind
  have hAset : ∀ (ε : ℝ) n, MeasurableSet {ω | ∃ i < n, ε < |ξ n i ω|} := by
    intro ε n
    have : {ω | ∃ i < n, ε < |ξ n i ω|} = ⋃ i ∈ Finset.range n, {ω | ε < |ξ n i ω|} := by
      ext ω; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hξm n i))
  have hpoly_eval : ∀ n (t : Set.Icc (0 : ℝ) 1), Measurable fun ω => arrayPolygon n ξ ω t :=
    fun n t => (continuous_eval_const t).measurable.comp (measurable_arrayPolygon n ξ (hξm n))
  refine tendstoInDistribution_skorokhod_of_tight_of_fdd one_pos
    (fun n => arrayStepProcess n ξ) (fun n => arrayPolygon n ξ) Z
    (fun n => (measurable_arrayStepProcess n ξ (hξm n)).aemeasurable)
    (fun n => (measurable_arrayPolygon n ξ (hξm n)).aemeasurable) hZ
    (isTightMeasureSet_arrayPolygon_of_aldousCondition (fun n i => (hξ n i).measurable) hjump
      (aldousCondition_of_martingaleDifference hξ hmds hL2 hQV)) ?_ ?_
  · -- finite-dimensional convergence of the polygon, by Slutsky from `hT81`
    intro I
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ (hT81 I) ?_
      (fun n => (measurable_pi_iff.2 fun (t : I) => hpoly_eval n t).aemeasurable)
    refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
    set δ := ε.toReal / 2 with hδ
    have hδpos : 0 < δ := by
      have := ENNReal.toReal_pos hε.ne' hεtop; positivity
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hjump δ hδpos)
      (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
    by_contra hω'
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hω hω'
    refine absurd hω (not_le.2 (lt_of_le_of_lt (b := ENNReal.ofReal δ)
      (edist_pi_le_iff.2 fun t => ?_) ?_))
    · simp only [Pi.sub_apply, Pi.zero_apply, Finset.restrict]
      rw [edist_dist, dist_zero_right, Real.norm_eq_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := abs_arrayStepProcess_sub_arrayPolygon_le n ξ ω hδpos.le hω' t
      rw [arrayStepProcess_apply] at h
      rwa [abs_sub_comm] at h
    · rw [hδ, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hεtop]
      rw [ENNReal.ofReal_ofNat]
      exact ENNReal.half_lt_self hε.ne' hεtop
  · -- jump control
    intro ε hε
    refine ⟨fun n => {ω | ∃ i < n, ε < |ξ n i ω|}, hAset ε, ?_, fun n ω hω t => ?_⟩
    · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hjump ε hε)
      simp only [measureReal_def]
      exact this
    · simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hω
      exact abs_arrayStepProcess_sub_arrayPolygon_le n ξ ω hε.le hω t

end

end MathlibExt.Probability.Martingale
