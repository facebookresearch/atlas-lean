/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Selection
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Directional selection, overdominance and underdominance at one locus

One diploid locus with alleles `A` (allele `0`) and `a` (allele `1`), random mating with
Hardy–Weinberg proportions among newborns, nonoverlapping generations and constant genotype
viabilities `wAA`, `wAa`, `waa`, encoded as the symmetric genotype-fitness matrix
`![![wAA, wAa], ![wAa, waa]]`. One generation of viability selection maps the frequency `p` of
`A` to `p' = diploidSelect ![p, 1 - p] w 0 = p (p wAA + q wAa) / w̄`, where `q = 1 - p` and
`w̄ = diploidMeanFitness ![p, 1 - p] w = p² wAA + 2 p q wAa + q² waa` (`Selection.lean`).

## Main results

* `viability_selection_regimes`: the change `p' - p = p q (p (wAA - wAa) + q (wAa - waa)) / w̄`,
  and the long-run behaviour of the frequency of `A` from any `p₀ ∈ (0, 1)` in the three regimes:
  under **directional selection** (`wAA ≥ wAa ≥ waa ≥ 0`, not all equal) it increases strictly to
  `1`, or jumps to `1` in one generation when `wAa = waa = 0`; under **overdominance**
  (viabilities `1 - s, 1, 1 - t` with `0 < s, t ≤ 1`) it converges monotonically, without
  overshooting, to the unique interior equilibrium `p_e = t / (s + t)`; under
  **underdominance** (`s, t < 0`) it tends to `0` or `1` according to the side of `p_e` it
  starts on, and stays at `p_e` if it starts there. In the `s, t` parametrization
  `p' - p = p q (s + t) (p_e - p) / w̄`, and under overdominance the factor `p q (s + t) / w̄`
  lies in `(0, 1]`.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics* (version of December 2019), Section II.4,
  equations (II-31)–(II-34), pp. 62–63; Section II.7, equations (II-101)–(II-102), pp. 84–89;
  Chapter II, Complements/Problems, Problem 15, p. 135.
-/

@[expose] public section

open Filter Topology Set
open MathlibExt.Biology.PopulationGenetics.Selection

namespace MathlibExt.Biology.PopulationGenetics.Classical.ViabilityRegimes

/-- Mean viability of two alleles at frequencies `(p, 1 - p)` with symmetric viabilities. -/
private lemma diploidMeanFitness_two (a b c p : ℝ) :
    diploidMeanFitness ![p, 1 - p] ![![a, b], ![b, c]] =
      p ^ 2 * a + 2 * p * (1 - p) * b + (1 - p) ^ 2 * c := by
  simp [diploidMeanFitness, Fin.sum_univ_two]
  ring

/-- The frequency of allele `0` after one generation of selection, in closed form. -/
private lemma diploidSelect_two (a b c p : ℝ) :
    diploidSelect ![p, 1 - p] ![![a, b], ![b, c]] 0 =
      p * (p * a + (1 - p) * b) / diploidMeanFitness ![p, 1 - p] ![![a, b], ![b, c]] := by
  have hm : marginalFitness ![p, 1 - p] ![![a, b], ![b, c]] 0 = p * a + (1 - p) * b := by
    simp [marginalFitness, Fin.sum_univ_two]
    ring
  simp only [diploidSelect, hm, Matrix.cons_val_zero]

/-- A monotone trajectory of a map, bounded above, converges to a fixed point of the map when the
map is continuous between the start and the bound. -/
private lemma exists_fixedPt_of_monotone {f : ℝ → ℝ} {x₀ B : ℝ}
    (hmono : Monotone fun n => f^[n] x₀) (hB : ∀ n, f^[n] x₀ ≤ B)
    (hcont : ∀ y, x₀ ≤ y → y ≤ B → ContinuousAt f y) :
    ∃ L, x₀ ≤ L ∧ L ≤ B ∧ f L = L ∧ Tendsto (fun n => f^[n] x₀) atTop (𝓝 L) := by
  have hbdd : BddAbove (range fun n => f^[n] x₀) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  have ht := tendsto_atTop_ciSup hmono hbdd
  have h0 : x₀ ≤ ⨆ n, f^[n] x₀ := by simpa using hmono.ge_of_tendsto ht 0
  have hLB : ⨆ n, f^[n] x₀ ≤ B := ciSup_le hB
  exact ⟨_, h0, hLB, isFixedPt_of_tendsto_iterate ht (hcont _ h0 hLB), ht⟩

/-- An antitone trajectory of a map, bounded below, converges to a fixed point of the map when
the map is continuous between the bound and the start. -/
private lemma exists_fixedPt_of_antitone {f : ℝ → ℝ} {x₀ B : ℝ}
    (hanti : Antitone fun n => f^[n] x₀) (hB : ∀ n, B ≤ f^[n] x₀)
    (hcont : ∀ y, B ≤ y → y ≤ x₀ → ContinuousAt f y) :
    ∃ L, B ≤ L ∧ L ≤ x₀ ∧ f L = L ∧ Tendsto (fun n => f^[n] x₀) atTop (𝓝 L) := by
  have hbdd : BddBelow (range fun n => f^[n] x₀) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  have ht := tendsto_atTop_ciInf hanti hbdd
  have h0 : ⨅ n, f^[n] x₀ ≤ x₀ := by simpa using hanti.le_of_tendsto ht 0
  have hBL : B ≤ ⨅ n, f^[n] x₀ := le_ciInf hB
  exact ⟨_, hBL, h0, isFixedPt_of_tendsto_iterate ht (hcont _ hBL h0), ht⟩

section Step

variable {a b c : ℝ} {wbar f : ℝ → ℝ}
  (hw : ∀ p, wbar p = p ^ 2 * a + 2 * p * (1 - p) * b + (1 - p) ^ 2 * c)
  (hf : ∀ p, f p = p * (p * a + (1 - p) * b) / wbar p)
include hw hf

/-- The change in the frequency of `A` over one generation (Felsenstein's (II-34)). -/
private lemma step_sub {p : ℝ} (hp : wbar p ≠ 0) :
    f p - p = p * (1 - p) * (p * (a - b) + (1 - p) * (b - c)) / wbar p := by
  rw [hf, div_sub' hp, hw]
  congr 1
  ring

/-- The frequency of `a` after one generation. -/
private lemma one_sub_step {p : ℝ} (hp : wbar p ≠ 0) :
    1 - f p = (1 - p) * (p * b + (1 - p) * c) / wbar p := by
  rw [hf, one_sub_div hp, hw]
  congr 1
  ring

/-- The selection map is continuous wherever the mean viability does not vanish. -/
private lemma continuousAt_step {y : ℝ} (hy : wbar y ≠ 0) : ContinuousAt f y := by
  have hfe : f = fun p => p * (p * a + (1 - p) * b) /
      (p ^ 2 * a + 2 * p * (1 - p) * b + (1 - p) ^ 2 * c) := by
    funext p
    rw [hf, hw]
  rw [hw] at hy
  rw [hfe]
  fun_prop (disch := exact hy)

/-- Directional selection, for viabilities `a ≥ b ≥ c ≥ 0` with `c < a`: the frequency of `A`
increases strictly to `1` when `b > 0`, and reaches `1` in one generation when `b = c = 0`. -/
private lemma directional {p₀ : ℝ} (hp₀ : p₀ ∈ Ioo 0 1) (hc : 0 ≤ c) (hcb : c ≤ b)
    (hba : b ≤ a) (hca : c < a) :
    0 < a ∧ (∀ p ∈ Ioc 0 1, 0 < wbar p) ∧
      (0 < b → (∀ n, f^[n] p₀ ∈ Ioo 0 1) ∧ StrictMono (fun n => f^[n] p₀) ∧
        Tendsto (fun n => f^[n] p₀) atTop (𝓝 1)) ∧
      (b = 0 → c = 0 → f^[1] p₀ = 1) := by
  have ha : 0 < a := hc.trans_lt hca
  have hb : 0 ≤ b := hc.trans hcb
  have hpos : ∀ p ∈ Ioc 0 1, 0 < wbar p := by
    rintro p ⟨hp0, hp1⟩
    rw [hw]
    have h1 : 0 ≤ 1 - p := by linarith
    have : 0 < p ^ 2 * a := by positivity
    have : 0 ≤ 2 * p * (1 - p) * b := by positivity
    have : 0 ≤ (1 - p) ^ 2 * c := by positivity
    linarith
  refine ⟨ha, hpos, fun hb0 => ?_, fun hb0 hc0 => ?_⟩
  · -- one generation keeps the frequency in `(0, 1)` and raises it
    have hstep : ∀ p ∈ Ioo 0 1, f p ∈ Ioo 0 1 ∧ p < f p := by
      rintro p ⟨hp0, hp1⟩
      have hD := hpos p ⟨hp0, hp1.le⟩
      have hq : 0 < 1 - p := by linarith
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hf]
        have : 0 < p * a := mul_pos hp0 ha
        have : 0 ≤ (1 - p) * b := mul_nonneg hq.le hb
        have : 0 < p * (p * a + (1 - p) * b) := mul_pos hp0 (by linarith)
        positivity
      · have h := one_sub_step hw hf hD.ne'
        have : 0 < (1 - p) * (p * b + (1 - p) * c) / wbar p := by
          have : 0 < p * b := mul_pos hp0 hb0
          have : 0 ≤ (1 - p) * c := mul_nonneg hq.le hc
          have : 0 < p * b + (1 - p) * c := by linarith
          positivity
        linarith
      · have h := step_sub hw hf hD.ne'
        have hbr : 0 < p * (a - b) + (1 - p) * (b - c) := by
          rcases hba.lt_or_eq with hlt | heq
          · have : 0 < p * (a - b) := mul_pos hp0 (by linarith)
            have : 0 ≤ (1 - p) * (b - c) := mul_nonneg hq.le (by linarith)
            linarith
          · have : 0 ≤ p * (a - b) := mul_nonneg hp0.le (by linarith)
            have : 0 < (1 - p) * (b - c) := mul_pos hq (by linarith)
            linarith
        have : 0 < p * (1 - p) * (p * (a - b) + (1 - p) * (b - c)) / wbar p := by positivity
        linarith
    have hn : ∀ n, f^[n] p₀ ∈ Ioo 0 1 := by
      intro n
      induction n with
      | zero => exact hp₀
      | succ n ih => rw [Function.iterate_succ_apply']; exact (hstep _ ih).1
    have hsm : StrictMono fun n => f^[n] p₀ := strictMono_nat_of_lt_succ fun n => by
      simp only [Function.iterate_succ_apply']
      exact (hstep _ (hn n)).2
    refine ⟨hn, hsm, ?_⟩
    obtain ⟨L, hL0, hL1, hfix, ht⟩ := exists_fixedPt_of_monotone hsm.monotone
      (fun n => (hn n).2.le) fun y hy0 hy1 =>
        continuousAt_step hw hf (hpos y ⟨hp₀.1.trans_le hy0, hy1⟩).ne'
    rcases hL1.lt_or_eq with hlt | rfl
    · exact absurd hfix (hstep L ⟨hp₀.1.trans_le hL0, hlt⟩).2.ne'
    · exact ht
  · -- only `AA` survives
    have hp0 : p₀ ≠ 0 := hp₀.1.ne'
    rw [Function.iterate_one, hf, hw, hb0, hc0]
    field_simp
    ring

omit hf in
/-- In the parametrization `a = 1 - s`, `b = 1`, `c = 1 - t`, the mean viability exceeds
`p q (s + t)` by `p (1 - s) + q (1 - t)`. -/
private lemma wbar_sub_param {s t : ℝ} (hs : a = 1 - s) (hb1 : b = 1) (ht : c = 1 - t) (p : ℝ) :
    wbar p - p * (1 - p) * (s + t) = p * (1 - s) + (1 - p) * (1 - t) := by
  rw [hw, hs, hb1, ht]
  ring

/-- In the parametrization `a = 1 - s`, `b = 1`, `c = 1 - t` with `s + t ≠ 0`, the change in
frequency is `p q (s + t) (p_e - p) / w̄` with `p_e = t / (s + t)`. -/
private lemma step_sub_param {s t : ℝ} (hs : a = 1 - s) (hb1 : b = 1) (ht : c = 1 - t)
    (hst : s + t ≠ 0) {p : ℝ} (hp : wbar p ≠ 0) :
    f p - p = p * (1 - p) * (s + t) * (t / (s + t) - p) / wbar p := by
  rw [step_sub hw hf hp, hs, hb1, ht]
  congr 1
  field_simp
  ring

/-- The selection map as a step of size `p q (s + t) / w̄` towards `p_e`. -/
private lemma step_eq_param {s t : ℝ} (hs : a = 1 - s) (hb1 : b = 1) (ht : c = 1 - t)
    (hst : s + t ≠ 0) {p : ℝ} (hp : wbar p ≠ 0) :
    f p = p + p * (1 - p) * (s + t) / wbar p * (t / (s + t) - p) := by
  have h := step_sub_param hw hf hs hb1 ht hst hp
  have e : p * (1 - p) * (s + t) * (t / (s + t) - p) / wbar p =
      p * (1 - p) * (s + t) / wbar p * (t / (s + t) - p) := by ring
  linarith

/-- Overdominance, for viabilities `1 - s, 1, 1 - t` with `0 < s, t ≤ 1`: the frequency of `A`
converges monotonically to `p_e = t / (s + t)` without overshooting it. -/
private lemma overdominance {s t p₀ : ℝ} (hs : a = 1 - s) (hb1 : b = 1) (ht : c = 1 - t)
    (hp₀ : p₀ ∈ Ioo 0 1) (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∀ p ∈ Ioo 0 1, 0 < 2 * p * (1 - p) ∧ 2 * p * (1 - p) ≤ wbar p) ∧
      t / (s + t) ∈ Ioo 0 1 ∧ (∀ p ∈ Ioo 0 1, f p = p ↔ p = t / (s + t)) ∧
      (∀ p ∈ Ioo 0 1, 0 < p * (1 - p) * (s + t) / wbar p ∧
        p * (1 - p) * (s + t) / wbar p ≤ 1 ∧
        (p * (1 - p) * (s + t) / wbar p = 1 ↔ s = 1 ∧ t = 1)) ∧
      (s = 1 → t = 1 → f^[1] p₀ = t / (s + t)) ∧
      (p₀ ≤ t / (s + t) → Monotone (fun n => f^[n] p₀) ∧ ∀ n, f^[n] p₀ ≤ t / (s + t)) ∧
      (t / (s + t) ≤ p₀ → Antitone (fun n => f^[n] p₀) ∧ ∀ n, t / (s + t) ≤ f^[n] p₀) ∧
      Tendsto (fun n => f^[n] p₀) atTop (𝓝 (t / (s + t))) := by
  have hst : 0 < s + t := by linarith
  set pe := t / (s + t) with hpe
  have hlow : ∀ p ∈ Ioo (0 : ℝ) 1, 0 < 2 * p * (1 - p) ∧ 2 * p * (1 - p) ≤ wbar p := by
    rintro p ⟨hp0, hp1⟩
    have hq : 0 < 1 - p := by linarith
    refine ⟨by positivity, ?_⟩
    rw [hw, hs, hb1, ht]
    have h1 : 0 ≤ 1 - s := by linarith
    have h2 : 0 ≤ 1 - t := by linarith
    have : 0 ≤ p ^ 2 * (1 - s) := by positivity
    have : 0 ≤ (1 - p) ^ 2 * (1 - t) := by positivity
    linarith
  have hD : ∀ p ∈ Ioo (0 : ℝ) 1, 0 < wbar p := fun p hp => (hlow p hp).1.trans_le (hlow p hp).2
  have hpe0 : 0 < pe := div_pos ht0 hst
  have hpe1 : pe < 1 := (div_lt_one hst).2 (by linarith)
  have hfac : ∀ p ∈ Ioo (0 : ℝ) 1, 0 < p * (1 - p) * (s + t) / wbar p ∧
      p * (1 - p) * (s + t) / wbar p ≤ 1 ∧
      (p * (1 - p) * (s + t) / wbar p = 1 ↔ s = 1 ∧ t = 1) := by
    rintro p ⟨hp0, hp1⟩
    have hq : 0 < 1 - p := by linarith
    have hDp := hD p ⟨hp0, hp1⟩
    have hid := wbar_sub_param hw hs hb1 ht p
    have h1 : 0 ≤ p * (1 - s) := mul_nonneg hp0.le (by linarith)
    have h2 : 0 ≤ (1 - p) * (1 - t) := mul_nonneg hq.le (by linarith)
    refine ⟨by positivity, (div_le_one hDp).2 (by linarith), ?_⟩
    rw [div_eq_one_iff_eq hDp.ne']
    constructor
    · intro h
      have e1 : p * (1 - s) = 0 := by linarith
      have e2 : (1 - p) * (1 - t) = 0 := by linarith
      constructor
      · rcases mul_eq_zero.1 e1 with h | h <;> linarith
      · rcases mul_eq_zero.1 e2 with h | h <;> linarith
    · rintro ⟨h1, h2⟩
      rw [h1, h2] at hid ⊢
      linarith
  have hrel : ∀ p ∈ Ioo (0 : ℝ) 1, f p = p + p * (1 - p) * (s + t) / wbar p * (pe - p) :=
    fun p hp => step_eq_param hw hf hs hb1 ht hst.ne' (hD p hp).ne'
  have hfix : ∀ p ∈ Ioo (0 : ℝ) 1, f p = p ↔ p = pe := by
    intro p hp
    have hφ := (hfac p hp).1
    rw [hrel p hp]
    constructor
    · intro h
      have : p * (1 - p) * (s + t) / wbar p * (pe - p) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hφ.ne'
      · linarith
    · intro h
      rw [← h]
      ring
  have hbelow : ∀ p ∈ Ioo (0 : ℝ) 1, p ≤ pe → p ≤ f p ∧ f p ≤ pe := by
    intro p hp hle
    obtain ⟨hφ0, hφ1, -⟩ := hfac p hp
    rw [hrel p hp]
    have h1 := mul_nonneg hφ0.le (sub_nonneg.2 hle)
    have h2 := mul_le_mul_of_nonneg_right hφ1 (sub_nonneg.2 hle)
    constructor <;> linarith
  have habove : ∀ p ∈ Ioo (0 : ℝ) 1, pe ≤ p → f p ≤ p ∧ pe ≤ f p := by
    intro p hp hle
    obtain ⟨hφ0, hφ1, -⟩ := hfac p hp
    rw [hrel p hp]
    have h1 := mul_nonpos_of_nonneg_of_nonpos hφ0.le (sub_nonpos.2 hle)
    have h2 := mul_le_mul_of_nonpos_right hφ1 (sub_nonpos.2 hle)
    constructor <;> linarith
  have hinc : p₀ ≤ pe → ∀ n, f^[n] p₀ ∈ Icc p₀ pe := by
    intro h n
    induction n with
    | zero => exact ⟨le_rfl, h⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := hbelow _ ⟨hp₀.1.trans_le ih.1, ih.2.trans_lt hpe1⟩ ih.2
      exact ⟨ih.1.trans h1, h2⟩
  have hdec : pe ≤ p₀ → ∀ n, f^[n] p₀ ∈ Icc pe p₀ := by
    intro h n
    induction n with
    | zero => exact ⟨h, le_rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := habove _ ⟨hpe0.trans_le ih.1, ih.2.trans_lt hp₀.2⟩ ih.1
      exact ⟨h2, h1.trans ih.2⟩
  have hmono : p₀ ≤ pe → Monotone fun n => f^[n] p₀ := fun h =>
    monotone_nat_of_le_succ fun n => by
      change f^[n] p₀ ≤ f^[n + 1] p₀
      rw [Function.iterate_succ_apply']
      exact (hbelow _ ⟨hp₀.1.trans_le (hinc h n).1, (hinc h n).2.trans_lt hpe1⟩ (hinc h n).2).1
  have hanti : pe ≤ p₀ → Antitone fun n => f^[n] p₀ := fun h =>
    antitone_nat_of_succ_le fun n => by
      change f^[n + 1] p₀ ≤ f^[n] p₀
      rw [Function.iterate_succ_apply']
      exact (habove _ ⟨hpe0.trans_le (hdec h n).1, (hdec h n).2.trans_lt hp₀.2⟩ (hdec h n).1).1
  refine ⟨hlow, ⟨hpe0, hpe1⟩, hfix, hfac, fun h1 h2 => ?_,
    fun h => ⟨hmono h, fun n => (hinc h n).2⟩, fun h => ⟨hanti h, fun n => (hdec h n).1⟩, ?_⟩
  · rw [Function.iterate_one, hrel p₀ hp₀, (hfac p₀ hp₀).2.2.2 ⟨h1, h2⟩]
    ring
  · rcases le_total p₀ pe with h | h
    · obtain ⟨L, hL0, hL1, hfixL, hlim⟩ := exists_fixedPt_of_monotone (hmono h)
        (fun n => (hinc h n).2) fun y hy0 hy1 =>
          continuousAt_step hw hf (hD y ⟨hp₀.1.trans_le hy0, hy1.trans_lt hpe1⟩).ne'
      rwa [(hfix L ⟨hp₀.1.trans_le hL0, hL1.trans_lt hpe1⟩).1 hfixL] at hlim
    · obtain ⟨L, hL0, hL1, hfixL, hlim⟩ := exists_fixedPt_of_antitone (hanti h)
        (fun n => (hdec h n).1) fun y hy0 hy1 =>
          continuousAt_step hw hf (hD y ⟨hpe0.trans_le hy0, hy1.trans_lt hp₀.2⟩).ne'
      rwa [(hfix L ⟨hpe0.trans_le hL0, hL1.trans_lt hp₀.2⟩).1 hfixL] at hlim

/-- Underdominance, for viabilities `1 - s, 1, 1 - t` with `s, t < 0`: the frequency of `A` moves
away from `p_e = t / (s + t)` to `0` or to `1`. -/
private lemma underdominance {s t p₀ : ℝ} (hs : a = 1 - s) (hb1 : b = 1) (ht : c = 1 - t)
    (hp₀ : p₀ ∈ Ioo 0 1) (hs0 : s < 0) (ht0 : t < 0) :
    t / (s + t) ∈ Ioo 0 1 ∧ (∀ p ∈ Ioo 0 1, f p = p ↔ p = t / (s + t)) ∧
      (p₀ < t / (s + t) → Tendsto (fun n => f^[n] p₀) atTop (𝓝 0)) ∧
      (t / (s + t) < p₀ → Tendsto (fun n => f^[n] p₀) atTop (𝓝 1)) ∧
      (p₀ = t / (s + t) → ∀ n, f^[n] p₀ = t / (s + t)) := by
  have hst : s + t < 0 := by linarith
  set pe := t / (s + t) with hpe
  have hDpos : ∀ p, 0 < wbar p := by
    intro p
    rw [hw, hs, hb1, ht]
    have e : p ^ 2 * (1 - s) + 2 * p * (1 - p) * 1 + (1 - p) ^ 2 * (1 - t) =
        1 + -s * p ^ 2 + -t * (1 - p) ^ 2 := by ring
    rw [e]
    have := mul_nonneg (neg_nonneg.2 hs0.le) (sq_nonneg p)
    have := mul_nonneg (neg_nonneg.2 ht0.le) (sq_nonneg (1 - p))
    linarith
  have hpe0 : 0 < pe := div_pos_of_neg_of_neg ht0 hst
  have hpe1 : pe < 1 := (div_lt_one_of_neg hst).2 (by linarith)
  have hφ : ∀ p ∈ Ioo (0 : ℝ) 1, p * (1 - p) * (s + t) / wbar p < 0 := by
    rintro p ⟨hp0, hp1⟩
    have : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hst) (hDpos p)
  have hrel : ∀ p, f p = p + p * (1 - p) * (s + t) / wbar p * (pe - p) :=
    fun p => step_eq_param hw hf hs hb1 ht hst.ne (hDpos p).ne'
  have hfix : ∀ p ∈ Ioo (0 : ℝ) 1, f p = p ↔ p = pe := by
    intro p hp
    rw [hrel p]
    constructor
    · intro h
      have : p * (1 - p) * (s + t) / wbar p * (pe - p) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hφ p hp).ne
      · linarith
    · intro h
      rw [← h]
      ring
  have hcont : ∀ y, ContinuousAt f y := fun y => continuousAt_step hw hf (hDpos y).ne'
  refine ⟨⟨hpe0, hpe1⟩, hfix, fun h => ?_, fun h => ?_, fun h n => ?_⟩
  · -- below `p_e` the frequency of `A` decreases to `0`
    have hstep : ∀ p ∈ Ioo (0 : ℝ) 1, p < pe → 0 < f p ∧ f p < p := by
      rintro p ⟨hp0, hp1⟩ hlt
      have h1 := mul_neg_of_neg_of_pos (hφ p ⟨hp0, hp1⟩) (sub_pos.2 hlt)
      refine ⟨?_, by rw [hrel p]; linarith⟩
      rw [hf, hs, hb1]
      have : 0 < p * (1 - s) := mul_pos hp0 (by linarith)
      have : 0 < p * (p * (1 - s) + (1 - p) * 1) := mul_pos hp0 (by linarith)
      exact div_pos this (hDpos p)
    have hn : ∀ n, f^[n] p₀ ∈ Ioc 0 p₀ := by
      intro n
      induction n with
      | zero => exact ⟨hp₀.1, le_rfl⟩
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        obtain ⟨h1, h2⟩ := hstep _ ⟨ih.1, ih.2.trans_lt hp₀.2⟩ (ih.2.trans_lt h)
        exact ⟨h1, h2.le.trans ih.2⟩
    have hanti : Antitone fun n => f^[n] p₀ := antitone_nat_of_succ_le fun n => by
      change f^[n + 1] p₀ ≤ f^[n] p₀
      rw [Function.iterate_succ_apply']
      exact (hstep _ ⟨(hn n).1, (hn n).2.trans_lt hp₀.2⟩ ((hn n).2.trans_lt h)).2.le
    obtain ⟨L, hL0, hL1, hfixL, hlim⟩ :=
      exists_fixedPt_of_antitone hanti (fun n => (hn n).1.le) fun y _ _ => hcont y
    rcases hL0.lt_or_eq with hpos | rfl
    · have := (hfix L ⟨hpos, hL1.trans_lt hp₀.2⟩).1 hfixL
      linarith
    · exact hlim
  · -- above `p_e` the frequency of `A` increases to `1`
    have hstep : ∀ p ∈ Ioo (0 : ℝ) 1, pe < p → p < f p ∧ f p < 1 := by
      rintro p ⟨hp0, hp1⟩ hlt
      have h1 := mul_pos_of_neg_of_neg (hφ p ⟨hp0, hp1⟩) (sub_neg.2 hlt)
      refine ⟨by rw [hrel p]; linarith, ?_⟩
      have h := one_sub_step hw hf (hDpos p).ne'
      rw [hb1, ht] at h
      have hq : 0 < 1 - p := by linarith
      have : 0 ≤ (1 - p) * (1 - t) := mul_nonneg hq.le (by linarith)
      have : 0 < (1 - p) * (p * 1 + (1 - p) * (1 - t)) := mul_pos hq (by linarith)
      have : 0 < (1 - p) * (p * 1 + (1 - p) * (1 - t)) / wbar p := div_pos this (hDpos p)
      linarith
    have hn : ∀ n, f^[n] p₀ ∈ Ico p₀ 1 := by
      intro n
      induction n with
      | zero => exact ⟨le_rfl, hp₀.2⟩
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        obtain ⟨h1, h2⟩ := hstep _ ⟨hp₀.1.trans_le ih.1, ih.2⟩ (h.trans_le ih.1)
        exact ⟨ih.1.trans h1.le, h2⟩
    have hmono : Monotone fun n => f^[n] p₀ := monotone_nat_of_le_succ fun n => by
      change f^[n] p₀ ≤ f^[n + 1] p₀
      rw [Function.iterate_succ_apply']
      exact (hstep _ ⟨hp₀.1.trans_le (hn n).1, (hn n).2⟩ (h.trans_le (hn n).1)).1.le
    obtain ⟨L, hL0, hL1, hfixL, hlim⟩ :=
      exists_fixedPt_of_monotone hmono (fun n => (hn n).2.le) fun y _ _ => hcont y
    rcases hL1.lt_or_eq with hlt | rfl
    · have := (hfix L ⟨hp₀.1.trans_le hL0, hlt⟩).1 hfixL
      linarith
    · exact hlim
  · -- started at `p_e`, the frequency stays there
    rw [h]
    exact Function.iterate_fixed ((hfix pe ⟨hpe0, hpe1⟩).2 rfl) n

end Step

/-- **Directional selection, overdominance and underdominance at one locus.** Let genotypes `AA`,
`Aa`, `aa` of a diploid locus with alleles `A` (allele `0`) and `a` (allele `1`) have viabilities
`wAA`, `wAa`, `waa`, given as the symmetric genotype-fitness matrix `w`, and let
`w̄ p = diploidMeanFitness ![p, 1 - p] w = p² wAA + 2 p q wAa + q² waa`, where `q = 1 - p`, and
`f p = diploidSelect ![p, 1 - p] w 0`. For `p ∈ [0, 1]`, nonnegative viabilities and `w̄ p > 0`,
under random mating `w̄ p` is the mean viability of a population whose newborns carry `A` at
frequency `p`, and `f p` is the frequency of `A` after one generation of viability selection. Let
`p₀ ∈ (0, 1)` and `p_n = f^[n] p₀`.

* The change formula is an algebraic identity: for all real viabilities and every real `p` with
  `w̄ p ≠ 0`, `f p - p = p q (p (wAA - wAa) + q (wAa - waa)) / w̄ p`.
* **Directional selection.** Let `0 ≤ waa ≤ wAa ≤ wAA` with `waa < wAA` (the viabilities are
  nonnegative and not all equal). Then `wAA > 0` and `w̄ > 0` on `(0, 1]`. If `wAa > 0`, then
  `p_n ∈ (0, 1)` for all `n`, `p_n` increases strictly and `p_n → 1`; if `wAa = waa = 0`, then
  `p_1 = 1`.
* Write `wAA = 1 - s`, `wAa = 1`, `waa = 1 - t` and `p_e = t / (s + t)`. Then
  `w̄ p - p q (s + t) = p (1 - s) + q (1 - t)` for every real `p`, and if `s + t ≠ 0`, then
  `f p - p = p q (s + t) (p_e - p) / w̄ p` for every real `p` with `w̄ p ≠ 0`.
* **Overdominance** (`0 < s ≤ 1` and `0 < t ≤ 1`). For `p ∈ (0, 1)`, `w̄ p ≥ 2 p q > 0`. The
  equilibrium `p_e` lies in `(0, 1)` and is the only `p ∈ (0, 1)` with `f p = p`. For
  `p ∈ (0, 1)` the factor `p q (s + t) / w̄ p` lies in `(0, 1]` and equals `1` exactly when
  `s = t = 1`, in which case `p_1 = p_e`. If `p₀ ≤ p_e`, then `p_n` is monotone (nondecreasing)
  with `p_n ≤ p_e` for all `n`; if `p₀ ≥ p_e`, then `p_n` is antitone with `p_n ≥ p_e` for all `n`;
  and `p_n → p_e`.
* **Underdominance** (`s < 0` and `t < 0`). The equilibrium `p_e` lies in `(0, 1)` and is the only
  `p ∈ (0, 1)` with `f p = p`. If `p₀ < p_e`, then `p_n → 0`; if `p₀ > p_e`, then `p_n → 1`; and
  if `p₀ = p_e`, then `p_n = p_e` for all `n`. -/
theorem viability_selection_regimes (wAA wAa waa : ℝ) {p₀ : ℝ} (hp₀ : p₀ ∈ Ioo 0 1) :
    let w : Fin 2 → Fin 2 → ℝ := ![![wAA, wAa], ![wAa, waa]]
    let wbar : ℝ → ℝ := fun p => diploidMeanFitness ![p, 1 - p] w
    let f : ℝ → ℝ := fun p => diploidSelect ![p, 1 - p] w 0
    let pn : ℕ → ℝ := fun n => f^[n] p₀
    (∀ p, wbar p ≠ 0 →
      f p - p = p * (1 - p) * (p * (wAA - wAa) + (1 - p) * (wAa - waa)) / wbar p) ∧
    (0 ≤ waa → waa ≤ wAa → wAa ≤ wAA → waa < wAA →
      0 < wAA ∧ (∀ p ∈ Ioc 0 1, 0 < wbar p) ∧
      (0 < wAa → (∀ n, pn n ∈ Ioo 0 1) ∧ StrictMono pn ∧ Tendsto pn atTop (𝓝 1)) ∧
      (wAa = 0 → waa = 0 → pn 1 = 1)) ∧
    ∀ s t : ℝ, wAA = 1 - s → wAa = 1 → waa = 1 - t →
      let pe := t / (s + t)
      (∀ p, wbar p - p * (1 - p) * (s + t) = p * (1 - s) + (1 - p) * (1 - t)) ∧
      (s + t ≠ 0 → ∀ p, wbar p ≠ 0 → f p - p = p * (1 - p) * (s + t) * (pe - p) / wbar p) ∧
      (0 < s → s ≤ 1 → 0 < t → t ≤ 1 →
        (∀ p ∈ Ioo 0 1, 0 < 2 * p * (1 - p) ∧ 2 * p * (1 - p) ≤ wbar p) ∧
        pe ∈ Ioo 0 1 ∧ (∀ p ∈ Ioo 0 1, f p = p ↔ p = pe) ∧
        (∀ p ∈ Ioo 0 1, 0 < p * (1 - p) * (s + t) / wbar p ∧
          p * (1 - p) * (s + t) / wbar p ≤ 1 ∧
          (p * (1 - p) * (s + t) / wbar p = 1 ↔ s = 1 ∧ t = 1)) ∧
        (s = 1 → t = 1 → pn 1 = pe) ∧
        (p₀ ≤ pe → Monotone pn ∧ ∀ n, pn n ≤ pe) ∧
        (pe ≤ p₀ → Antitone pn ∧ ∀ n, pe ≤ pn n) ∧
        Tendsto pn atTop (𝓝 pe)) ∧
      (s < 0 → t < 0 →
        pe ∈ Ioo 0 1 ∧ (∀ p ∈ Ioo 0 1, f p = p ↔ p = pe) ∧
        (p₀ < pe → Tendsto pn atTop (𝓝 0)) ∧ (pe < p₀ → Tendsto pn atTop (𝓝 1)) ∧
        (p₀ = pe → ∀ n, pn n = pe)) := by
  intro w wbar f pn
  have hw : ∀ p, wbar p = p ^ 2 * wAA + 2 * p * (1 - p) * wAa + (1 - p) ^ 2 * waa :=
    fun p => diploidMeanFitness_two wAA wAa waa p
  have hf : ∀ p, f p = p * (p * wAA + (1 - p) * wAa) / wbar p :=
    fun p => diploidSelect_two wAA wAa waa p
  exact ⟨fun p hp => step_sub hw hf hp,
    fun hc hcb hba hca => directional hw hf hp₀ hc hcb hba hca,
    fun s t hs hb1 ht => ⟨wbar_sub_param hw hs hb1 ht,
      fun hst p hp => step_sub_param hw hf hs hb1 ht hst hp,
      fun hs0 hs1 ht0 ht1 => overdominance hw hf hs hb1 ht hp₀ hs0 hs1 ht0 ht1,
      fun hs0 ht0 => underdominance hw hf hs hb1 ht hp₀ hs0 ht0⟩⟩

end MathlibExt.Biology.PopulationGenetics.Classical.ViabilityRegimes
