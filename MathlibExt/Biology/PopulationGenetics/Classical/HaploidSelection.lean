/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExt.Biology.PopulationGenetics.Selection
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Closed form for iterated haploid selection

For finitely many haploid types with constant positive fitnesses `w`, one
generation of selection is `p i ↦ p i * w i / ∑ j, p j * w j`. Iterating this
map has the closed form
`p_t i = p₀ i * w i ^ t / ∑ j, p₀ j * w j ^ t` on the closed simplex.

For two initially present types, the log-odds grow linearly with slope
`log (w true / w false)`. If one initially present type is strictly fitter
than every other initially present type, it goes to fixation; types absent
initially remain absent. The limiting statement for tied maximal fitnesses is
not part of this file.

The public results are stated directly for `Selection.select` in the
`Selection` namespace. The intervening lemmas for an abstract map satisfying
the one-generation formula are private implementation details, not a second
selection API.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, Sections II.2, II.6,
  II.8 and VIII.2.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Classical.HaploidSelection

/-- **Closed form of iterated haploid selection.** `S` is one generation of haploid selection
with constant fitnesses `w`, `S p i = p i * w i / ∑ j, p j * w j`. With positive fitnesses and an
initial frequency vector `p₀` on the closed simplex, after `t` generations
`S^[t] p₀ i = p₀ i * w i ^ t / ∑ j, p₀ j * w j ^ t`. Types absent at the start (`p₀ i = 0`) stay
absent. -/
private theorem iterate_select_apply {ι : Type*} [Fintype ι] (w p₀ : ι → ℝ)
    (S : (ι → ℝ) → ι → ℝ) (hS : ∀ p i, S p i = p i * w i / ∑ j, p j * w j)
    (hw : ∀ i, 0 < w i) (hp₀ : ∀ i, 0 ≤ p₀ i) (hsum : ∑ i, p₀ i = 1) (t : ℕ) (i : ι) :
    S^[t] p₀ i = p₀ i * w i ^ t / ∑ j, p₀ j * w j ^ t := by
  have hD : ∀ t : ℕ, 0 < ∑ j, p₀ j * w j ^ t := by
    intro t
    have hex : ∃ j₀, 0 < p₀ j₀ := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hzero : ∑ i, p₀ i = 0 :=
        Finset.sum_eq_zero (fun i _ => le_antisymm (hcon i) (hp₀ i))
      rw [hsum] at hzero
      exact one_ne_zero hzero
    obtain ⟨j₀, hj₀⟩ := hex
    refine Finset.sum_pos' (fun j _ => mul_nonneg (hp₀ j) (pow_nonneg (le_of_lt (hw j)) t)) ?_
    exact ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (pow_pos (hw j₀) t)⟩
  revert i
  induction t with
  | zero =>
    intro i
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
    rw [hsum, div_one]
  | succ t ih =>
    intro i
    have hDt : (∑ j, p₀ j * w j ^ t) ≠ 0 := ne_of_gt (hD t)
    have hDt1 : (∑ j, p₀ j * w j ^ (t + 1)) ≠ 0 := ne_of_gt (hD (t + 1))
    rw [Function.iterate_succ_apply', hS]
    simp only [ih]
    have hterm : ∀ j : ι, (p₀ j * w j ^ t / (∑ j, p₀ j * w j ^ t)) * w j
        = (p₀ j * w j ^ (t + 1)) / (∑ j, p₀ j * w j ^ t) := by
      intro j
      rw [pow_succ]
      ring
    have hM : (∑ j, (p₀ j * w j ^ t / (∑ j, p₀ j * w j ^ t)) * w j)
        = (∑ j, p₀ j * w j ^ (t + 1)) / (∑ j, p₀ j * w j ^ t) := by
      simp only [hterm, ← Finset.sum_div]
    rw [hM]
    have hN : (p₀ i * w i ^ t / (∑ j, p₀ j * w j ^ t)) * w i
        = (p₀ i * w i ^ (t + 1)) / (∑ j, p₀ j * w j ^ t) := by
      rw [pow_succ]
      ring
    rw [hN]
    field_simp

/-- **Log-odds of two haploid types change linearly in time.** Two types, `true` (fitness
`w true`) and `false` (fitness `w false`), with positive fitnesses; `S` is one generation of
haploid selection. If both types are present initially (`0 < p₀ true < 1`, written
`∀ i, 0 < p₀ i` and `∑ i, p₀ i = 1`), the log-odds of `true` after `t` generations is
`log (p₀ true / (1 - p₀ true)) + t * log (w true / w false)`. -/
private theorem log_odds_iterate_select (w p₀ : Bool → ℝ)
    (S : (Bool → ℝ) → Bool → ℝ) (hS : ∀ p i, S p i = p i * w i / ∑ j, p j * w j)
    (hw : ∀ i, 0 < w i) (hp₀ : ∀ i, 0 < p₀ i) (hsum : ∑ i, p₀ i = 1) (t : ℕ) :
    Real.log (S^[t] p₀ true / (1 - S^[t] p₀ true)) =
      Real.log (p₀ true / (1 - p₀ true)) + (t : ℝ) * Real.log (w true / w false) := by
  have hclosed : ∀ t : ℕ, ∀ i : Bool, S^[t] p₀ i = p₀ i * w i ^ t / ∑ j, p₀ j * w j ^ t :=
    fun t i => iterate_select_apply w p₀ S hS hw (fun i => le_of_lt (hp₀ i)) hsum t i
  have hD : ∀ t : ℕ, 0 < ∑ j, p₀ j * w j ^ t := by
    intro t
    exact Finset.sum_pos (fun j _ => mul_pos (hp₀ j) (pow_pos (hw j) t)) Finset.univ_nonempty
  have hDne : (∑ j, p₀ j * w j ^ t) ≠ 0 := ne_of_gt (hD t)
  have hb : (p₀ false * w false ^ t) ≠ 0 :=
    ne_of_gt (mul_pos (hp₀ false) (pow_pos (hw false) t))
  have hDsum : (∑ j, p₀ j * w j ^ t) = (p₀ true * w true ^ t) + (p₀ false * w false ^ t) := by
    simp only [Fintype.sum_bool]
  have h1m : 1 - S^[t] p₀ true = (p₀ false * w false ^ t) / (∑ j, p₀ j * w j ^ t) := by
    rw [hclosed t true, hDsum]
    have hne : (p₀ true * w true ^ t) + (p₀ false * w false ^ t) ≠ 0 := by
      rw [← hDsum]
      exact hDne
    field_simp
    ring
  have hratio : S^[t] p₀ true / (1 - S^[t] p₀ true)
      = (p₀ true / p₀ false) * ((w true / w false) ^ t) := by
    rw [h1m, hclosed t true, div_pow]
    have hp0f : p₀ false ≠ 0 := ne_of_gt (hp₀ false)
    have hwft : w false ^ t ≠ 0 := pow_ne_zero t (ne_of_gt (hw false))
    field_simp
  have h1p : (1 : ℝ) - p₀ true = p₀ false := by
    have h := hsum
    simp only [Fintype.sum_bool] at h
    linarith
  rw [hratio]
  have hp0f : p₀ false ≠ 0 := ne_of_gt (hp₀ false)
  have hp0t : p₀ true ≠ 0 := ne_of_gt (hp₀ true)
  rw [Real.log_mul (div_ne_zero hp0t hp0f)
    (pow_ne_zero t (div_ne_zero (ne_of_gt (hw true)) (ne_of_gt (hw false))))]
  rw [Real.log_pow, h1p]

/-- **A unique fittest initially present type goes to fixation.** With positive fitnesses, an
initial frequency vector `p₀` on the simplex, a type `k` present initially (`0 < p₀ k`) and
strictly fitter than every other initially present type, the frequency vectors `S^[t] p₀` of
iterated haploid selection converge to `Pi.single k 1` (frequency `1` for `k`, `0` for every
other type). Types absent initially remain absent regardless of their fitness. -/
private theorem tendsto_iterate_select_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w p₀ : ι → ℝ)
    (S : (ι → ℝ) → ι → ℝ) (hS : ∀ p i, S p i = p i * w i / ∑ j, p j * w j)
    (hw : ∀ i, 0 < w i) (hp₀ : ∀ i, 0 ≤ p₀ i) (hsum : ∑ i, p₀ i = 1)
    (k : ι) (hk : 0 < p₀ k) (hmax : ∀ j, 0 < p₀ j → j ≠ k → w j < w k) :
    Filter.Tendsto (fun t : ℕ => S^[t] p₀) Filter.atTop (nhds (Pi.single k 1 : ι → ℝ)) := by
  have hclosed : ∀ t : ℕ, ∀ i : ι, S^[t] p₀ i = p₀ i * w i ^ t / ∑ j, p₀ j * w j ^ t :=
    fun t i => iterate_select_apply w p₀ S hS hw hp₀ hsum t i
  have hnorm : ∀ t : ℕ, ∀ i : ι, S^[t] p₀ i
      = (p₀ i * (w i / w k) ^ t) / (∑ j, p₀ j * (w j / w k) ^ t) := by
    intro t i
    have hckt : (w k ^ t) ≠ 0 := pow_ne_zero t (ne_of_gt (hw k))
    rw [hclosed t i]
    have hpow : ∀ j : ι, (w j / w k) ^ t * w k ^ t = w j ^ t := by
      intro j
      rw [div_pow, div_mul_cancel₀ _ hckt]
    have h2 : (∑ j, p₀ j * w j ^ t) = (∑ j, p₀ j * (w j / w k) ^ t) * w k ^ t := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      calc p₀ j * w j ^ t = p₀ j * ((w j / w k) ^ t * w k ^ t) := by rw [hpow j]
        _ = (p₀ j * (w j / w k) ^ t) * w k ^ t := by ring
    rw [h2]
    have h1 : p₀ i * w i ^ t = (p₀ i * (w i / w k) ^ t) * w k ^ t := by
      calc p₀ i * w i ^ t = p₀ i * ((w i / w k) ^ t * w k ^ t) := by rw [hpow i]
        _ = (p₀ i * (w i / w k) ^ t) * w k ^ t := by ring
    rw [h1, mul_div_mul_right _ _ hckt]
  have hterm : ∀ j : ι, Filter.Tendsto (fun t : ℕ => p₀ j * (w j / w k) ^ t) Filter.atTop
      (nhds (if j = k then p₀ k else 0)) := by
    intro j
    by_cases hj : j = k
    · rw [hj, ite_eq_left rfl]
      simp only [div_self (ne_of_gt (hw k)), one_pow, mul_one]
      exact tendsto_const_nhds
    · rw [ite_eq_right hj]
      by_cases hj0 : p₀ j = 0
      · simp only [hj0, zero_mul]
        exact tendsto_const_nhds
      · have hpos : 0 < p₀ j := lt_of_le_of_ne (hp₀ j) (Ne.symm hj0)
        have hlt : w j / w k < 1 := (div_lt_one (hw k)).mpr (hmax j hpos hj)
        have hnn : 0 ≤ w j / w k := div_nonneg (le_of_lt (hw j)) (le_of_lt (hw k))
        have hpow : Filter.Tendsto (fun t : ℕ => (w j / w k) ^ t) Filter.atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt
        have hmul : Filter.Tendsto (fun t : ℕ => p₀ j * (w j / w k) ^ t) Filter.atTop
            (nhds (p₀ j * 0)) := tendsto_const_nhds.mul hpow
        rw [mul_zero] at hmul
        exact hmul
  have hE : Filter.Tendsto (fun t : ℕ => ∑ j, p₀ j * (w j / w k) ^ t) Filter.atTop
      (nhds (p₀ k)) := by
    have hsum1 : (∑ j, (if j = k then p₀ k else 0)) = p₀ k := by
      simp [Finset.sum_ite_eq']
    rw [← hsum1]
    exact tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  rw [tendsto_pi_nhds]
  intro i
  by_cases hi : i = k
  · rw [hi]
    rw [Pi.single_eq_same]
    have hlim : Filter.Tendsto (fun t : ℕ => p₀ k / (∑ j, p₀ j * (w j / w k) ^ t)) Filter.atTop
        (nhds (p₀ k / p₀ k)) := tendsto_const_nhds.div hE (ne_of_gt hk)
    rw [div_self (ne_of_gt hk)] at hlim
    refine Filter.Tendsto.congr (fun t => ?_) hlim
    rw [hnorm t k]
    congr 1
    rw [div_self (ne_of_gt (hw k)), one_pow, mul_one]
  · rw [Pi.single_eq_of_ne hi]
    have hNi : Filter.Tendsto (fun t : ℕ => p₀ i * (w i / w k) ^ t) Filter.atTop (nhds 0) := by
      have h := hterm i
      rw [ite_eq_right hi] at h
      exact h
    have hlim : Filter.Tendsto
        (fun t : ℕ => (p₀ i * (w i / w k) ^ t) / (∑ j, p₀ j * (w j / w k) ^ t))
        Filter.atTop (nhds (0 / p₀ k)) := hNi.div hE (ne_of_gt hk)
    rw [zero_div] at hlim
    refine Filter.Tendsto.congr (fun t => (hnorm t i).symm) hlim

end MathlibExt.Biology.PopulationGenetics.Classical.HaploidSelection

namespace MathlibExt.Biology.PopulationGenetics.Selection

/-- Closed form for iterating `Selection.select` with constant positive
fitnesses. -/
theorem iterate_select {ι : Type*} [Fintype ι] {w p₀ : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp₀ : ∀ i, 0 ≤ p₀ i) (hsum : ∑ i, p₀ i = 1)
    (t : ℕ) (i : ι) :
    (fun p => select p w)^[t] p₀ i =
      p₀ i * w i ^ t / ∑ j, p₀ j * w j ^ t :=
  MathlibExt.Biology.PopulationGenetics.Classical.HaploidSelection.iterate_select_apply
    w p₀ (fun p => select p w) (fun _ _ => rfl) hw hp₀ hsum t i

/-- Log-odds form for iterating `Selection.select` on two types. -/
theorem log_odds_iterate_select {w p₀ : Bool → ℝ}
    (hw : ∀ i, 0 < w i) (hp₀ : ∀ i, 0 < p₀ i) (hsum : ∑ i, p₀ i = 1)
    (t : ℕ) :
    Real.log ((fun p => select p w)^[t] p₀ true /
        (1 - (fun p => select p w)^[t] p₀ true)) =
      Real.log (p₀ true / (1 - p₀ true)) +
        (t : ℝ) * Real.log (w true / w false) :=
  MathlibExt.Biology.PopulationGenetics.Classical.HaploidSelection.log_odds_iterate_select
    w p₀ (fun p => select p w) (fun _ _ => rfl) hw hp₀ hsum t

/-- A type that is initially present and strictly fitter than every other
initially present type goes to fixation under iterated `Selection.select`;
initially absent types remain absent. -/
theorem tendsto_iterate_select_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w p₀ : ι → ℝ} (hw : ∀ i, 0 < w i) (hp₀ : ∀ i, 0 ≤ p₀ i)
    (hsum : ∑ i, p₀ i = 1) (k : ι) (hk : 0 < p₀ k)
    (hmax : ∀ j, 0 < p₀ j → j ≠ k → w j < w k) :
    Filter.Tendsto (fun t : ℕ => (fun p => select p w)^[t] p₀) Filter.atTop
      (nhds (Pi.single k 1 : ι → ℝ)) :=
  MathlibExt.Biology.PopulationGenetics.Classical.HaploidSelection.tendsto_iterate_select_pi_single
    w p₀ (fun p => select p w) (fun _ _ => rfl) hw hp₀ hsum k hk hmax

end MathlibExt.Biology.PopulationGenetics.Selection
