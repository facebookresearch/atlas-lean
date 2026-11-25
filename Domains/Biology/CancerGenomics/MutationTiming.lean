/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Molecular timing of copy-number gains from mutation multiplicities

Point mutations accumulate on every copy of a region at a constant rate `μ` per copy per unit
time. A single copy-number event at time `t` (the tumor's history normalized to `[0, 1]`)
replaces each of the `c₀` original copies `i` by `desc i` copies (`0` for a lost copy, `2` for a
duplicated one). A mutation acquired before the event on copy `i` is carried by all `desc i`
descendants, so it has multiplicity `desc i`; a mutation acquired after the event has
multiplicity `1`. The expected number of mutations of multiplicity `m` is therefore

`E_m = μ t #{i | desc i = m} + [m = 1] μ c₁ (1 - t)`, with `c₁ = ∑ i, desc i`.

This is the single-event case of the model `q = A π` of Purdom et al. (2013, §2.1), linking
the multiplicity spectrum to the time spent in each copy-number stage, and the model behind
the gain timing of Gerstung et al. (2020).

## Main results

* `sum_mul_expectedCount`: the multiplicity-weighted total `∑_m m E_m = μ c₁` does not depend
  on `t`.
* `sum_expectedCount_amplified`: the mutations of multiplicity `≥ 2` number
  `μ t #{i | desc i ≥ 2}`.
* `timing_eq`, `rate_eq`: **closed forms** `t = c₁ ∑_{m ≥ 2} E_m / (#{i | desc i ≥ 2} ∑_m m E_m)`
  and `μ = ∑_m m E_m / c₁`, whenever some copy is amplified.
* `expectedCount_injective`: hence `(μ, t)` is identifiable from the multiplicity spectrum.
* `singleGain_timing`, `cnLOH_timing`, `wgd_timing`: the familiar special cases
  `t = 3 E₂ / (E₁ + 2 E₂)` (gain `1 + 1 → 2 + 1`), `t = 2 E₂ / (E₁ + 2 E₂)` (copy-neutral LOH
  `1 + 1 → 2 + 0`) and `t = 2 E₂ / (E₁ + 2 E₂)` (doubling `1 + 1 → 2 + 2`).

The identities hold for all real `t`; the biological domain is `μ > 0`, `0 ≤ t ≤ 1`.
The closed forms are derived here from the model, with the per-copy rate normalization above;
Purdom et al. state only the general linear relation `q = A π`. They are exact identities for
expected counts; plugging in observed counts gives the usual moment estimators.

## References

* E. Purdom, C. Ho, C. S. Grasso, M. J. Quist, R. J. Cho, P. Spellman, *Methods and
  challenges in timing chromosomal abnormalities within cancer samples*, Bioinformatics 29
  (2013), 3113–3120.
* M. Gerstung et al., *The evolutionary history of 2,658 cancers*, Nature 578 (2020),
  122–128.
-/

@[expose] public section

namespace MathlibExt.Biology.CancerGenomics.MutationTiming

open Finset

/-- A single copy-number event on a region: `copies` original copies, of which copy `i` has
`desc i` copies after the event (`0` if lost, `2` if duplicated). -/
structure GainHistory where
  /-- The number of copies of the region before the event. -/
  copies : ℕ
  /-- The number of copies descending from each original copy after the event. -/
  desc : Fin copies → ℕ

namespace GainHistory

/-- The copy number `c₁ = ∑ i, desc i` after the event. -/
def finalCopies (h : GainHistory) : ℕ := ∑ i, h.desc i

/-- The number of original copies amplified by the event (`desc i ≥ 2`). -/
def amplified (h : GainHistory) : ℕ := (univ.filter fun i => 2 ≤ h.desc i).card

/-- Expected number of mutations of multiplicity `m`:
`μ t #{i | desc i = m} + [m = 1] μ c₁ (1 - t)` (per-copy rate `μ`, event at time `t` of the
normalized history `[0, 1]`). -/
noncomputable def expectedCount (h : GainHistory) (μ t : ℝ) (m : ℕ) : ℝ :=
  μ * t * ((univ.filter fun i => h.desc i = m).card : ℝ) +
    if m = 1 then μ * h.finalCopies * (1 - t) else 0

private theorem sum_mul_card_filter (h : GainHistory) {B : ℕ} (hB : ∀ i, h.desc i ≤ B) :
    ∑ m ∈ range (B + 1), (m : ℝ) * ((univ.filter fun i => h.desc i = m).card : ℝ) =
      h.finalCopies := by
  simp_rw [card_filter, Nat.cast_sum, mul_sum]
  rw [sum_comm, finalCopies, Nat.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq (range (B + 1)) (h.desc i) fun m => (m : ℝ)]
  simp [Nat.lt_succ_of_le (hB i)]

/-- **The multiplicity-weighted total is time-invariant**: `∑_m m E_m = μ c₁`, summing over
all multiplicities up to a bound `B ≥ max(1, max_i desc i)`. -/
theorem sum_mul_expectedCount (h : GainHistory) (μ t : ℝ) {B : ℕ} (hB : ∀ i, h.desc i ≤ B)
    (hB1 : 1 ≤ B) :
    ∑ m ∈ range (B + 1), (m : ℝ) * h.expectedCount μ t m = μ * h.finalCopies := by
  unfold expectedCount
  simp_rw [mul_add, sum_add_distrib]
  have h1 : ∑ m ∈ range (B + 1), (m : ℝ) * (μ * t * ((univ.filter fun i =>
      h.desc i = m).card : ℝ)) = μ * t * h.finalCopies := by
    rw [← sum_mul_card_filter h hB, mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have h2 : ∑ m ∈ range (B + 1), (m : ℝ) * (if m = 1 then μ * h.finalCopies * (1 - t) else 0) =
      μ * h.finalCopies * (1 - t) := by
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq' (range (B + 1)) 1]
    simp [Nat.lt_succ_of_le hB1]
  rw [h1, h2]
  ring

/-- The mutations of multiplicity at least two number `μ t #{i | desc i ≥ 2}` in expectation:
they all arose before the event, on an amplified copy. -/
theorem sum_expectedCount_amplified (h : GainHistory) (μ t : ℝ) {B : ℕ}
    (hB : ∀ i, h.desc i ≤ B) :
    ∑ m ∈ Ico 2 (B + 1), h.expectedCount μ t m = μ * t * h.amplified := by
  unfold expectedCount amplified
  have hz : ∑ m ∈ Ico 2 (B + 1), (if m = 1 then μ * h.finalCopies * (1 - t) else 0) = 0 :=
    sum_eq_zero fun m hm => by
      have : m ≠ 1 := by have := (mem_Ico.1 hm).1; omega
      simp [this]
  rw [sum_add_distrib, hz, add_zero, ← mul_sum]
  congr 1
  rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := h.desc) (t := Ico 2 (B + 1))]
  · simp only [filter_filter]
    refine congrArg _ (sum_congr rfl fun m hm => congrArg _ (filter_congr fun i _ => ?_))
    have := (mem_Ico.1 hm).1
    constructor
    · rintro rfl; exact ⟨this, rfl⟩
    · rintro ⟨_, h⟩; exact h
  · intro i hi
    exact mem_Ico.2 ⟨(mem_filter.1 hi).2, Nat.lt_succ_of_le (hB i)⟩

/-- An event that amplifies some copy leaves a positive copy number. -/
theorem finalCopies_pos {h : GainHistory} (ha : 0 < h.amplified) : 0 < h.finalCopies := by
  obtain ⟨i, hi⟩ := card_pos.1 ha
  have h2 := (mem_filter.1 hi).2
  have := single_le_sum (f := h.desc) (fun j _ => Nat.zero_le _) (mem_univ i)
  unfold finalCopies; omega

/-- **The mutation rate from the spectrum**: `μ = ∑_m m E_m / c₁` (`c₁ > 0`). -/
theorem rate_eq (h : GainHistory) (μ t : ℝ) {B : ℕ} (hB : ∀ i, h.desc i ≤ B) (hB1 : 1 ≤ B)
    (hc : 0 < h.finalCopies) :
    μ = (∑ m ∈ range (B + 1), (m : ℝ) * h.expectedCount μ t m) / h.finalCopies := by
  have hc' : (0 : ℝ) < h.finalCopies := by exact_mod_cast hc
  rw [sum_mul_expectedCount h μ t hB hB1]
  field_simp

/-- **The timing closed form**: when some copy is amplified and `μ ≠ 0`,
`t = c₁ ∑_{m ≥ 2} E_m / (#{i | desc i ≥ 2} ∑_m m E_m)`. -/
theorem timing_eq (h : GainHistory) {μ : ℝ} (t : ℝ) (hμ : μ ≠ 0) {B : ℕ}
    (hB : ∀ i, h.desc i ≤ B) (hB1 : 1 ≤ B) (ha : 0 < h.amplified) :
    t = h.finalCopies * (∑ m ∈ Ico 2 (B + 1), h.expectedCount μ t m) /
      (h.amplified * ∑ m ∈ range (B + 1), (m : ℝ) * h.expectedCount μ t m) := by
  have hc' : (0 : ℝ) < h.finalCopies := by exact_mod_cast finalCopies_pos ha
  have ha' : (0 : ℝ) < h.amplified := by exact_mod_cast ha
  rw [sum_mul_expectedCount h μ t hB hB1, sum_expectedCount_amplified h μ t hB]
  field_simp

/-- **Identifiability**: if some copy is amplified, two parameter pairs `(μ, t)`, `(μ', t')`
with `μ, μ' ≠ 0` and the same expected multiplicity spectrum are equal. -/
theorem expectedCount_injective (h : GainHistory) {μ μ' t t' : ℝ} (hμ : μ ≠ 0) (hμ' : μ' ≠ 0)
    (ha : 0 < h.amplified) (heq : h.expectedCount μ t = h.expectedCount μ' t') :
    μ = μ' ∧ t = t' := by
  set B := max 1 (∑ i, h.desc i)
  have hB : ∀ i, h.desc i ≤ B := fun i =>
    le_max_of_le_right (single_le_sum (f := h.desc) (fun j _ => Nat.zero_le _) (mem_univ i))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hc := finalCopies_pos ha
  refine ⟨?_, ?_⟩
  · rw [rate_eq h μ t hB hB1 hc, rate_eq h μ' t' hB hB1 hc, heq]
  · rw [timing_eq h t hμ hB hB1 ha, timing_eq h t' hμ' hB hB1 ha, heq]

/-- A single-copy gain `1 + 1 → 2 + 1`: one copy duplicated, the other kept. -/
def singleGain : GainHistory := ⟨2, ![2, 1]⟩

/-- Copy-neutral loss of heterozygosity `1 + 1 → 2 + 0`: one copy duplicated, the other lost. -/
def cnLOH : GainHistory := ⟨2, ![2, 0]⟩

/-- Whole-genome doubling of a diploid region `1 + 1 → 2 + 2`. -/
def wgd : GainHistory := ⟨2, ![2, 2]⟩

/-- **Single gain** (`2 + 1`): `t = 3 E₂ / (E₁ + 2 E₂)`, for `μ ≠ 0`. -/
theorem singleGain_timing {μ : ℝ} (t : ℝ) (hμ : μ ≠ 0) :
    t = 3 * singleGain.expectedCount μ t 2 /
      (singleGain.expectedCount μ t 1 + 2 * singleGain.expectedCount μ t 2) := by
  have c1 : (univ.filter fun i => singleGain.desc i = 1).card = 1 := by decide
  have c2 : (univ.filter fun i => singleGain.desc i = 2).card = 1 := by decide
  have f : singleGain.finalCopies = 3 := by decide
  simp only [expectedCount, c1, c2, f]
  norm_num
  field_simp
  ring

/-- **Copy-neutral LOH** (`2 + 0`): `t = 2 E₂ / (E₁ + 2 E₂)`, for `μ ≠ 0`. -/
theorem cnLOH_timing {μ : ℝ} (t : ℝ) (hμ : μ ≠ 0) :
    t = 2 * cnLOH.expectedCount μ t 2 /
      (cnLOH.expectedCount μ t 1 + 2 * cnLOH.expectedCount μ t 2) := by
  have c1 : (univ.filter fun i => cnLOH.desc i = 1).card = 0 := by decide
  have c2 : (univ.filter fun i => cnLOH.desc i = 2).card = 1 := by decide
  have f : cnLOH.finalCopies = 2 := by decide
  simp only [expectedCount, c1, c2, f]
  norm_num
  field_simp
  ring

/-- **Whole-genome doubling** (`2 + 2`): `t = 2 E₂ / (E₁ + 2 E₂)`, for `μ ≠ 0`. -/
theorem wgd_timing {μ : ℝ} (t : ℝ) (hμ : μ ≠ 0) :
    t = 2 * wgd.expectedCount μ t 2 /
      (wgd.expectedCount μ t 1 + 2 * wgd.expectedCount μ t 2) := by
  have c1 : (univ.filter fun i => wgd.desc i = 1).card = 0 := by decide
  have c2 : (univ.filter fun i => wgd.desc i = 2).card = 2 := by decide
  have f : wgd.finalCopies = 4 := by decide
  simp only [expectedCount, c1, c2, f]
  norm_num
  field_simp
  ring

end GainHistory

end MathlibExt.Biology.CancerGenomics.MutationTiming
