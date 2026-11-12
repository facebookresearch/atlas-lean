/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Bonferroni alpha allocation from a spending budget for repeated looks: type-I error control
under optional stopping

A clinical trial tests one null hypothesis at `K` pre-planned interim looks. At look `k + 1`
(`k < K`) the accumulated data give a p-value `p k`, and the trial stops with a rejection at the
first look whose p-value falls at or below that look's nominal level. The type-I error is the
probability, under the null, that **some** look rejects.

## This is not Lan–DeMets group-sequential boundaries

The procedure formalized here is a **Bonferroni allocation**: each look's spending increment
is used directly as a p-value cutoff, and type-I error control follows from the union bound
over the looks. It is *not* the Lan–DeMets procedure of Lan and DeMets (1983). In Lan–DeMets,
a spending increment is the allocated probability of first boundary crossing, and the
critical boundary at each look is derived from the joint null distribution of the test
statistics (for example the canonical joint law of a Brownian-motion score process); those
boundaries are generally larger than the spending increments and reject on a larger region
with the same total spend. The Lan–DeMets name below attaches only to the *shape* of the
spending budget (`pocockSpending`, a Lan–DeMets Pocock-type spending function), not to the
boundaries: no joint-law boundary, first-crossing spending constraint, or optimality claim is
formalized here.

Concretely, with two looks whose spending increments are `c₁, c₂ > 0` and independent
uniform p-values, the procedure rejects with probability `1 - (1 - c₁)(1 - c₂) =
c₁ + c₂ - c₁ * c₂ < c₁ + c₂` (`two_look_independent_gap` is the algebra), so it is
conservative relative to the spend: it is weighted Bonferroni, not exact Lan–DeMets.

## Fixed-family testing versus optional stopping

*Fixed-family testing* treats the `K` looks as `K` separate tests, each at level `α`. Every
single look then has type-I error at most `α`, but the trial's error is the probability of the
union of the per-look rejection events, and the union bound only gives `K α`
(`measure_rejectedLooks_const_nonempty_le`). The bound is attained:
`exists_rejectedLooks_const_typeI_eq` exhibits two valid looks at level `1/4` whose sequential
error is `1/2`. Testing each look at level `α` and stopping at the first rejection does not
control the error at `α`.

*Bonferroni allocation* fixes, before the trial, a spending function `f` with `f 0 = 0`,
monotone on `[0, 1]`, `f 1 ≤ α` (`IsAlphaSpendingFunction`) and information times
`0 = τ 0 ≤ τ 1 ≤ ⋯ ≤ τ K ≤ 1`. The theorems take `τ : ℕ → ℝ` with `Monotone τ`; a finite
schedule is extended by `τ k = τ K` for `k > K`, which leaves every planned look unchanged.
Look `k + 1` is tested at the nominal level (the Bonferroni cutoff on the p-value scale)
`bonferroniLookLevel f τ k = f (τ (k + 1)) - f (τ k)`: the spending increment is used
directly as the cutoff, not converted into a joint-law boundary. The nominal levels
telescope to `f (τ K) ≤ α` (`sum_bonferroniLookLevel_le`), so the probability that any
look rejects is at most `α` (`measure_rejectedLooks_bonferroniLookLevel_nonempty_le`).
Because that event contains the event "reject at the look where the trial stopped", the
guarantee holds for **every** stopping rule within the planned looks, including
data-dependent and non-adapted ones (`measure_reject_at_stopped_look_bonferroni_le`).

The chosen spending budget is the Lan–DeMets Pocock-type function
`pocockSpending α t = α log (1 + (e - 1) t)` (`isAlphaSpendingFunction_pocockSpending`), which
spends exactly `α` at `t = 1` (`pocockSpending_one`). Only its shape is Lan–DeMets; the
cutoffs are Bonferroni. The theorems hold for any `IsAlphaSpendingFunction`.

## Dependence across looks and endpoints

The proofs use only that each look's p-value is *marginally* valid under the null
(`IsValidPValue μ (p k)`). Nothing is assumed about the joint law of `(p 0, …, p (K - 1))`:
looks computed on overlapping cumulative data (strongly positively correlated, as for a
Brownian-motion score process) and arbitrary dependence across endpoints are covered. The price
is conservatism: exact group-sequential boundaries computed recursively from the joint
(canonical) law reject on a larger region with the same spend; those boundaries and any
optimality claim are not formalized here. Several endpoints are handled by splitting each
look's spend with weights summing to at most one (`measure_exists_look_endpoint_bonferroni_le`).

## Zero rejections

With no looks nothing is rejected (`rejectedLooks_zero`); p-values strictly above every
nominal level give no rejection (`rejectedLooks_eq_empty_of_forall_lt`); in particular, for
`α < 1` the all-ones p-values reject nothing
(`rejectedLooks_bonferroniLookLevel_eq_empty_of_eq_one`).

## Implementation notes

Reuse search (2026-11-11): Mathlib and MathlibExt have no alpha-spending, group-sequential, or
e-process development; Mathlib's Doob maximal inequality `MeasureTheory.maximal_ineq` is not
needed for this procedure. This file reuses `IsValidPValue` from `MultipleTesting.Basic`. The
union-bound step `measure_exists_le_level_le_sum` is a weighted form of the Bonferroni bound
`measure_exists_mem_le_le`.

## References

* K. K. G. Lan and D. L. DeMets, *Discrete sequential boundaries for clinical trials*,
  Biometrika 70 (1983), 659–663 (spending functions; the Pocock-type function
  `α log (1 + (e - 1) t)`).
* P. Armitage, C. K. McPherson and B. C. Rowe, *Repeated significance tests on accumulating
  data*, J. Roy. Statist. Soc. Ser. A 132 (1969), 235–244 (inflation of repeated testing at a
  fixed level).
* C. Jennison and B. W. Turnbull, *Group Sequential Methods with Applications to Clinical
  Trials*, Chapman & Hall/CRC (2000), Chapter 7.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Spending functions -/

/-- `f` is an *alpha-spending function* for level `α`: it spends nothing at information time
`0`, is monotone on `[0, 1]`, and has spent at most `α` at information time `1`.

Source: Lan and DeMets (1983). -/
structure IsAlphaSpendingFunction (α : ℝ) (f : ℝ → ℝ) : Prop where
  /-- Nothing is spent at information time `0`. -/
  map_zero : f 0 = 0
  /-- The cumulative spend is monotone in information time. -/
  monotoneOn : MonotoneOn f (Set.Icc 0 1)
  /-- At most `α` is spent by information time `1`. -/
  map_one_le : f 1 ≤ α

namespace IsAlphaSpendingFunction

variable {α : ℝ} {f : ℝ → ℝ}

/-- A spending function is nonnegative on `[0, 1]`. -/
theorem nonneg (hf : IsAlphaSpendingFunction α f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ f t :=
  hf.map_zero ▸ hf.monotoneOn ⟨le_rfl, zero_le_one⟩ ht ht.1

/-- A spending function is at most `α` on `[0, 1]`. -/
theorem le (hf : IsAlphaSpendingFunction α f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f t ≤ α :=
  (hf.monotoneOn ht ⟨zero_le_one, le_rfl⟩ ht.2).trans hf.map_one_le

end IsAlphaSpendingFunction

/-- The Lan–DeMets **Pocock-type spending function** `α log (1 + (e - 1) t)`.

Source: Lan and DeMets (1983). -/
noncomputable def pocockSpending (α t : ℝ) : ℝ :=
  α * Real.log (1 + (Real.exp 1 - 1) * t)

/-- The Pocock-type function spends nothing at time `0`. -/
@[simp]
theorem pocockSpending_zero (α : ℝ) : pocockSpending α 0 = 0 := by
  simp [pocockSpending]

/-- The Pocock-type function spends exactly `α` at time `1`. -/
@[simp]
theorem pocockSpending_one (α : ℝ) : pocockSpending α 1 = α := by
  simp [pocockSpending]

/-- For `α ≥ 0` the Pocock-type function is an alpha-spending function for level `α`. -/
theorem isAlphaSpendingFunction_pocockSpending {α : ℝ} (hα : 0 ≤ α) :
    IsAlphaSpendingFunction α (pocockSpending α) where
  map_zero := pocockSpending_zero α
  monotoneOn := by
    intro s hs t _ hst
    have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp 1]
    have hs0 : 0 ≤ (Real.exp 1 - 1) * s := mul_nonneg he hs.1
    have hst' : (Real.exp 1 - 1) * s ≤ (Real.exp 1 - 1) * t := mul_le_mul_of_nonneg_left hst he
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hα
  map_one_le := (pocockSpending_one α).le

/-! ### Per-look nominal levels -/

/-- The nominal level (Bonferroni cutoff on the p-value scale) of look `k + 1`: the spending
increment `f (τ (k + 1)) - f (τ k)` accrued since the previous look, used directly as the
cutoff. This is not a Lan–DeMets critical value: Lan–DeMets boundaries are derived from the
joint null law and are generally larger. The convention `τ 0 = 0` marks the start of the
trial. -/
noncomputable def bonferroniLookLevel (f : ℝ → ℝ) (τ : ℕ → ℝ) (k : ℕ) : ℝ :=
  f (τ (k + 1)) - f (τ k)

/-- The looks among the first `K` whose p-value is at most the nominal level `c k`. The trial
rejects the null iff this set is nonempty; under optional stopping it stops at its least
element. -/
noncomputable def rejectedLooks (K : ℕ) (c : ℕ → ℝ) (p : ℕ → ℝ) : Finset ℕ :=
  (Finset.range K).filter fun k => p k ≤ c k

/-- The nominal levels telescope to the total spend `f (τ K) - f (τ 0)`. -/
theorem sum_bonferroniLookLevel (f : ℝ → ℝ) (τ : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, bonferroniLookLevel f τ k = f (τ K) - f (τ 0) :=
  Finset.sum_range_sub (fun k => f (τ k)) K

section Spend

variable {α : ℝ} {f : ℝ → ℝ} {τ : ℕ → ℝ} {K : ℕ}

private theorem mem_Icc_of_le_horizon (hτ0 : τ 0 = 0) (hτ : Monotone τ) (hτK : τ K ≤ 1)
    {k : ℕ} (hk : k ≤ K) : τ k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hτ0 ▸ hτ (Nat.zero_le k), (hτ hk).trans hτK⟩

/-- Each planned look has a nonnegative nominal level. -/
theorem bonferroniLookLevel_nonneg (hf : IsAlphaSpendingFunction α f) (hτ0 : τ 0 = 0)
    (hτ : Monotone τ) (hτK : τ K ≤ 1) {k : ℕ} (hk : k < K) :
    0 ≤ bonferroniLookLevel f τ k :=
  sub_nonneg.2 <| hf.monotoneOn (mem_Icc_of_le_horizon hτ0 hτ hτK hk.le)
    (mem_Icc_of_le_horizon hτ0 hτ hτK hk) (hτ k.le_succ)

/-- Each planned look has nominal level at most `α`. -/
theorem bonferroniLookLevel_le (hf : IsAlphaSpendingFunction α f) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) {k : ℕ} (hk : k < K) : bonferroniLookLevel f τ k ≤ α := by
  have h1 := hf.le (mem_Icc_of_le_horizon hτ0 hτ hτK hk)
  have h0 := hf.nonneg (mem_Icc_of_le_horizon hτ0 hτ hτK hk.le)
  unfold bonferroniLookLevel
  linarith

/-- **Spending accounting.** The nominal levels of the `K` planned looks sum to at most `α`. -/
theorem sum_bonferroniLookLevel_le (hf : IsAlphaSpendingFunction α f) (hτ0 : τ 0 = 0)
    (hτ : Monotone τ) (hτK : τ K ≤ 1) :
    ∑ k ∈ Finset.range K, bonferroniLookLevel f τ k ≤ α := by
  rw [sum_bonferroniLookLevel, hτ0, hf.map_zero, sub_zero]
  exact hf.le (mem_Icc_of_le_horizon hτ0 hτ hτK le_rfl)

end Spend

/-- **Conservatism gap for two independent looks.** If two looks have spending increments
`c₁, c₂ ≥ 0` and independent uniform p-values, the procedure rejects with probability
`1 - (1 - c₁)(1 - c₂)`, which equals `c₁ + c₂ - c₁ * c₂` and is at most the Bonferroni
bound `c₁ + c₂`, with gap `c₁ * c₂`. This is the algebra behind the claim that the
procedure is conservative weighted Bonferroni, not exact Lan–DeMets: the joint-law
calculation itself is not formalized, only the resulting real identity. -/
theorem two_look_independent_gap {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    1 - (1 - c₁) * (1 - c₂) = c₁ + c₂ - c₁ * c₂ ∧
      1 - (1 - c₁) * (1 - c₂) ≤ c₁ + c₂ := by
  refine ⟨by ring, ?_⟩
  rw [show 1 - (1 - c₁) * (1 - c₂) = c₁ + c₂ - c₁ * c₂ by ring]
  exact sub_le_self _ (mul_nonneg hc₁ hc₂)

/-! ### Type-I error control -/

/-- **Weighted union bound for valid p-values.** If each `p i` (`i ∈ s`) is a valid p-value and
`c i ∈ [0, 1]`, the probability that some `p i` is at most `c i` is at most `∑ c i`. No
assumption is made on the joint law of the p-values. -/
theorem measure_exists_le_level_le_sum (μ : Measure Ω) {ι : Type*} (s : Finset ι)
    (p : ι → Ω → ℝ) (c : ι → ℝ) (hp : ∀ i ∈ s, IsValidPValue μ (p i))
    (hc : ∀ i ∈ s, c i ∈ Set.Icc (0 : ℝ) 1) :
    μ {ω | ∃ i ∈ s, p i ω ≤ c i} ≤ ENNReal.ofReal (∑ i ∈ s, c i) := by
  have hset : {ω | ∃ i ∈ s, p i ω ≤ c i} = ⋃ i ∈ s, {ω | p i ω ≤ c i} := by
    ext ω
    simp
  rw [hset, ENNReal.ofReal_sum_of_nonneg fun i hi => (hc i hi).1]
  exact (measure_biUnion_finset_le s _).trans
    (Finset.sum_le_sum fun i hi => hp i hi (c i) (hc i hi))

section Control

variable {α : ℝ} {f : ℝ → ℝ} {τ : ℕ → ℝ} {K : ℕ}

/-- **Bonferroni allocation controls the type-I error.** If the p-value of each of the `K` planned
looks is valid under the null, the probability that the Bonferroni allocation rejects at
some look is at most `α`. Only marginal validity is used: the looks may have any joint law.

Source: Lan and DeMets (1983); Jennison and Turnbull (2000), Chapter 7. -/
theorem measure_rejectedLooks_bonferroniLookLevel_nonempty_le (μ : Measure Ω) (p : ℕ → Ω → ℝ)
    (hf : IsAlphaSpendingFunction α f) (hα : α ≤ 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) (hnull : ∀ k < K, IsValidPValue μ (p k)) :
    μ {ω | (rejectedLooks K (bonferroniLookLevel f τ) fun k => p k ω).Nonempty} ≤
      ENNReal.ofReal α := by
  have hset : {ω | (rejectedLooks K (bonferroniLookLevel f τ) fun k => p k ω).Nonempty} =
      {ω | ∃ k ∈ Finset.range K, p k ω ≤ bonferroniLookLevel f τ k} := by
    ext ω
    simp [rejectedLooks, Finset.Nonempty]
  rw [hset]
  refine (measure_exists_le_level_le_sum μ _ p _
    (fun k hk => hnull k (Finset.mem_range.1 hk)) fun k hk => ?_).trans
    (ENNReal.ofReal_le_ofReal (sum_bonferroniLookLevel_le hf hτ0 hτ hτK))
  have hk := Finset.mem_range.1 hk
  exact ⟨bonferroniLookLevel_nonneg hf hτ0 hτ hτK hk,
    (bonferroniLookLevel_le hf hτ0 hτ hτK hk).trans hα⟩

/-- **Optional stopping.** For any rule `N` choosing the look at which the trial stops, which may
depend on the data arbitrarily (it need not be a stopping time), the probability of stopping at
a planned look with a rejection is at most `α`. -/
theorem measure_reject_at_stopped_look_bonferroni_le (μ : Measure Ω) (p : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (hf : IsAlphaSpendingFunction α f) (hα : α ≤ 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) (hnull : ∀ k < K, IsValidPValue μ (p k)) :
    μ {ω | N ω < K ∧ p (N ω) ω ≤ bonferroniLookLevel f τ (N ω)} ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans
    (measure_rejectedLooks_bonferroniLookLevel_nonempty_le μ p hf hα hτ0 hτ hτK hnull)
  intro ω hω
  exact ⟨N ω, Finset.mem_filter.2 ⟨Finset.mem_range.2 hω.1, hω.2⟩⟩

/-- **Multiple endpoints.** At each look, test endpoint `j ∈ E` at level `w j` times that look's
spend, with weights `w j ≥ 0` summing to at most one. If every endpoint's p-value at every look
is valid under the (global) null, the probability of any rejection is at most `α`. No
assumption is made on the dependence across looks or endpoints. -/
theorem measure_exists_look_endpoint_bonferroni_le (μ : Measure Ω) {ι : Type*} (E : Finset ι)
    (p : ℕ → ι → Ω → ℝ) (w : ι → ℝ) (hw0 : ∀ j ∈ E, 0 ≤ w j) (hw1 : ∑ j ∈ E, w j ≤ 1)
    (hf : IsAlphaSpendingFunction α f) (hα : α ≤ 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) (hnull : ∀ k < K, ∀ j ∈ E, IsValidPValue μ (p k j)) :
    μ {ω | ∃ k < K, ∃ j ∈ E, p k j ω ≤ w j * bonferroniLookLevel f τ k} ≤ ENNReal.ofReal α := by
  have hset : {ω | ∃ k < K, ∃ j ∈ E, p k j ω ≤ w j * bonferroniLookLevel f τ k} =
      {ω | ∃ i ∈ Finset.range K ×ˢ E, p i.1 i.2 ω ≤ w i.2 * bonferroniLookLevel f τ i.1} := by
    ext ω
    simp [and_assoc]
  rw [hset]
  refine (measure_exists_le_level_le_sum μ _ (fun i : ℕ × ι => p i.1 i.2)
    (fun i : ℕ × ι => w i.2 * bonferroniLookLevel f τ i.1)
    (fun i hi => ?_) fun i hi => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [Finset.mem_product, Finset.mem_range] at hi
    exact hnull i.1 hi.1 i.2 hi.2
  · rw [Finset.mem_product, Finset.mem_range] at hi
    have hs0 := bonferroniLookLevel_nonneg hf hτ0 hτ hτK hi.1
    have hs1 := (bonferroniLookLevel_le hf hτ0 hτ hτK hi.1).trans hα
    have hw := (Finset.single_le_sum hw0 hi.2).trans hw1
    exact ⟨mul_nonneg (hw0 _ hi.2) hs0, by nlinarith⟩
  · rw [Finset.sum_product]
    calc ∑ k ∈ Finset.range K, ∑ j ∈ E, w j * bonferroniLookLevel f τ k
        = ∑ k ∈ Finset.range K, (∑ j ∈ E, w j) * bonferroniLookLevel f τ k := by
          simp [Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.range K, bonferroniLookLevel f τ k := Finset.sum_le_sum fun k hk =>
          mul_le_of_le_one_left
            (bonferroniLookLevel_nonneg hf hτ0 hτ hτK (Finset.mem_range.1 hk)) hw1
      _ ≤ α := sum_bonferroniLookLevel_le hf hτ0 hτ hτK

end Control

/-! ### Zero rejections -/

/-- With no planned look, nothing is rejected. -/
@[simp]
theorem rejectedLooks_zero (c p : ℕ → ℝ) : rejectedLooks 0 c p = ∅ := by
  simp [rejectedLooks]

/-- If every planned look's p-value exceeds its nominal level, nothing is rejected. -/
theorem rejectedLooks_eq_empty_of_forall_lt {K : ℕ} {c p : ℕ → ℝ} (h : ∀ k < K, c k < p k) :
    rejectedLooks K c p = ∅ :=
  Finset.filter_eq_empty_iff.2 fun k hk => not_le.2 (h k (Finset.mem_range.1 hk))

/-- **Zero rejections.** For `α < 1`, the Bonferroni allocation rejects nothing when every
p-value equals `1`. -/
theorem rejectedLooks_bonferroniLookLevel_eq_empty_of_eq_one {α : ℝ} {f : ℝ → ℝ} {τ : ℕ → ℝ} {K : ℕ}
    (hf : IsAlphaSpendingFunction α f) (hα : α < 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) : rejectedLooks K (bonferroniLookLevel f τ) (fun _ => 1) = ∅ :=
  rejectedLooks_eq_empty_of_forall_lt fun _ hk =>
    (bonferroniLookLevel_le hf hτ0 hτ hτK hk).trans_lt hα

/-! ### Fixed-family testing at level `α` per look -/

/-- **Fixed-family testing gives only `K α`.** Testing each of `K` valid looks at level
`α ∈ [0, 1]` and rejecting if any look rejects has type-I error at most `K α`; the bound is
attained (`exists_rejectedLooks_const_typeI_eq`), so it does not control the error at `α`. -/
theorem measure_rejectedLooks_const_nonempty_le (μ : Measure Ω) (p : ℕ → Ω → ℝ) {α : ℝ}
    {K : ℕ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hnull : ∀ k < K, IsValidPValue μ (p k)) :
    μ {ω | (rejectedLooks K (fun _ => α) fun k => p k ω).Nonempty} ≤
      ENNReal.ofReal (K * α) := by
  have hset : {ω | (rejectedLooks K (fun _ => α) fun k => p k ω).Nonempty} =
      {ω | ∃ k ∈ Finset.range K, p k ω ≤ α} := by
    ext ω
    simp [rejectedLooks, Finset.Nonempty]
  rw [hset]
  simpa using measure_exists_le_level_le_sum μ (Finset.range K) p (fun _ => α)
    (fun k hk => hnull k (Finset.mem_range.1 hk)) fun _ _ => ⟨hα₀, hα₁⟩

/-- A two-valued p-value, equal to `c` on a set of measure at most `c` and to `1` elsewhere, is
valid under a probability measure. -/
private theorem isValidPValue_ite (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
    [DecidablePred (· ∈ A)] {c : ℝ} (hc : c ≤ 1) (hA : μ A ≤ ENNReal.ofReal c) :
    IsValidPValue μ fun ω => if ω ∈ A then c else 1 := by
  intro t ht
  rcases lt_or_ge t c with htc | hct
  · have : {ω | (if ω ∈ A then c else 1) ≤ t} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      split_ifs <;> linarith
    simp [this]
  rcases lt_or_ge t 1 with ht1 | ht1
  · refine (measure_mono fun ω hω => ?_).trans (hA.trans (ENNReal.ofReal_le_ofReal hct))
    by_contra h
    simp only [Set.mem_ofPred_eq, h, ite_false] at hω
    linarith
  · calc μ _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal t := by simpa using ENNReal.ofReal_le_ofReal ht1

/-- **Computed inflation example.** On four equally likely outcomes, two looks with valid
p-values tested at level `1/4` each reject on disjoint events, so the sequential type-I error
is `2 · 1/4 = 1/2`: twice the per-look level. -/
theorem exists_rejectedLooks_const_typeI_eq :
    ∃ (μ : Measure (Fin 4)) (p : ℕ → Fin 4 → ℝ), IsProbabilityMeasure μ ∧
      (∀ k < 2, IsValidPValue μ (p k)) ∧
      μ {ω | (rejectedLooks 2 (fun _ => 1 / 4) fun k => p k ω).Nonempty} =
        ENNReal.ofReal (2 * (1 / 4)) ∧
      ENNReal.ofReal (1 / 4) < ENNReal.ofReal (2 * (1 / 4)) := by
  set μ : Measure (Fin 4) := (4 : ENNReal)⁻¹ • Measure.count
  have hμ : ∀ s : Finset (Fin 4), μ s = (4 : ENNReal)⁻¹ * s.card := fun s => by
    simp [μ]
  have : IsProbabilityMeasure μ := ⟨by
    rw [← Finset.coe_univ, hμ]
    simp [ENNReal.inv_mul_cancel]⟩
  refine ⟨μ, fun k ω => if (ω : ℕ) = k then 1 / 4 else 1, inferInstance, fun k _ => ?_, ?_,
    ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by norm_num, by norm_num⟩⟩
  · have hk := isValidPValue_ite μ {ω : Fin 4 | (ω : ℕ) = k} (c := 1 / 4) (by norm_num) ?_
    · simpa using hk
    calc μ {ω : Fin 4 | (ω : ℕ) = k}
        ≤ μ ((Finset.univ.filter fun ω : Fin 4 => (ω : ℕ) = k : Finset (Fin 4)) : Set (Fin 4)) :=
          measure_mono fun ω hω => by simpa using hω
      _ ≤ ENNReal.ofReal (1 / 4) := by
          rw [hμ]
          have : (Finset.univ.filter fun ω : Fin 4 => (ω : ℕ) = k).card ≤ 1 :=
            Finset.card_le_one.2 fun a ha b hb => by
              simp only [Finset.mem_filter] at ha hb
              exact Fin.ext (ha.2.trans hb.2.symm)
          calc (4 : ENNReal)⁻¹ * ((Finset.univ.filter fun ω : Fin 4 => (ω : ℕ) = k).card : ENNReal)
              ≤ (4 : ENNReal)⁻¹ * 1 := by gcongr; exact_mod_cast this
            _ = ENNReal.ofReal (1 / 4) := by
              rw [mul_one, ENNReal.ofReal_div_of_pos (by norm_num)]
              simp
  · have hset : {ω : Fin 4 | (rejectedLooks 2 (fun _ => 1 / 4)
        fun k => if (ω : ℕ) = k then (1 / 4 : ℝ) else 1).Nonempty} = (({0, 1} : Finset (Fin 4)) :
          Set (Fin 4)) := by
      ext ω
      fin_cases ω <;> simp only [rejectedLooks, Finset.Nonempty, Finset.mem_filter,
        Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      · exact iff_of_true ⟨0, by norm_num⟩ (Or.inl rfl)
      · exact iff_of_true ⟨1, by norm_num⟩ (Or.inr rfl)
      · refine iff_of_false ?_ (by decide)
        rintro ⟨x, hx, h⟩
        split_ifs at h with hx2 <;> norm_num at hx2 h; omega
      · refine iff_of_false ?_ (by decide)
        rintro ⟨x, hx, h⟩
        split_ifs at h with hx2 <;> norm_num at hx2 h; omega
    rw [hset, hμ]
    rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.card_insert_of_notMem,
      Finset.card_singleton, Nat.reduceAdd, Nat.cast_ofNat, ENNReal.ofReal_one, one_div,
      ENNReal.ofReal_ofNat]
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num)), mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
      mul_one]

end MathlibExt.Probability.Statistics.MultipleTesting
