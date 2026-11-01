/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.CancerGenomics.DetectionPower
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Binomial saturation power for cancer gene discovery

Lawrence et al. (2014, Methods, "Power calculations") use a binomial power model. With `N`
patients, the number of patients carrying a non-silent mutation in a gene is binomial. Under
the background model each patient is mutated with probability
`p₀ = 1 - (1 - μ f_g)^(3L/4)` (gene length `L` coding bases, background rate `μ` per base,
gene factor `f_g`, a 3 : 1 non-silent : silent ratio); a driver mutated in a fraction `r` of
patients above background, detected with miss rate `m`, raises it to `p₁ = p₀ + r (1 - m)`.
Power is the probability under `p₁` of a p-value `ℙ_{p₀}(X ≥ x) ≤ γ` (they take
`γ = 0.1 / 20000`), and `N₉₀` is the cohort size giving 90% power.

This file proves that the model is well posed: for every level `γ > 0` and every `p₁ > p₀`,
power tends to `1` as `N → ∞`, so for every target power `β < 1` there is a cohort size beyond
which power is at least `β`. Power is not monotone in `N` (the binomial test is discrete), so
the statement is "eventually", not "from the first `N` that reaches `β`".

## Main results

* `saturationPower`: `ℙ_{p₁}(ℙ_{p₀}(X ≥ x) ≤ γ)` for `X ~ Bin(N, ·)`.
* `tendsto_saturationPower`: power tends to `1` when `0 ≤ p₀ < p₁ ≤ 1` and `0 < γ`.
* `eventually_le_saturationPower`: for every `β < 1`, power is eventually at least `β`
  (`N₉₀` exists, `β = 0.9`).
* `lawrenceP0_mem`, `lawrenceP0_lt_lawrenceP1`: the Lawrence et al. parameters satisfy the
  hypotheses when `0 ≤ μ f_g ≤ 1`, `r > 0`, `m < 1` and `p₁ ≤ 1`.

## References

* M. S. Lawrence et al., *Discovery and saturation analysis of cancer genes across 21 tumour
  types*, Nature 505 (2014), 495–501 (Methods, "Power calculations").
-/

@[expose] public section

namespace MathlibExt.Biology.CancerGenomics.SaturationPower

open Finset Filter Topology MathlibExt.Biology.CancerGenomics.DetectionPower

/-- Power of the one-sided binomial test of Lawrence et al. (2014): the probability, when each
of `N` patients is mutated with probability `p₁`, of observing a count `x` whose background
p-value `ℙ_{p₀}(X ≥ x)` is at most `γ`. -/
noncomputable def saturationPower (N : ℕ) (p₀ p₁ γ : ℝ) : ℝ :=
  ∑ x ∈ range (N + 1) with upperTail N p₀ x ≤ γ, binomPmf N p₁ x

/-- Background probability `p₀ = 1 - (1 - μ f_g)^(3L/4)` that a patient carries at least one
non-silent background mutation in a gene of `L` coding bases (Lawrence et al. 2014). -/
noncomputable def lawrenceP0 (μ fg L : ℝ) : ℝ := 1 - (1 - μ * fg) ^ (3 * L / 4)

/-- Signal probability `p₁ = p₀ + r (1 - m)` for a gene mutated in a fraction `r` of patients
above background, with miss rate `m` (Lawrence et al. 2014). -/
def lawrenceP1 (p₀ r m : ℝ) : ℝ := p₀ + r * (1 - m)

private theorem pmf_nonneg (n i : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ binomPmf n p i := by
  unfold binomPmf
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp') _)

private theorem pmf_sum (n : ℕ) (p : ℝ) :
    ∑ i ∈ range (n + 1), binomPmf n p i = 1 := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ n)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, binomPmf] using h

private theorem pmf_variance (n : ℕ) (p : ℝ) :
    ∑ i ∈ range (n + 1), ((i : ℝ) - n * p) ^ 2 * binomPmf n p i =
      n * p * (1 - p) := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ n)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, binomPmf, nsmul_eq_mul,
    sub_sq_comm] using h

private theorem concentration (n : ℕ) {p d : ℝ} (hn : 0 < n) (hp : 0 ≤ p)
    (hp' : p ≤ 1) (hd : 0 < d) (s : Finset ℕ) (hs : s ⊆ range (n + 1))
    (hdev : ∀ i ∈ s, ((n : ℝ) * d) ^ 2 ≤ ((i : ℝ) - n * p) ^ 2) :
    ∑ i ∈ s, binomPmf n p i ≤ (p * (1 - p) / d ^ 2) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < ((n : ℝ) * d) ^ 2 := sq_pos_of_pos (mul_pos hn' hd)
  have hbound : ((n : ℝ) * d) ^ 2 * (∑ i ∈ s, binomPmf n p i) ≤
      n * p * (1 - p) := by
    calc
      _ = ∑ i ∈ s, ((n : ℝ) * d) ^ 2 * binomPmf n p i := mul_sum _ _ _
      _ ≤ ∑ i ∈ s, ((i : ℝ) - n * p) ^ 2 * binomPmf n p i :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hdev i hi) (pmf_nonneg n i hp hp')
      _ ≤ ∑ i ∈ range (n + 1), ((i : ℝ) - n * p) ^ 2 * binomPmf n p i :=
        sum_le_sum_of_subset_of_nonneg hs fun i _ _ =>
          mul_nonneg (sq_nonneg _) (pmf_nonneg n i hp hp')
      _ = n * p * (1 - p) := pmf_variance n p
  have hquot : (n : ℝ) * p * (1 - p) / ((n : ℝ) * d) ^ 2 =
      (p * (1 - p) / d ^ 2) / n := by
    field_simp
  rw [← hquot]
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using hbound)

private theorem tail_bound (n x : ℕ) {p c : ℝ} (hn : 0 < n) (hp : 0 ≤ p)
    (hp' : p ≤ 1) (hc : p < c) (hx : (n : ℝ) * c ≤ x) :
    upperTail n p x ≤ (p * (1 - p) / (c - p) ^ 2) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold upperTail
  refine concentration n hn hp hp' (sub_pos.mpr hc) (Ico x (n + 1)) ?_ ?_
  · intro i hi
    exact mem_range.mpr (mem_Ico.mp hi).2
  · intro i hi
    have hxi : (x : ℝ) ≤ i := by exact_mod_cast (mem_Ico.mp hi).1
    have hdist : (n : ℝ) * (c - p) ≤ (i : ℝ) - n * p := by linarith
    have hnonneg : 0 ≤ (n : ℝ) * (c - p) :=
      mul_nonneg hn'.le (sub_nonneg.mpr hc.le)
    exact (sq_le_sq₀ hnonneg (hnonneg.trans hdist)).mpr hdist

private theorem lower_bound (n : ℕ) {p c : ℝ} (hn : 0 < n) (hp : 0 ≤ p)
    (hp' : p ≤ 1) (hc : c < p) :
    ∑ i ∈ range (n + 1) with ¬(n : ℝ) * c ≤ ((i : ℕ) : ℝ), binomPmf n p i ≤
      (p * (1 - p) / (p - c) ^ 2) / n := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine concentration n hn hp hp' (sub_pos.mpr hc) _ (filter_subset _ _) ?_
  intro i hi
  have hi' : (i : ℝ) < (n : ℝ) * c := lt_of_not_ge (mem_filter.mp hi).2
  have hdist : (n : ℝ) * (p - c) ≤ n * p - (i : ℝ) := by linarith
  have hnonneg : 0 ≤ (n : ℝ) * (p - c) :=
    mul_nonneg hn'.le (sub_nonneg.mpr hc.le)
  rw [sub_sq_comm (i : ℝ)]
  exact (sq_le_sq₀ hnonneg (hnonneg.trans hdist)).mpr hdist

private theorem power_le_one (n : ℕ) (p₀ γ : ℝ) {p₁ : ℝ} (hp : 0 ≤ p₁)
    (hp' : p₁ ≤ 1) : saturationPower n p₀ p₁ γ ≤ 1 := by
  classical
  calc
    _ ≤ ∑ i ∈ range (n + 1), binomPmf n p₁ i :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => pmf_nonneg n i hp hp'
    _ = 1 := pmf_sum n p₁

private theorem power_lower (n : ℕ) {p₀ p₁ c γ : ℝ} (hn : 0 < n) (hp₀ : 0 ≤ p₀)
    (hp₀' : p₀ ≤ 1) (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hc₀ : p₀ < c) (hc₁ : c < p₁)
    (hlevel : (p₀ * (1 - p₀) / (c - p₀) ^ 2) / n ≤ γ) :
    1 - (p₁ * (1 - p₁) / (p₁ - c) ^ 2) / n ≤ saturationPower n p₀ p₁ γ := by
  classical
  have hsubset : (range (n + 1)).filter (fun i : ℕ => (n : ℝ) * c ≤ (i : ℝ)) ⊆
      (range (n + 1)).filter (fun i => upperTail n p₀ i ≤ γ) := by
    intro i hi
    obtain ⟨hi, hic⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi, (tail_bound n i hn hp₀ hp₀' hc₀ hic).trans hlevel⟩
  have hsum : (∑ i ∈ range (n + 1) with (n : ℝ) * c ≤ ((i : ℕ) : ℝ), binomPmf n p₁ i) +
      (∑ i ∈ range (n + 1) with ¬(n : ℝ) * c ≤ ((i : ℕ) : ℝ), binomPmf n p₁ i) = 1 := by
    rw [sum_filter_add_sum_filter_not, pmf_sum]
  have hhigh : (∑ i ∈ range (n + 1) with (n : ℝ) * c ≤ ((i : ℕ) : ℝ), binomPmf n p₁ i) ≤
      saturationPower n p₀ p₁ γ :=
    sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => pmf_nonneg n i hp₁ hp₁'
  have hlow := lower_bound n hn hp₁ hp₁' hc₁
  linarith

/-- **Power tends to one**: for `0 ≤ p₀ < p₁ ≤ 1` and any level `γ > 0`, the power of the
binomial test tends to `1` as the number of patients grows. -/
theorem tendsto_saturationPower {p₀ p₁ γ : ℝ} (hp₀ : 0 ≤ p₀) (hp₀₁ : p₀ < p₁) (hp₁ : p₁ ≤ 1)
    (hγ : 0 < γ) : Tendsto (fun N => saturationPower N p₀ p₁ γ) atTop (𝓝 1) := by
  let c := (p₀ + p₁) / 2
  have hc₀ : p₀ < c := by dsimp [c]; linarith
  have hc₁ : c < p₁ := by dsimp [c]; linarith
  have hp₀' : p₀ ≤ 1 := hp₀₁.le.trans hp₁
  have hp₁' : 0 ≤ p₁ := hp₀.trans hp₀₁.le
  have ht₀ := tendsto_const_div_atTop_nhds_zero_nat (p₀ * (1 - p₀) / (c - p₀) ^ 2)
  have ht₁ := tendsto_const_div_atTop_nhds_zero_nat (p₁ * (1 - p₁) / (p₁ - c) ^ 2)
  have hlevel : ∀ᶠ n : ℕ in atTop, (p₀ * (1 - p₀) / (c - p₀) ^ 2) / n ≤ γ :=
    (tendsto_order.mp ht₀).2 γ hγ |>.mono fun _ h => h.le
  have hlower : Tendsto
      (fun n : ℕ => 1 - (p₁ * (1 - p₁) / (p₁ - c) ^ 2) / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ht₁
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [hlevel, eventually_gt_atTop 0] with n hlevel hn
    exact power_lower n hn hp₀ hp₀' hp₁' hp₁ hc₀ hc₁ hlevel
  · exact Eventually.of_forall fun n => power_le_one n p₀ γ hp₁' hp₁

/-- **`N_β` exists**: for every target power `β < 1` there is a cohort size beyond which the
power is at least `β` (Lawrence et al. 2014 take `β = 0.9`). -/
theorem eventually_le_saturationPower {p₀ p₁ γ β : ℝ} (hp₀ : 0 ≤ p₀) (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≤ 1) (hγ : 0 < γ) (hβ : β < 1) :
    ∃ N₀, ∀ N ≥ N₀, β ≤ saturationPower N p₀ p₁ γ := by
  have := (tendsto_saturationPower hp₀ hp₀₁ hp₁ hγ).eventually (Ici_mem_nhds hβ)
  simpa using this

/-- The background probability is a probability below one: `0 ≤ p₀ < 1` for
`0 ≤ μ f_g < 1` and `L ≥ 0`. -/
theorem lawrenceP0_mem {μ fg L : ℝ} (h0 : 0 ≤ μ * fg) (h1 : μ * fg < 1) (hL : 0 ≤ L) :
    0 ≤ lawrenceP0 μ fg L ∧ lawrenceP0 μ fg L < 1 := by
  unfold lawrenceP0
  have hb0 : 0 < 1 - μ * fg := by linarith
  refine ⟨?_, ?_⟩
  · have : (1 - μ * fg) ^ (3 * L / 4) ≤ 1 :=
      Real.rpow_le_one hb0.le (by linarith) (by positivity)
    linarith
  · have : 0 < (1 - μ * fg) ^ (3 * L / 4) := Real.rpow_pos_of_pos hb0 _
    linarith

/-- A driver mutated above background raises the per-patient probability:
`p₀ < p₀ + r (1 - m)` for `r > 0` and `m < 1`. -/
theorem lawrenceP0_lt_lawrenceP1 {p₀ r m : ℝ} (hr : 0 < r) (hm : m < 1) :
    p₀ < lawrenceP1 p₀ r m := by
  unfold lawrenceP1
  have : 0 < r * (1 - m) := mul_pos hr (by linarith)
  linarith

end MathlibExt.Biology.CancerGenomics.SaturationPower
