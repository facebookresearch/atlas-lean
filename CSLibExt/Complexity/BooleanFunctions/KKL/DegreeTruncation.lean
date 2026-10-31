/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CappedExponentGap

/-!
# Degree truncation of the capped estimate under p-biased measures

The capped per-coordinate estimate `∑_S 4 |S| (1-u)^{|S|-1} f̂(S)² ≤ δ^{u/(2-u)} ∑ₑ Infₑ` under
the Bernoulli(`p`) measure is split by Fourier degree: the part with `|S| > k` is at most
`4p(1-p)(1-u)^k ∑ₑ Infₑ` (`dtr_high_part_le`), so the estimate follows from a bound on the
low-degree part (`dtr_trunc_split`). The predicate `dtr_lowDegreeResidue q` is that low-degree
bound for `p ∈ (1/2, q)` in the regime not covered by `TwoPointHCqGt2`; it implies the earlier
reduction predicates (`dtr_lowDegree_of_residue`, `dtr_smallDelta_of_residue`,
`dtr_martingaleHC_of_residue`) and is not proved in this library for any `q > 1/2`.

## Main definitions

* `StatMech.Probability.dtr_qstar`: the exponent `1 + (1-u)/(4p(1-p))` paired with `u`.
* `StatMech.Probability.dtr_lowDegreeResidue`: the low-degree bound on `(1/2, q)`.

## Main results

* `StatMech.Probability.dtr_full_weight_eq`: `4 ∑_S |S| f̂(S)² = 4p(1-p) ∑ₑ Infₑ`.
* `StatMech.Probability.dtr_high_part_le`: the high-degree bound.
* `StatMech.Probability.dtr_trunc_split`: the capped estimate from a low-degree bound.
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real Set

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Fourier total weight under `μ_p`: `4 ∑_S |S| f̂(S)² = 4p(1-p) ∑ₑ Infₑ`. -/
theorem dtr_full_weight_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    4 * ∑ S : Finset ι, (S.card : ℝ)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      = 4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < (ptn_sigma p) ^ 2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1]
  rw [hσ2]
  have hppos : 0 < p * (1 - p) := by nlinarith
  set W := ∑ S : Finset ι, (S.card : ℝ)
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hW
  rw [show (4 : ℝ) * p * (1 - p) * (1 / (p * (1 - p)) * W)
      = (4 * (p * (1 - p)) * (1 / (p * (1 - p)))) * W by ring]
  rw [mul_one_div, mul_div_assoc, div_self (ne_of_gt hppos), mul_one]

/-- The Fourier part of degree greater than `k` contributes at most `4p(1-p)(1-u)^k ∑ₑ Infₑ` to the
  damped total weight. -/
theorem dtr_high_part_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have h1u1 : (1 : ℝ) - u ≤ 1 := by linarith
  have hterm : ∀ S ∈ univ.filter (fun S : Finset ι => k < S.card),
      4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S
        ≤ (1 - u) ^ k * (4 * (S.card : ℝ) * c S) := by
    intro S hS
    rw [Finset.mem_filter] at hS
    have hkS : k ≤ S.card - 1 := by omega
    have hpow : (1 - u) ^ (S.card - 1) ≤ (1 - u) ^ k := pow_le_pow_of_le_one h1u0 h1u1 hkS
    have hcoef : (0 : ℝ) ≤ 4 * (S.card : ℝ) * c S := by positivity
    nlinarith [hpow, hcoef, Real.rpow_natCast (1 - u) k]
  rw [Finset.mul_sum]
  calc (∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
          4 * ((S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S))
      = ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
          4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S := by
        apply Finset.sum_congr rfl; intro S _; ring
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), (1 - u) ^ k *
        (4 * (S.card : ℝ) * c S) :=
        Finset.sum_le_sum hterm
    _ = (1 - u) ^ k * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), 4 *
        (S.card : ℝ) * c S := by
        rw [Finset.mul_sum]
    _ ≤ (1 - u) ^ k * ∑ S : Finset ι, 4 * (S.card : ℝ) * c S := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _; positivity
    _ = (1 - u) ^ k * (4 * ∑ S : Finset ι, (S.card : ℝ) * c S) := by
        congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring
    _ = (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
        rw [dtr_full_weight_eq hp0 hp1 φ]

/-- The capped estimate follows from a bound on its part of degree at most `k`. -/
theorem dtr_trunc_split {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        + (1 - u) ^ k * (4 * p * (1 - p)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  set g := fun S : Finset ι => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S with hg
  have hgnn : ∀ S, 0 ≤ g S := by
    intro S; rw [hg]; have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
    positivity
  have hsplit : (∑ S : Finset ι, g S)
      = (∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k), g S)
        + ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), g S := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun S : Finset ι => S.card ≤ k) g]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [hsplit]
  apply add_le_add
  · apply le_of_eq
    have hRHS : (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
        = ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k), g S := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; rw [hg]; ring
    rw [hRHS]
    symm
    apply Finset.sum_subset
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      exact ⟨hS.1, hS.2.2⟩
    · intro S hS hSnot
      rw [Finset.mem_filter] at hS hSnot
      have hc0 : S.card = 0 := by
        by_contra h
        exact hSnot ⟨Finset.mem_univ S, Nat.one_le_iff_ne_zero.mpr h, hS.2⟩
      change 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S = 0
      rw [hc0]; simp
  · have hconv : (∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), g S)
        = 4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; rw [hg]; ring
    rw [hconv]
    exact dtr_high_part_le hp0 hp1 φ hu0 hu1 k

/-- The exponent `q*(p, u) = 1 + (1-u)/(4p(1-p))` paired with the damping `1 - u`. -/
noncomputable def dtr_qstar (p u : ℝ) : ℝ := 1 + (1 - u) / (4 * p * (1 - p))

/-- The low-degree form of the capped estimate for every `p ∈ (1/2, q)` with `p < 1`, small maximal
  influence `δ < e^{-1}`, and parameters `u` outside the range handled by `TwoPointHCqGt2`. Not
  proved in this library for any `q > 1/2`. -/
def dtr_lowDegreeResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-1) →
      ∀ u : ℝ, 0 < u → u < 1 →
        (u < 1 - 4 * p * (1 - p) ∨
          (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
              ^ (u / (2 - u) - (2 / dtr_qstar p u - 1))
            < 4 * (ptn_sigma p) ^ 2) →
        ∃ k : ℕ,
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - 4 * p * (1 - p) * (1 - u) ^ k)
              * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)

/-- `dtr_lowDegreeResidue q` implies `hcq_lowRangeResidue q`. -/
theorem dtr_lowDegree_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    hcq_lowRangeResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1 hlow
  have hp0 : 0 < p := by have := hp.1; linarith
  have hlow' : u < 1 - 4 * p * (1 - p) ∨
      (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u) - (2 / dtr_qstar p u - 1))
        < 4 * (ptn_sigma p) ^ 2 := by
    rcases hlow with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [dtr_qstar]; exact h)
  obtain ⟨k, hk⟩ := H p hp hp1 φ hδ u hu0 hu1 hlow'
  have hsplit := dtr_trunc_split hp0 hp1 φ hu0 hu1 k
  set T := totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδdef
  calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          + (1 - u) ^ k * (4 * p * (1 - p) * T) := hsplit
    _ ≤ (δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k) * T
          + (1 - u) ^ k * (4 * p * (1 - p) * T) := by linarith [hk]
    _ = δ ^ (u / (2 - u)) * T := by ring

/-- `dtr_lowDegreeResidue q` implies `cvg_smallDeltaResidue q`. -/
theorem dtr_smallDelta_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    cvg_smallDeltaResidue q :=
  hcq_smallDelta_of_lowRange (dtr_lowDegree_of_residue H)

/-- `dtr_lowDegreeResidue q` implies `mxd_martingaleHC_statement q`. -/
theorem dtr_martingaleHC_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    mxd_martingaleHC_statement q :=
  cvg_martingaleHC_of_smallDelta (dtr_smallDelta_of_residue H)

/-- For `δ > 0` the truncation budget `δ^{u/(2-u)} - 4p(1-p)(1-u)^k` is nonnegative for some `k`. -/
theorem dtr_budget_pos {p δ u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (_hu1 : u < 1)
    (hδ0 : 0 < δ ^ (u / (2 - u))) :
    ∃ k : ℕ, 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k := by
  have hs0 : 0 < 4 * p * (1 - p) := by nlinarith
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := δ ^ (u / (2 - u)) / (4 * p * (1 - p)))
    (by positivity) h1u
  refine ⟨k, ?_⟩
  rw [lt_div_iff₀ hs0] at hk
  nlinarith [hk]

/-- For `δ^{u/(2-u)} > 0` some truncation level `k` makes the right side of the low-degree bound
  in `dtr_lowDegreeResidue` nonnegative. -/
theorem dtr_residue_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ k : ℕ, (0 : ℝ)
      ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          - 4 * p * (1 - p) * (1 - u) ^ k)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  obtain ⟨k, hk⟩ := dtr_budget_pos hp0 hp1 hu0 hu1 hδ0
  refine ⟨k, ?_⟩
  apply mul_nonneg hk
  exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _

end StatMech.Probability
