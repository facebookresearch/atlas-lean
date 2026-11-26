/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DowkerHalfSum
import MathlibExt.NumberTheory.WatsonAlternatingBounds

/-!
# Vanishing limits of Watson's cosine sum at one sixth and five sixths

This module proves `MetaMathlibExt.watson_cos_sum_sixth_limits`: as `m → ∞` through the
natural numbers, `C_{6m}(m) → 0` and `C_{6m}(5m) → 0`, where `C_n(ν)` is
`MetaMathlibExt.watsonCosSum`.

The proof writes `C_{6m}(m)` as `(C_{6m} - 3 * C_{2m}) / 2` in terms of
`MetaMathlibExt.watsonAlternatingCosecantSum` by splitting the defining sum according to
`l mod 3`, then applies `MetaMathlibExt.watson_alternating_simple_bounds`: the main terms
cancel and the remaining error terms tend to zero. The case `ν = 5 * m` agrees termwise
with the case `ν = m`.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 4.
-/

namespace MetaMathlibExt

open Filter
open scoped BigOperators Topology

namespace watson_cos_sum_sixth_limits

/-- Split a sum over `range (3 * N)` into blocks of three consecutive terms. -/
private lemma sum_range_three (f : ℕ → ℝ) (N : ℕ) :
    ∑ l ∈ Finset.range (3 * N), f l
      = ∑ k ∈ Finset.range N, (f (3 * k) + f (3 * k + 1) + f (3 * k + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : 3 * (N + 1) = (3 * N + 2) + 1 := by ring
    have e2 : 3 * N + 2 = (3 * N + 1) + 1 := by ring
    have s1 : ∑ l ∈ Finset.range (3 * N + 2), f l
        = (∑ l ∈ Finset.range (3 * N + 1), f l) + f (3 * N + 1) := by
      rw [e2]
      exact Finset.sum_range_succ f _
    have s0 : ∑ l ∈ Finset.range (3 * N + 1), f l
        = (∑ l ∈ Finset.range (3 * N), f l) + f (3 * N) :=
      Finset.sum_range_succ f _
    rw [e1, Finset.sum_range_succ, s1, s0, ih, Finset.sum_range_succ]
    ring

/-- A sum over `range n` equals the sum over `Icc 1 (n - 1)` when `f 0 = 0`. -/
private lemma sum_range_eq_Icc (f : ℕ → ℝ) (n : ℕ) (hf : f 0 = 0) :
    ∑ l ∈ Finset.range n, f l = ∑ l ∈ Finset.Icc 1 (n - 1), f l := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ' _ n, hf, add_zero, Nat.add_sub_cancel]
    have hIco : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [← hIco, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    rw [add_comm k 1]

/-- Summand of `MetaMathlibExt.watsonCosSum (6 * m) m` at `l`. -/
private noncomputable def cosSummand (m l : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * (m : ℝ) * (l : ℝ) / ((6 * m : ℕ) : ℝ)) *
    (1 / Real.sin (Real.pi * (l : ℝ) / ((6 * m : ℕ) : ℝ)))

/-- Summand of `MetaMathlibExt.watsonAlternatingCosecantSum n` at `l`. -/
private noncomputable def altSummand (n l : ℕ) : ℝ :=
  (-1 : ℝ) ^ (l + 1) * (1 / Real.sin (Real.pi * (l : ℝ) / ((n : ℕ) : ℝ)))

private lemma cosSummand_zero (m : ℕ) : cosSummand m 0 = 0 := by
  simp [cosSummand]

private lemma altSummand_zero (n : ℕ) : altSummand n 0 = 0 := by
  simp [altSummand]

/-- The cosine sum at `ν / n = 1 / 6` as a sum over `range (6 * m)`. -/
private lemma cosSum_range (m : ℕ) :
    watsonCosSum (6 * m) m = ∑ l ∈ Finset.range (6 * m), cosSummand m l :=
  (sum_range_eq_Icc (cosSummand m) (6 * m) (cosSummand_zero m)).symm

/-- The alternating cosecant sum as a sum over `range n`. -/
private lemma alt_range (n : ℕ) :
    watsonAlternatingCosecantSum n = ∑ l ∈ Finset.range n, altSummand n l :=
  (sum_range_eq_Icc (altSummand n) n (altSummand_zero n)).symm

/-- The `l ≡ 0` terms of the cosine block negate the alternating terms. -/
private lemma block_cos0 (m k : ℕ) (hm : m ≠ 0) :
    cosSummand m (3 * k) = -altSummand (2 * m) k := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hm2 : (2 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hA : (2 * Real.pi * (m : ℝ) * ((3 * k : ℕ) : ℝ) / ((6 * m : ℕ) : ℝ))
      = (k : ℝ) * Real.pi := by
    push_cast
    field_simp
    ring
  have hS : (Real.pi * ((3 * k : ℕ) : ℝ) / ((6 * m : ℕ) : ℝ))
      = Real.pi * (k : ℝ) / ((2 * m : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  unfold cosSummand altSummand
  rw [hA, Real.cos_nat_mul_pi, hS, pow_succ]
  ring

/-- The `l ≡ 0` terms of the alternating block reindex to the smaller sum. -/
private lemma block_alt0 (m k : ℕ) (hm : m ≠ 0) :
    altSummand (6 * m) (3 * k) = altSummand (2 * m) k := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hm2 : (2 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hS : (Real.pi * ((3 * k : ℕ) : ℝ) / ((6 * m : ℕ) : ℝ))
      = Real.pi * (k : ℝ) / ((2 * m : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  have hp0 : (-1 : ℝ) ^ (3 * k + 1) = (-1) ^ (k + 1) := by
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  unfold altSummand
  rw [hS, hp0]

/-- The `l ≡ 1` terms of the cosine block halve the alternating terms. -/
private lemma block_cos1 (m k : ℕ) (hm : m ≠ 0) :
    cosSummand m (3 * k + 1) = altSummand (6 * m) (3 * k + 1) / 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hA : (2 * Real.pi * (m : ℝ) * ((3 * k + 1 : ℕ) : ℝ) / ((6 * m : ℕ) : ℝ))
      = Real.pi / 3 + (k : ℝ) * Real.pi := by
    push_cast
    field_simp
    ring
  have hp1 : (-1 : ℝ) ^ ((3 * k + 1) + 1) = (-1) ^ k := by
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  unfold cosSummand altSummand
  rw [hA, Real.cos_add_nat_mul_pi, Real.cos_pi_div_three, hp1]
  ring

/-- The `l ≡ 2` terms of the cosine block halve the alternating terms. -/
private lemma block_cos2 (m k : ℕ) (hm : m ≠ 0) :
    cosSummand m (3 * k + 2) = altSummand (6 * m) (3 * k + 2) / 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hA : (2 * Real.pi * (m : ℝ) * ((3 * k + 2 : ℕ) : ℝ) / ((6 * m : ℕ) : ℝ))
      = 2 * Real.pi / 3 + (k : ℝ) * Real.pi := by
    push_cast
    field_simp
    ring
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h23 : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hp2 : (-1 : ℝ) ^ ((3 * k + 2) + 1) = (-1) ^ (k + 1) := by
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  unfold cosSummand altSummand
  rw [hA, Real.cos_add_nat_mul_pi, hcos, hp2, pow_succ]
  ring

/-- One residue block of the cosine sum in terms of the alternating sums. -/
private lemma block (m k : ℕ) (hm : m ≠ 0) :
    cosSummand m (3 * k) + cosSummand m (3 * k + 1) + cosSummand m (3 * k + 2)
      = (altSummand (6 * m) (3 * k) + altSummand (6 * m) (3 * k + 1)
          + altSummand (6 * m) (3 * k + 2) - 3 * altSummand (2 * m) k) / 2 := by
  have hc0 := block_cos0 m k hm
  have hg0 := block_alt0 m k hm
  have hc1 := block_cos1 m k hm
  have hc2 := block_cos2 m k hm
  linarith

/-- The cosine sum at `ν / n = 1 / 6` via alternating cosecant sums. -/
private lemma cos_sum_eq (m : ℕ) :
    watsonCosSum (6 * m) m
      = (watsonAlternatingCosecantSum (6 * m)
          - 3 * watsonAlternatingCosecantSum (2 * m)) / 2 := by
  by_cases hm : m = 0
  · subst hm
    simp [watsonCosSum, watsonAlternatingCosecantSum]
  · have h63 : 6 * m = 3 * (2 * m) := by ring
    have hC := cosSum_range m
    have hA6 := alt_range (6 * m)
    have hA2 := alt_range (2 * m)
    have hsplitC : ∑ l ∈ Finset.range (6 * m), cosSummand m l
        = ∑ k ∈ Finset.range (2 * m),
            (cosSummand m (3 * k) + cosSummand m (3 * k + 1)
              + cosSummand m (3 * k + 2)) := by
      rw [h63]
      exact sum_range_three _ _
    have hsplitA : ∑ l ∈ Finset.range (6 * m), altSummand (6 * m) l
        = ∑ k ∈ Finset.range (2 * m),
            (altSummand (6 * m) (3 * k) + altSummand (6 * m) (3 * k + 1)
              + altSummand (6 * m) (3 * k + 2)) := by
      rw [h63]
      exact sum_range_three _ _
    rw [hC, hsplitC, hA6, hsplitA, hA2, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    exact block m k hm

/-- The cosine sums at `ν / n = 5 / 6` and `ν / n = 1 / 6` agree. -/
private lemma five_eq (m : ℕ) :
    watsonCosSum (6 * m) (5 * m) = watsonCosSum (6 * m) m := by
  unfold watsonCosSum
  apply Finset.sum_congr rfl
  intro l _
  by_cases hm : m = 0
  · subst hm
    simp
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
    have h5 : (2 * Real.pi * ((5 * m : ℕ) : ℝ) * (l : ℝ) / ((6 * m : ℕ) : ℝ))
        = -(Real.pi * (l : ℝ) / 3) + (l : ℝ) * (2 * Real.pi) := by
      push_cast
      field_simp
      ring
    have h1 : (2 * Real.pi * (m : ℝ) * (l : ℝ) / ((6 * m : ℕ) : ℝ))
        = Real.pi * (l : ℝ) / 3 := by
      push_cast
      field_simp
      ring
    rw [h5, Real.cos_add_nat_mul_two_pi, Real.cos_neg, h1]

/-- Lower estimate for the alternating-sum combination. -/
private lemma bound_lo (m : ℕ) (hm : 2 ≤ m) :
    (-(1 / (m : ℝ))) ≤ (2 * (6 * (m : ℝ)) * Real.log 2 / Real.pi
      + 0.252 / (6 * (m : ℝ))
      - 3 * (2 * (2 * (m : ℝ)) * Real.log 2 / Real.pi + 0.262 / (2 * (m : ℝ)))) / 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hm2 : (2 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h6mpos : (0 : ℝ) < 6 * (m : ℝ) := by positivity
  have hE : (2 * (6 * (m : ℝ)) * Real.log 2 / Real.pi + 0.252 / (6 * (m : ℝ))
      - 3 * (2 * (2 * (m : ℝ)) * Real.log 2 / Real.pi + 0.262 / (2 * (m : ℝ)))) / 2
      = -(1.053 / (6 * (m : ℝ))) := by
    field_simp
    ring
  have hcancel : (1 : ℝ) / (m : ℝ) * (6 * (m : ℝ)) = 6 := by field_simp
  rw [hE, neg_le_neg_iff, div_le_iff₀ h6mpos, hcancel]
  norm_num

/-- Upper estimate for the alternating-sum combination. -/
private lemma bound_hi (m : ℕ) (hm : 2 ≤ m) :
    (2 * (6 * (m : ℝ)) * Real.log 2 / Real.pi + 0.262 / (6 * (m : ℝ))
      - 3 * (2 * (2 * (m : ℝ)) * Real.log 2 / Real.pi + 0.252 / (2 * (m : ℝ)))) / 2
      ≤ 1 / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm6 : (6 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hm2 : (2 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hE : (2 * (6 * (m : ℝ)) * Real.log 2 / Real.pi + 0.262 / (6 * (m : ℝ))
      - 3 * (2 * (2 * (m : ℝ)) * Real.log 2 / Real.pi + 0.252 / (2 * (m : ℝ)))) / 2
      = -1.003 / (6 * (m : ℝ)) := by
    field_simp
    ring
  rw [hE]
  have hneg : (-1.003 : ℝ) / (6 * (m : ℝ)) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hpos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  linarith

/-- The cosine sum at `ν / n = 1 / 6` is eventually bounded by `1 / m`. -/
private lemma norm_le (m : ℕ) (hm : 2 ≤ m) :
    ‖watsonCosSum (6 * m) m‖ ≤ 1 / (m : ℝ) := by
  have heven6 : Even (6 * m) := ⟨3 * m, by ring⟩
  have heven2 : Even (2 * m) := ⟨m, by ring⟩
  have h4_6 : 4 ≤ 6 * m := by omega
  have h4_2 : 4 ≤ 2 * m := by omega
  obtain ⟨lo6, hi6⟩ := watson_alternating_simple_bounds (6 * m) heven6 h4_6
  obtain ⟨lo2, hi2⟩ := watson_alternating_simple_bounds (2 * m) heven2 h4_2
  push_cast at lo6 hi6 lo2 hi2
  rw [cos_sum_eq m, Real.norm_eq_abs, abs_le]
  constructor
  · linarith [bound_lo m hm, lo6, hi2]
  · linarith [bound_hi m hm, hi6, lo2]

end watson_cos_sum_sixth_limits

open watson_cos_sum_sixth_limits

/--
**Vanishing limits of Watson's cosine sum at one sixth and five sixths.** For natural numbers
$n$ and $\nu$ let $C_n(\nu) = \sum_{l=1}^{n-1} \cos(2 \pi \nu l / n) / \sin(\pi l / n)$. As
$m \to \infty$ through the natural numbers, $C_{6m}(m) \to 0$ and $C_{6m}(5m) \to 0$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 4.
-/
public theorem watson_cos_sum_sixth_limits :
    Tendsto (fun m : ℕ => watsonCosSum (6 * m) m) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => watsonCosSum (6 * m) (5 * m)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => watsonCosSum (6 * m) m) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun m : ℕ => ‖watsonCosSum (6 * m) m‖) atTop (𝓝 0) := by
      have hnn : ∀ᶠ m : ℕ in atTop, 0 ≤ ‖watsonCosSum (6 * m) m‖ :=
        Eventually.of_forall fun m => norm_nonneg _
      have hle : ∀ᶠ m : ℕ in atTop, ‖watsonCosSum (6 * m) m‖ ≤ 1 / (m : ℝ) := by
        filter_upwards [eventually_ge_atTop 2] with m hm
        exact norm_le m hm
      have hg : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 1
      exact squeeze_zero' hnn hle hg
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  refine ⟨hlim, ?_⟩
  have heq : (fun m : ℕ => watsonCosSum (6 * m) (5 * m))
      = (fun m : ℕ => watsonCosSum (6 * m) m) :=
    funext five_eq
  rw [heq]
  exact hlim

end MetaMathlibExt
