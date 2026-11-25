/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# Block-count drift of a Λ-coalescent

The **block-count drift** `γ_b = ∑_{k=2}^b (k - 1) C(b, k) λ_{b,k}` is the rate at which
the number of blocks is expected to decrease from `b` blocks: a `k`-merger happens at
rate `C(b, k) λ_{b,k}` and lowers the block count by `k - 1`. Equivalently, the
block-counting generator applied to `f(j) = j` gives `-γ_b` at state `b`.

## Main results

* `LambdaComingDown.blockDrift_eq`: Schweinsberg's integral formula for `γ_b`, with the
  Kingman atom at `0` split off.
* `LambdaComingDown.blockDrift_mono`: `γ_b` is nondecreasing.
* `LambdaComingDown.blockDrift_dirac_zero`: for Kingman's coalescent, `γ_b = C(b, 2)`.
* `LambdaComingDown.blockDrift_volume`: for the Bolthausen–Sznitman coalescent,
  `γ_b = b ∑_{k=2}^b 1 / k`.
* `LambdaComingDown.blockCountingGenerator_mulVec_natCast`: the generator applied to
  the identity is `-γ_b`.

## References

* J. Schweinsberg, "A necessary and sufficient condition for the Λ-coalescent to come
  down from infinity", *Electronic Communications in Probability* 5 (2000), 1–11.
-/

@[expose] public section

open MeasureTheory Finset unitInterval Matrix

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaComingDown

open LambdaCoalescent

variable (Λ : Measure I) [IsFiniteMeasure Λ]

/-- The **block-count drift** `γ_b = ∑_{k=2}^b (k - 1) C(b, k) λ_{b,k}` of the Λ-coalescent: a
`k`-merger among `b` blocks lowers the block count by `k - 1` and happens at rate
`C(b, k) λ_{b,k}`, so `γ_b` is the rate at which the number of blocks is expected to decrease
from `b` blocks (Schweinsberg 2000). For `b < 2` the sum is empty and `γ_b = 0`. -/
def blockDrift (b : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 b, ((k : ℝ) - 1) * (b.choose k : ℝ) * mergerRate Λ b k

private theorem sum_range_sub_one_mul (x : ℝ) (b : ℕ) :
    ∑ k ∈ range (b + 1), ((k : ℝ) - 1) * (b.choose k : ℝ) * (x ^ k * (1 - x) ^ (b - k)) =
      b * x - 1 := by
  have h1 := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ b)
  have h2 := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ b)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_natCast, nsmul_eq_mul] at h1 h2
  have e : ∑ k ∈ range (b + 1), ((k : ℝ) - 1) * (b.choose k : ℝ) * (x ^ k * (1 - x) ^ (b - k)) =
      ∑ k ∈ range (b + 1), (k : ℝ) * ((b.choose k : ℝ) * x ^ k * (1 - x) ^ (b - k)) -
        ∑ k ∈ range (b + 1), (b.choose k : ℝ) * x ^ k * (1 - x) ^ (b - k) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [e, h1, h2]

/-- The drift kernel `D_b(x) = ∑_{k=2}^b (k - 1) C(b, k) x ^ (k - 2) (1 - x) ^ (b - k)`, so that
`γ_b = ∫ D_b dΛ`. Powers are natural-number powers, so `0 ^ 0 = 1`. For `b < 2` the sum is
empty and `D_b = 0`. -/
def driftKernel (b : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 b, ((k : ℝ) - 1) * (b.choose k : ℝ) * (x ^ (k - 2) * (1 - x) ^ (b - k))

/-- The kernel in closed form: `x² D_b(x) = b x - 1 + (1 - x) ^ b` for every real `x`. For
`0 ≤ x ≤ 1` the right side is the mean of `k - 1` for `k ~ Binomial(b, x)`, with the `k = 0` term
removed. -/
theorem sq_mul_driftKernel (x : ℝ) (b : ℕ) :
    x ^ 2 * driftKernel b x = b * x - 1 + (1 - x) ^ b := by
  rw [driftKernel]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h := sum_range_sub_one_mul x b
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega),
    sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_add_one_right_eq_Icc] at h
  rw [mul_sum]
  have hs : ∑ k ∈ Icc 2 b, x ^ 2 * (((k : ℝ) - 1) * (b.choose k : ℝ) * (x ^ (k - 2) * (1 - x) ^ (b - k))) =
      ∑ k ∈ Icc 2 b, ((k : ℝ) - 1) * (b.choose k : ℝ) * (x ^ k * (1 - x) ^ (b - k)) := by
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by have := (mem_Icc.1 hk).1; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hs]
  simp at h
  linarith




private lemma integrable_pow_mul_one_sub_pow' (a c : ℕ) :
    Integrable (fun x : I => (x : ℝ) ^ a * (1 - (x : ℝ)) ^ c) Λ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) (ae_of_all _ fun x => ?_)
  have h0 : 0 ≤ (x : ℝ) ^ a * (1 - (x : ℝ)) ^ c :=
    mul_nonneg (pow_nonneg (nonneg x) _) (pow_nonneg (one_sub_nonneg x) _)
  have h1 : (x : ℝ) ^ a * (1 - (x : ℝ)) ^ c ≤ 1 := by
    simpa using mul_le_mul (pow_le_one₀ (nonneg x) (le_one x))
      (pow_le_one₀ (one_sub_nonneg x) (one_sub_le_one x)) (pow_nonneg (one_sub_nonneg x) _)
      zero_le_one
  rwa [Real.norm_eq_abs, abs_of_nonneg h0]

private lemma integrable_driftKernel (b : ℕ) :
    Integrable (fun x : I => driftKernel b (x : ℝ)) Λ :=
  integrable_finsetSum _ fun _ _ => (integrable_pow_mul_one_sub_pow' Λ _ _).const_mul _

/-- `γ_b = ∫ D_b dΛ`. -/
theorem blockDrift_eq_integral (b : ℕ) :
    blockDrift Λ b = ∫ x, driftKernel b (x : ℝ) ∂Λ := by
  unfold driftKernel
  rw [blockDrift, integral_finsetSum _ fun k _ =>
    (integrable_pow_mul_one_sub_pow' Λ _ _).const_mul _]
  refine sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, mergerRate_of_le Λ (mem_Icc.1 hk).1 (mem_Icc.1 hk).2]

private lemma driftKernel_zero (b : ℕ) : driftKernel b 0 = b.choose 2 := by
  rcases lt_or_ge b 2 with hb | hb
  · simp [driftKernel, Icc_eq_empty (show ¬ 2 ≤ b by omega), Nat.choose_eq_zero_of_lt hb]
  · simp only [driftKernel, sub_zero, one_pow, mul_one]
    rw [sum_eq_single_of_mem 2 (mem_Icc.2 ⟨le_rfl, hb⟩) fun k hk hk2 => by
      simp [show k - 2 ≠ 0 by have := (mem_Icc.1 hk).1; omega]]
    norm_num

/-- **Schweinsberg's formula**: `γ_b = C(b, 2) Λ{0} + ∫_{(0,1]} (b x - 1 + (1 - x) ^ b) x⁻² Λ(dx)`;
the Kingman atom at `0` is split off, so no division by zero occurs. -/
theorem blockDrift_eq (b : ℕ) :
    blockDrift Λ b = (b.choose 2 : ℝ) * Λ.real {0} +
      ∫ x in ({0}ᶜ : Set I), (b * (x : ℝ) - 1 + (1 - (x : ℝ)) ^ b) / (x : ℝ) ^ 2 ∂Λ := by
  rw [blockDrift_eq_integral,
    ← integral_add_compl (measurableSet_singleton 0) (integrable_driftKernel Λ b),
    integral_singleton, Set.Icc.coe_zero, driftKernel_zero, smul_eq_mul, mul_comm]
  congr 1
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have hx0 : (x : ℝ) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [eq_div_iff (pow_ne_zero 2 hx0), mul_comm]
  exact sq_mul_driftKernel (x : ℝ) b

private lemma driftKernel_le_succ (b : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    driftKernel b x ≤ driftKernel (b + 1) x := by
  rcases hx0.eq_or_lt with rfl | hx
  · rw [driftKernel_zero, driftKernel_zero]
    exact_mod_cast Nat.choose_le_choose 2 (Nat.le_succ b)
  have hsq : 0 < x ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hsq
  rw [sq_mul_driftKernel, sq_mul_driftKernel, pow_succ]
  have hp : (1 - x) ^ b ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  push_cast
  nlinarith

/-- `γ_b` is nondecreasing in `b`. -/
theorem blockDrift_mono : Monotone (blockDrift Λ) :=
  monotone_nat_of_le_succ fun b => by
    rw [blockDrift_eq_integral, blockDrift_eq_integral]
    exact integral_mono (integrable_driftKernel Λ b) (integrable_driftKernel Λ (b + 1))
      fun x => driftKernel_le_succ b (unitInterval.nonneg x) (unitInterval.le_one x)

/-- `γ_b ≥ 0`. -/
theorem blockDrift_nonneg (b : ℕ) : 0 ≤ blockDrift Λ b := by
  refine sum_nonneg fun k hk => mul_nonneg (mul_nonneg ?_ (Nat.cast_nonneg _)) (mergerRate_nonneg Λ b k)
  have : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
  linarith

/-- **Kingman** (`Λ = δ₀`): `γ_b = C(b, 2)`. -/
theorem blockDrift_dirac_zero (b : ℕ) :
    blockDrift (Measure.dirac 0) b = b.choose 2 := by
  rw [blockDrift]
  simp_rw [mergerRate_dirac_zero]
  rcases lt_or_ge b 2 with hb | hb
  · rw [Icc_eq_empty (by omega), sum_empty, Nat.choose_eq_zero_of_lt hb, Nat.cast_zero]
  · rw [sum_eq_single_of_mem 2 (mem_Icc.2 ⟨le_rfl, hb⟩) fun k _ hk => by simp [hk]]
    simp [hb]
    norm_num

/-- **Bolthausen–Sznitman** (`Λ` uniform on `[0, 1]`): `γ_b = b ∑_{k=2}^b 1 / k`. For `b < 2`
the sum is empty and both sides are `0`. -/
theorem blockDrift_volume (b : ℕ) :
    blockDrift volume b = b * ∑ k ∈ Icc 2 b, (1 / (k : ℝ)) := by
  rw [blockDrift, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨hk2, hkb⟩ := mem_Icc.1 hk
  rw [mergerRate_volume hk2 hkb]
  have hc : ((b.choose k : ℕ) : ℝ) * (k.factorial : ℝ) * ((b - k).factorial : ℝ) =
      (b.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkb
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ] at hc
  simp only [Nat.add_sub_cancel] at hc ⊢
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (m.factorial : ℝ) ≠ 0 := by positivity
  push_cast at hc ⊢
  field_simp
  linear_combination hc

private lemma neg_totalMergerRate_mul_add_sum (b : ℕ) :
    -totalMergerRate Λ b * b +
        ∑ j ∈ range b, (b.choose (b + 1 - j) : ℝ) * mergerRate Λ b (b + 1 - j) * j =
      -blockDrift Λ b := by
  have hsum : ∑ j ∈ range b, (b.choose (b + 1 - j) : ℝ) * mergerRate Λ b (b + 1 - j) * j =
      ∑ k ∈ Icc 2 b, (b.choose k : ℝ) * mergerRate Λ b k * ((b : ℝ) + 1 - k) := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hb]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    refine sum_nbij' (fun j => b + 1 - j) (fun k => b + 1 - k) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ico, mem_Icc] at hj ⊢; omega
    · intro k hk; simp only [mem_Ico, mem_Icc] at hk ⊢; omega
    · intro j hj; simp only [mem_Ico] at hj; omega
    · intro k hk; simp only [mem_Icc] at hk; omega
    · intro j hj
      simp only [mem_Ico] at hj
      rw [Nat.cast_sub (by omega : j ≤ b + 1)]
      push_cast
      ring
  rw [hsum, blockDrift, totalMergerRate, neg_mul, sum_mul, ← sum_neg_distrib, ← sum_add_distrib,
    ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- **The generator applied to the identity**: for the block-counting generator on `0, …, n`, the
function `f(j) = j` satisfies `(Q f)(b) = -γ_b` at every state `b ≤ n`; i.e. `γ_b` is the expected
rate of descent of the block count from `b` blocks. -/
theorem blockCountingGenerator_mulVec_natCast (n : ℕ) (i : Fin (n + 1)) :
    (blockCountingGenerator Λ n *ᵥ fun j => ((j : ℕ) : ℝ)) i = -blockDrift Λ i := by
  set F : ℕ → ℝ := fun j => (if (i : ℕ) = j then -totalMergerRate Λ i * i else 0) +
    (if j < (i : ℕ) then ((i : ℕ).choose (i + 1 - j) : ℝ) * mergerRate Λ i (i + 1 - j) * j
      else 0) with hF
  have hterm : ∀ j : Fin (n + 1), blockCountingGenerator Λ n i j * ((j : ℕ) : ℝ) = F j := by
    intro j
    simp only [blockCountingGenerator, hF, Fin.ext_iff]
    by_cases h : (i : ℕ) = j
    · simp [h]
    · by_cases h' : (j : ℕ) < i
      · simp [h, h']
      · simp [h, h']
  simp only [mulVec, dotProduct]
  rw [sum_congr rfl fun j _ => hterm j, Fin.sum_univ_eq_sum_range F (n + 1), hF, sum_add_distrib,
    sum_ite_eq (range (n + 1)) (i : ℕ)]
  simp only [mem_range.2 i.isLt, ↓reduceIte]
  rw [← sum_filter]
  have hfil : (range (n + 1)).filter (· < (i : ℕ)) = range i := by
    ext j; simp only [mem_filter, mem_range]; omega
  rw [hfil]
  exact neg_totalMergerRate_mul_add_sum Λ i

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaComingDown
