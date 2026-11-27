/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import Domains.Biology.StatisticalGenetics.SpearmanKarber

/-!
# Unbiasedness and exact variance of the Spearman–Kärber estimator

In a quantal bioassay, doses on an equally spaced (log-)scale `xᵢ = x₀ + i d`
are given to `n` subjects each; at dose `i` the true response probability is `Pᵢ`
and the observed proportion is `rᵢ / n` for a binomial count `rᵢ`. Using the Spearman–Kärber
value `spearmanKarber` of `Domains.Biology.StatisticalGenetics.SpearmanKarber`, this file
defines the binomial point mass `binomProb`,
the expectation `expect` over independent binomial counts at the different doses,
and the estimator `estimator` computed from the counts. It proves `expect_variance`:
the estimator is unbiased for the mean of the interpolated tolerance distribution,
with exact variance `d² ∑ᵢ Pᵢ (1 - Pᵢ) / n` for independent counts.

The proofs of `choose_add_two_mul` and `binomProb_fact2_range` are adapted from
`MathlibExt/Probability/Distributions/BinomialMoments.lean`.

## References

* J. O. Irwin and E. A. Cheeseman, "On an approximate method of determining the median
effective dose and its error, in the case of a quantal response", J. Hyg. 39 (1939) 574–580,
doi:10.1017/S0022172400012213, p. 574; C. Spearman, "The method of 'right and wrong cases'
('constant stimuli') without Gauss's formulae", Brit. J. Psychol. 2 (1908) 227–242; G. Kärber,
Arch. Exp. Path. Pharmak. 162 (1931) 480–483.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted

open Finset

/-- The binomial probability `C(n, r) Pʳ (1 - P)ⁿ⁻ʳ` of `r` responders among `n` subjects. -/
noncomputable def binomProb (n : ℕ) (P : ℝ) (r : Fin (n + 1)) : ℝ :=
  (n.choose r : ℝ) * P ^ (r : ℕ) * (1 - P) ^ (n - r)

/-- The expectation of a function of the response counts `r : Fin (k + 1) → Fin (n + 1)` when the
counts at the different doses are independent binomial(`n`, `Pᵢ`). -/
noncomputable def expect {k : ℕ} (n : ℕ) (P : Fin (k + 1) → ℝ)
    (f : (Fin (k + 1) → Fin (n + 1)) → ℝ) : ℝ :=
  ∑ r : Fin (k + 1) → Fin (n + 1), (∏ i, binomProb n (P i) (r i)) * f r

/-- The estimator computed from the counts: the Spearman–Kärber value of the proportions
`rᵢ / n`. -/
noncomputable def estimator (x₀ d : ℝ) {k : ℕ} (n : ℕ) (r : Fin (k + 1) → Fin (n + 1)) : ℝ :=
  spearmanKarber x₀ d (fun i => ((r i : ℕ) : ℝ) / n)

private theorem binomProb_sum_range (n : ℕ) (P : ℝ) :
    ∑ m ∈ range (n + 1), (n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m) = 1 := by
  have h := add_pow P (1 - P) n
  rw [show P + (1 - P) = 1 by ring, one_pow] at h
  apply Eq.trans _ h.symm
  apply sum_congr rfl
  intro m _
  ring

private theorem binomProb_sum (n : ℕ) (P : ℝ) :
    ∑ s : Fin (n + 1), binomProb n P s = 1 := by
  have h := Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m)) (n + 1)
  rw [binomProb_sum_range] at h
  simpa [binomProb] using h

private theorem binomProb_first_range (n : ℕ) (P : ℝ) :
    ∑ m ∈ range (n + 1), (m : ℝ) * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))
      = (n : ℝ) * P := by
  match n with
  | 0 => simp
  | m + 1 =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hterm : ∀ j ∈ range (m + 1),
        ((j + 1 : ℕ) : ℝ) * ((((m + 1).choose (j + 1) : ℕ) : ℝ) * P ^ (j + 1) *
          (1 - P) ^ (m + 1 - (j + 1)))
        = ((m + 1 : ℕ) : ℝ) * P *
          (((m.choose j : ℕ) : ℝ) * P ^ j * (1 - P) ^ (m - j)) := by
      intro j _
      have hnat := Nat.add_one_mul_choose_eq m j
      have hc : ((((m + 1).choose (j + 1) : ℕ)) : ℝ) * ((j + 1 : ℕ) : ℝ)
          = ((m + 1 : ℕ) : ℝ) * ((m.choose j : ℕ) : ℝ) := by
        exact_mod_cast hnat.symm
      rw [show m + 1 - (j + 1) = m - j by omega]
      linear_combination P ^ j * (1 - P) ^ (m - j) * P * hc
    rw [sum_congr rfl hterm, ← mul_sum, binomProb_sum_range, mul_one]

private theorem binomProb_first (n : ℕ) (P : ℝ) :
    ∑ s : Fin (n + 1), (s : ℝ) * binomProb n P s = (n : ℝ) * P := by
  have h := Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (m : ℝ) * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))) (n + 1)
  rw [binomProb_first_range] at h
  simpa [binomProb, mul_assoc] using h

private theorem choose_add_two_mul (m j : ℕ) :
    (m + 2).choose (j + 2) * ((j + 2) * (j + 1)) = (m + 2) * (m + 1) * m.choose j := by
  have h1 := Nat.add_one_mul_choose_eq (m + 1) (j + 1)
  have h2 := Nat.add_one_mul_choose_eq m j
  calc (m + 2).choose (j + 2) * ((j + 2) * (j + 1))
      = ((m + 2).choose (j + 2) * (j + 2)) * (j + 1) := by ring
    _ = (m + 2) * ((m + 1).choose (j + 1) * (j + 1)) := by rw [← h1]; ring
    _ = (m + 2) * (m + 1) * m.choose j := by rw [← h2]; ring

private theorem binomProb_fact2_range (n : ℕ) (P : ℝ) :
    ∑ m ∈ range (n + 1), (m : ℝ) * ((m : ℝ) - 1) *
        ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))
      = (n : ℝ) * ((n : ℝ) - 1) * P ^ 2 := by
  match n with
  | 0 => simp
  | 1 => simp [sum_range_succ]
  | m + 2 =>
    rw [sum_range_succ', sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, sub_self, zero_mul, mul_zero, add_zero]
    have hterm : ∀ j ∈ range (m + 1),
        ((j + 1 + 1 : ℕ) : ℝ) * ((((j + 1 + 1 : ℕ)) : ℝ) - 1) *
          ((((m + 2).choose (j + 1 + 1) : ℕ) : ℝ) * P ^ (j + 1 + 1) *
            (1 - P) ^ (m + 2 - (j + 1 + 1)))
        = ((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1) * P ^ 2 *
          (((m.choose j : ℕ) : ℝ) * P ^ j * (1 - P) ^ (m - j)) := by
      intro j _
      have hc : (((m + 2).choose (j + 2) : ℕ) : ℝ) * ((j + 2) * (j + 1))
          = (m + 2) * (m + 1) * (m.choose j : ℝ) := by
        exact_mod_cast choose_add_two_mul m j
      rw [show m + 2 - (j + 1 + 1) = m - j by omega]
      push_cast
      linear_combination P ^ (j + 2) * (1 - P) ^ (m - j) * hc
    rw [sum_congr rfl hterm, ← mul_sum, binomProb_sum_range, mul_one]

private theorem expect_single {k n : ℕ} (P : Fin (k + 1) → ℝ) (j : Fin (k + 1))
    (g : Fin (n + 1) → ℝ) :
    expect n P (fun r => g (r j)) = ∑ s, binomProb n (P j) s * g s := by
  unfold expect
  have habs : ∀ r : Fin (k + 1) → Fin (n + 1),
      (∏ i, binomProb n (P i) (r i)) * g (r j)
      = ∏ i, (binomProb n (P i) (r i) * (if i = j then g (r i) else 1)) := by
    intro r
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq']
    simp
  simp only [habs]
  have huniv : Fintype.piFinset (fun _ : Fin (k + 1) => (univ : Finset (Fin (n + 1)))) =
      univ := by
    ext x
    simp
  have h := Finset.prod_univ_sum (fun _ : Fin (k + 1) => (univ : Finset (Fin (n + 1))))
    (fun i (s : Fin (n + 1)) => binomProb n (P i) s * (if i = j then g s else 1))
  rw [huniv] at h
  rw [← h]
  have hfac : ∀ i : Fin (k + 1),
      (∑ s, binomProb n (P i) s * (if i = j then g s else 1))
      = (if i = j then ∑ s, binomProb n (P j) s * g s else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [ite_eq_right hij, mul_one, binomProb_sum]
  simp only [hfac]
  rw [Finset.prod_ite_eq']
  simp

private theorem expect_pair {k n : ℕ} (P : Fin (k + 1) → ℝ) (j l : Fin (k + 1)) (hjl : j ≠ l)
    (g h : Fin (n + 1) → ℝ) :
    expect n P (fun r => g (r j) * h (r l))
      = (∑ s, binomProb n (P j) s * g s) * (∑ t, binomProb n (P l) t * h t) := by
  unfold expect
  have habs : ∀ r : Fin (k + 1) → Fin (n + 1),
      (∏ i, binomProb n (P i) (r i)) * (g (r j) * h (r l))
      = ∏ i, (binomProb n (P i) (r i) * (if i = j then g (r i) else 1) *
          (if i = l then h (r i) else 1)) := by
    intro r
    have hG : (∏ i, (if i = j then g (r i) else 1)) = g (r j) := by
      rw [Finset.prod_ite_eq']
      simp
    have hH : (∏ i, (if i = l then h (r i) else 1)) = h (r l) := by
      rw [Finset.prod_ite_eq']
      simp
    simp only [Finset.prod_mul_distrib, hG, hH]
    ring
  simp only [habs]
  have huniv : Fintype.piFinset (fun _ : Fin (k + 1) => (univ : Finset (Fin (n + 1)))) =
      univ := by
    ext x
    simp
  have hfactor := Finset.prod_univ_sum
    (fun _ : Fin (k + 1) => (univ : Finset (Fin (n + 1))))
    (fun i (s : Fin (n + 1)) => binomProb n (P i) s * (if i = j then g s else 1) *
      (if i = l then h s else 1))
  rw [huniv] at hfactor
  rw [← hfactor]
  have hfac : ∀ i : Fin (k + 1),
      (∑ s, binomProb n (P i) s * (if i = j then g s else 1) * (if i = l then h s else 1))
      = (if i = j then (∑ s, binomProb n (P j) s * g s)
         else if i = l then (∑ t, binomProb n (P l) t * h t) else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, ite_eq_right hjl, mul_one]
    · by_cases hil : i = l
      · subst hil
        simp only [ite_eq_right hij, ite_true, mul_one]
      · simp only [ite_eq_right hij, ite_eq_right hil, mul_one, binomProb_sum]
  simp only [hfac]
  have hsplit : (∏ i, (if i = j then (∑ s, binomProb n (P j) s * g s)
        else if i = l then (∑ t, binomProb n (P l) t * h t) else 1))
      = (∑ s, binomProb n (P j) s * g s) *
        ∏ i ∈ Finset.univ.erase j, (if i = j then (∑ s, binomProb n (P j) s * g s)
        else if i = l then (∑ t, binomProb n (P l) t * h t) else 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true]
  rw [hsplit]
  congr 1
  have herase : ∀ i ∈ Finset.univ.erase j,
      (if i = j then (∑ s, binomProb n (P j) s * g s)
        else if i = l then (∑ t, binomProb n (P l) t * h t) else 1)
      = (if i = l then (∑ t, binomProb n (P l) t * h t) else 1) := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact ite_eq_right hi
  have herase_prod : (∏ i ∈ Finset.univ.erase j, (if i = j then (∑ s, binomProb n (P j) s * g s)
        else if i = l then (∑ t, binomProb n (P l) t * h t) else 1))
      = ∏ i ∈ Finset.univ.erase j, (if i = l then (∑ t, binomProb n (P l) t * h t) else 1) :=
    Finset.prod_congr rfl (fun i hi => herase i hi)
  rw [herase_prod]
  have hmem : l ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ l⟩
  rw [Finset.prod_ite_eq', ite_eq_left hmem]

private theorem binomProb_second_range (n : ℕ) (P : ℝ) :
    ∑ m ∈ range (n + 1), (m : ℝ) ^ 2 * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))
      = (n : ℝ) * P * (1 - P) + ((n : ℝ) * P) ^ 2 := by
  have hsplit : ∀ m : ℕ,
      (m : ℝ) ^ 2 * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))
      = (m : ℝ) * ((m : ℝ) - 1) * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))
        + (m : ℝ) * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m)) := by
    intro m
    ring
  simp only [hsplit, Finset.sum_add_distrib, binomProb_fact2_range, binomProb_first_range]
  ring

private theorem binomProb_second (n : ℕ) (P : ℝ) :
    ∑ s : Fin (n + 1), (s : ℝ) ^ 2 * binomProb n P s
      = (n : ℝ) * P * (1 - P) + ((n : ℝ) * P) ^ 2 := by
  have h := Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (m : ℝ) ^ 2 * ((n.choose m : ℝ) * P ^ m * (1 - P) ^ (n - m))) (n + 1)
  rw [binomProb_second_range] at h
  simpa [binomProb, mul_assoc] using h

private theorem sum_mean {n : ℕ} (P : ℝ) (hn : 1 ≤ n) :
    ∑ s : Fin (n + 1), binomProb n P s * ((s : ℝ) / n) = P := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h : ∀ s : Fin (n + 1),
      binomProb n P s * ((s : ℝ) / n) = (1 / n) * ((s : ℝ) * binomProb n P s) := by
    intro s
    ring
  simp only [h, ← Finset.mul_sum, binomProb_first]
  field_simp

private theorem sum_centered {n : ℕ} (P : ℝ) (hn : 1 ≤ n) :
    ∑ s : Fin (n + 1), binomProb n P s * ((s : ℝ) / n - P) = 0 := by
  have h : ∀ s : Fin (n + 1),
      binomProb n P s * ((s : ℝ) / n - P)
      = binomProb n P s * ((s : ℝ) / n) - binomProb n P s * P := by
    intro s
    ring
  simp only [h, Finset.sum_sub_distrib, sum_mean P hn, ← Finset.sum_mul, binomProb_sum,
    one_mul, sub_self]

private theorem sum_sq {n : ℕ} (P : ℝ) (hn : 1 ≤ n) :
    ∑ s : Fin (n + 1), binomProb n P s * (((s : ℝ) / n - P) ^ 2)
      = P * (1 - P) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hexpand : ∀ s : Fin (n + 1),
      binomProb n P s * (((s : ℝ) / n - P) ^ 2)
      = (1 / n ^ 2) * ((s : ℝ) ^ 2 * binomProb n P s)
        - ((2 * P / n) * ((s : ℝ) * binomProb n P s))
        + P ^ 2 * binomProb n P s := by
    intro s
    field_simp
    ring
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    binomProb_second, binomProb_first, binomProb_sum, mul_one]
  field_simp
  ring

private theorem expect_mass {k n : ℕ} (P : Fin (k + 1) → ℝ) :
    expect n P (fun _ => 1) = 1 := by
  have h1 := expect_single (k := k) (n := n) P 0 (fun _ => (1 : ℝ))
  simpa [binomProb_sum] using h1

private theorem expect_const_mul {k n : ℕ} (P : Fin (k + 1) → ℝ) (c : ℝ)
    (f : (Fin (k + 1) → Fin (n + 1)) → ℝ) :
    expect n P (fun r => c * f r) = c * expect n P f := by
  unfold expect
  have hterm : ∀ r : Fin (k + 1) → Fin (n + 1),
      (∏ i, binomProb n (P i) (r i)) * (c * f r)
      = c * ((∏ i, binomProb n (P i) (r i)) * f r) := by
    intro r
    ring
  simp only [hterm, ← Finset.mul_sum]

private theorem expect_const {k n : ℕ} (P : Fin (k + 1) → ℝ) (c : ℝ) :
    expect n P (fun _ => c) = c := by
  have h : (fun _ : Fin (k + 1) → Fin (n + 1) => c) = (fun _ => c * 1) := by
    funext r
    exact (mul_one c).symm
  rw [h, expect_const_mul, expect_mass, mul_one]

private theorem expect_add {k n : ℕ} (P : Fin (k + 1) → ℝ)
    (f g : (Fin (k + 1) → Fin (n + 1)) → ℝ) :
    expect n P (fun r => f r + g r) = expect n P f + expect n P g := by
  unfold expect
  simp only [mul_add, Finset.sum_add_distrib]

private theorem expect_sub {k n : ℕ} (P : Fin (k + 1) → ℝ)
    (f g : (Fin (k + 1) → Fin (n + 1)) → ℝ) :
    expect n P (fun r => f r - g r) = expect n P f - expect n P g := by
  unfold expect
  simp only [mul_sub, Finset.sum_sub_distrib]

private theorem expect_sum {k n : ℕ} {ι : Type*} [Fintype ι] (P : Fin (k + 1) → ℝ)
    (F : ι → (Fin (k + 1) → Fin (n + 1)) → ℝ) :
    expect n P (fun r => ∑ i, F i r) = ∑ i, expect n P (fun r => F i r) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem expect_coord {k n : ℕ} (P : Fin (k + 1) → ℝ) (hn : 1 ≤ n) (j : Fin (k + 1)) :
    expect n P (fun r => ((r j : ℕ) : ℝ) / n) = P j := by
  have h := expect_single P j (fun s : Fin (n + 1) => ((s : ℕ) : ℝ) / n)
  simpa [sum_mean (P j) hn] using h

private theorem expect_centered {k n : ℕ} (P : Fin (k + 1) → ℝ) (hn : 1 ≤ n) (j : Fin (k + 1)) :
    expect n P (fun r => ((r j : ℕ) : ℝ) / n - P j) = 0 := by
  have h := expect_single P j (fun s : Fin (n + 1) => ((s : ℕ) : ℝ) / n - P j)
  simpa [sum_centered (P j) hn] using h

private theorem expect_centered_mul_off {k n : ℕ} (P : Fin (k + 1) → ℝ) (hn : 1 ≤ n)
    (j l : Fin (k + 1)) (hjl : j ≠ l) :
    expect n P (fun r => (((r j : ℕ) : ℝ) / n - P j) * (((r l : ℕ) : ℝ) / n - P l))
      = 0 := by
  have h := expect_pair P j l hjl (fun s : Fin (n + 1) => ((s : ℕ) : ℝ) / n - P j)
    (fun t : Fin (n + 1) => ((t : ℕ) : ℝ) / n - P l)
  simpa [sum_centered (P j) hn, sum_centered (P l) hn] using h

private theorem expect_centered_sq {k n : ℕ} (P : Fin (k + 1) → ℝ) (hn : 1 ≤ n)
    (j : Fin (k + 1)) :
    expect n P (fun r => (((r j : ℕ) : ℝ) / n - P j) ^ 2) = P j * (1 - P j) / n := by
  have h := expect_single P j (fun s : Fin (n + 1) => (((s : ℕ) : ℝ) / n - P j) ^ 2)
  simpa [sum_sq (P j) hn] using h

private theorem expect_centered_mul {k n : ℕ} (P : Fin (k + 1) → ℝ) (hn : 1 ≤ n)
    (j l : Fin (k + 1)) :
    expect n P (fun r => (((r j : ℕ) : ℝ) / n - P j) * (((r l : ℕ) : ℝ) / n - P l))
      = (if j = l then P j * (1 - P j) / n else 0) := by
  by_cases hjl : j = l
  · subst hjl
    simp only [← pow_two]
    rw [expect_centered_sq P hn j]
    simp
  · rw [expect_centered_mul_off P hn j l hjl]
    simp [hjl]

private noncomputable def midPt (x₀ d : ℝ) (t : ℕ) : ℝ :=
  ((x₀ + (t : ℝ) * d) + (x₀ + ((t : ℝ) + 1) * d)) / 2

private noncomputable def weight (x₀ d : ℝ) (k : ℕ) : Fin (k + 1) → ℝ :=
  fun j => (if 0 < j.val then midPt x₀ d (j.val - 1) else 0)
    - (if j.val < k then midPt x₀ d j.val else 0)

private theorem midPt_sub (x₀ d : ℝ) (a : ℕ) :
    midPt x₀ d a - midPt x₀ d (a + 1) = -d := by
  simp only [midPt]
  push_cast
  ring

private theorem sum_edge_eq_sum_vertex (x₀ d : ℝ) (k : ℕ) (F : Fin (k + 1) → ℝ) :
    ∑ i : Fin k, (F i.succ - F i.castSucc) * midPt x₀ d i
      = ∑ j, weight x₀ d k j * F j := by
  have hsplit : ∀ i : Fin k,
      (F i.succ - F i.castSucc) * midPt x₀ d ↑i
      = F i.succ * midPt x₀ d ↑i - F i.castSucc * midPt x₀ d ↑i := by
    intro i
    ring
  simp only [hsplit, Finset.sum_sub_distrib]
  have hB : (∑ i : Fin k, F i.succ * midPt x₀ d ↑i)
      = ∑ j : Fin (k + 1),
        F j * (if 0 < j.val then midPt x₀ d (j.val - 1) else 0) := by
    have h := Fin.sum_univ_succ
      (fun j : Fin (k + 1) =>
        F j * (if 0 < j.val then midPt x₀ d (j.val - 1) else 0))
    have hG0 : F (0 : Fin (k + 1)) *
        (if 0 < (0 : Fin (k + 1)).val
          then midPt x₀ d ((0 : Fin (k + 1)).val - 1) else 0) = 0 := by
      simp
    have hGs : ∀ i : Fin k,
        F i.succ * (if 0 < (i.succ).val then midPt x₀ d ((i.succ).val - 1) else 0)
        = F i.succ * midPt x₀ d ↑i := by
      intro i
      have hpos : 0 < (i.succ).val := by simp
      rw [ite_eq_left hpos, Fin.val_succ, Nat.add_sub_cancel]
    simp only [hG0, hGs, zero_add] at h
    exact h.symm
  have hA : (∑ i : Fin k, F i.castSucc * midPt x₀ d ↑i)
      = ∑ j : Fin (k + 1), F j * (if j.val < k then midPt x₀ d j.val else 0) := by
    have h := Fin.sum_univ_castSucc
      (fun j : Fin (k + 1) => F j * (if j.val < k then midPt x₀ d j.val else 0))
    have hGlast : F (Fin.last k) *
        (if (Fin.last k).val < k then midPt x₀ d (Fin.last k).val else 0) = 0 := by
      simp
    have hGcs : ∀ i : Fin k,
        F i.castSucc * (if (i.castSucc).val < k then midPt x₀ d (i.castSucc).val else 0)
        = F i.castSucc * midPt x₀ d ↑i := by
      intro i
      have hlt : (i.castSucc).val < k := by simp
      rw [ite_eq_left hlt, Fin.val_castSucc]
    simp only [hGlast, hGcs, add_zero] at h
    exact h.symm
  rw [hB, hA, ← Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin (k + 1),
      F j * (if 0 < j.val then midPt x₀ d (j.val - 1) else 0)
        - F j * (if j.val < k then midPt x₀ d j.val else 0)
      = weight x₀ d k j * F j := by
    intro j
    simp only [weight]
    ring
  simp only [hterm]

private theorem weight_sq_mul (x₀ d : ℝ) (k : ℕ) (P : Fin (k + 1) → ℝ)
    (h₀ : P 0 = 0) (hk₁ : P (Fin.last k) = 1) (j : Fin (k + 1)) :
    (weight x₀ d k j) ^ 2 * (P j * (1 - P j)) = d ^ 2 * (P j * (1 - P j)) := by
  by_cases hj0 : j = 0
  · subst hj0
    simp [h₀]
  · by_cases hjl : j = Fin.last k
    · subst hjl
      simp [hk₁]
    · have hval0 : j.val = 0 → j = 0 := by
        intro hcon
        ext
        simp [hcon]
      have hpos : 0 < j.val := Nat.pos_of_ne_zero (fun hcon => hj0 (hval0 hcon))
      have hvalk : j.val = k → j = Fin.last k := by
        intro hcon
        ext
        simp [hcon]
      have hne : j.val ≠ k := fun hcon => hjl (hvalk hcon)
      have hlt : j.val < k := by
        have hle : j.val ≤ k := Nat.le_of_lt_succ j.is_lt
        omega
      have hw : weight x₀ d k j = -d := by
        simp only [weight, ite_eq_left hpos, ite_eq_left hlt]
        set a := j.val - 1 with ha
        have hval : j.val = a + 1 := by omega
        rw [hval]
        exact midPt_sub x₀ d a
      rw [hw]
      ring

private theorem vertex_form_est {k n : ℕ} (x₀ d : ℝ) (r : Fin (k + 1) → Fin (n + 1)) :
    estimator x₀ d n r = ∑ j, weight x₀ d k j * (((r j : ℕ) : ℝ) / n) := by
  have hreg := sum_edge_eq_sum_vertex x₀ d k (fun i => (((r i : ℕ) : ℝ) / n))
  have hbridge : ∀ i : Fin k,
      ((((r i.succ : ℕ) : ℝ) / n) - (((r i.castSucc : ℕ) : ℝ) / n)) *
        (((x₀ + ((i : ℕ) : ℝ) * d) + (x₀ + (((i : ℕ) : ℝ) + 1) * d))) / 2
      = ((((r i.succ : ℕ) : ℝ) / n) - (((r i.castSucc : ℕ) : ℝ) / n)) *
        midPt x₀ d ↑i := by
    intro i
    simp only [midPt]
    ring
  calc estimator x₀ d n r
      = ∑ i : Fin k, ((((r i.succ : ℕ) : ℝ) / n) - (((r i.castSucc : ℕ) : ℝ) / n)) *
        midPt x₀ d ↑i := by
        unfold estimator spearmanKarber
        simp only [hbridge]
    _ = ∑ j, weight x₀ d k j * (((r j : ℕ) : ℝ) / n) := hreg

private theorem vertex_form_karber (x₀ d : ℝ) (k : ℕ) (P : Fin (k + 1) → ℝ) :
    spearmanKarber x₀ d P = ∑ j, weight x₀ d k j * P j := by
  have hreg := sum_edge_eq_sum_vertex x₀ d k P
  have hbridge : ∀ i : Fin k,
      (P i.succ - P i.castSucc) *
        (((x₀ + ((i : ℕ) : ℝ) * d) + (x₀ + (((i : ℕ) : ℝ) + 1) * d))) / 2
      = (P i.succ - P i.castSucc) * midPt x₀ d ↑i := by
    intro i
    simp only [midPt]
    ring
  unfold spearmanKarber
  simp only [hbridge]
  exact hreg

private theorem mean_part {k n : ℕ} (x₀ d : ℝ) (hn : 1 ≤ n) (P : Fin (k + 1) → ℝ) :
    expect n P (estimator x₀ d n) = spearmanKarber x₀ d P := by
  have h1 : estimator x₀ d n
      = (fun r => ∑ j, weight x₀ d k j * (((r j : ℕ) : ℝ) / n)) :=
    funext (vertex_form_est x₀ d)
  rw [h1]
  simp only [expect_sum, expect_const_mul, expect_coord P hn _]
  rw [← vertex_form_karber]

private theorem variance_part {k n : ℕ} (x₀ d : ℝ) (hn : 1 ≤ n) (P : Fin (k + 1) → ℝ)
    (h₀ : P 0 = 0) (hk₁ : P (Fin.last k) = 1) :
    expect n P (fun r => (estimator x₀ d n r - spearmanKarber x₀ d P) ^ 2) =
      d ^ 2 * (∑ i, P i * (1 - P i)) / n := by
  have hdiff : ∀ r : Fin (k + 1) → Fin (n + 1),
      estimator x₀ d n r - spearmanKarber x₀ d P
      = ∑ j, weight x₀ d k j * (((r j : ℕ) : ℝ) / n - P j) := by
    intro r
    rw [vertex_form_est x₀ d r, vertex_form_karber, ← Finset.sum_sub_distrib]
    have hterm : ∀ j : Fin (k + 1),
        weight x₀ d k j * (((r j : ℕ) : ℝ) / n) - weight x₀ d k j * P j
        = weight x₀ d k j * (((r j : ℕ) : ℝ) / n - P j) := by
      intro j
      ring
    simp only [hterm]
  have hsq : ∀ r : Fin (k + 1) → Fin (n + 1),
      (estimator x₀ d n r - spearmanKarber x₀ d P) ^ 2
      = ∑ j, ∑ l, (weight x₀ d k j * (((r j : ℕ) : ℝ) / n - P j)) *
        (weight x₀ d k l * (((r l : ℕ) : ℝ) / n - P l)) := by
    intro r
    rw [hdiff r, pow_two, Finset.sum_mul_sum]
  have hconst : ∀ j l : Fin (k + 1),
      expect n P (fun r => (weight x₀ d k j * (((r j : ℕ) : ℝ) / n - P j)) *
        (weight x₀ d k l * (((r l : ℕ) : ℝ) / n - P l)))
      = weight x₀ d k j * weight x₀ d k l *
        expect n P (fun r => (((r j : ℕ) : ℝ) / n - P j) * (((r l : ℕ) : ℝ) / n - P l)) := by
    intro j l
    have hfactor : (fun r : Fin (k + 1) → Fin (n + 1) =>
          (weight x₀ d k j * (((r j : ℕ) : ℝ) / n - P j)) *
          (weight x₀ d k l * (((r l : ℕ) : ℝ) / n - P l)))
        = (fun r => (weight x₀ d k j * weight x₀ d k l) *
          ((((r j : ℕ) : ℝ) / n - P j) * (((r l : ℕ) : ℝ) / n - P l))) := by
      funext r
      ring
    rw [hfactor, expect_const_mul]
  have hE : expect n P (fun r => (estimator x₀ d n r - spearmanKarber x₀ d P) ^ 2)
      = ∑ j, ∑ l, weight x₀ d k j * weight x₀ d k l *
        expect n P (fun r => (((r j : ℕ) : ℝ) / n - P j) * (((r l : ℕ) : ℝ) / n - P l)) := by
    simp only [hsq, expect_sum, hconst]
  rw [hE]
  simp only [expect_centered_mul P hn]
  have hinner : ∀ j : Fin (k + 1),
      (∑ l, weight x₀ d k j * weight x₀ d k l *
        (if j = l then P j * (1 - P j) / n else 0))
      = (weight x₀ d k j) ^ 2 * (P j * (1 - P j) / n) := by
    intro j
    have hterm : ∀ l : Fin (k + 1),
        weight x₀ d k j * weight x₀ d k l * (if j = l then P j * (1 - P j) / n else 0)
        = (if j = l then weight x₀ d k j * weight x₀ d k l * (P j * (1 - P j) / n)
          else 0) := by
      intro l
      by_cases hjl : j = l
      · subst hjl
        simp
      · simp [hjl]
    simp only [hterm]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  simp only [hinner]
  have hweight : ∀ j : Fin (k + 1),
      (weight x₀ d k j) ^ 2 * (P j * (1 - P j) / n)
      = d ^ 2 * (P j * (1 - P j)) / n := by
    intro j
    have h := weight_sq_mul x₀ d k P h₀ hk₁ j
    linear_combination h / n
  simp only [hweight]
  have hdiv : ∀ j : Fin (k + 1),
      d ^ 2 * (P j * (1 - P j)) / n = (1 / n) * (d ^ 2 * (P j * (1 - P j))) := by
    intro j
    ring
  simp only [hdiv, ← Finset.mul_sum]
  ring

/-- **Unbiasedness and exact variance** (Irwin and Cheeseman 1939, p. 574; derived): let `d > 0`,
`n ≥ 1`, and let the true response probabilities satisfy `0 ≤ Pᵢ ≤ 1`, `P₀ = 0`, `P_k = 1`, and
be nondecreasing in dose (`Pᵢ ≤ Pᵢ₊₁` for `i < k`), so that the interpolated tolerance
distribution, with mass `Pᵢ₊₁ - Pᵢ ≥ 0` at `(xᵢ + xᵢ₊₁) / 2`, is a probability distribution.
For independent binomial(`n`, `Pᵢ`) counts at the doses `xᵢ = x₀ + i d`, the Spearman–Kärber
estimator `m` has expectation equal to the mean of the interpolated tolerance distribution,
`E[m] = ∑ᵢ (Pᵢ₊₁ - Pᵢ) (xᵢ + xᵢ₊₁) / 2`, and variance `E[(m - E[m])²] = d² ∑ᵢ Pᵢ (1 - Pᵢ) / n`.

Source: Irwin and Cheeseman (1939), p. 574. -/
public theorem expect_variance (x₀ d : ℝ) (hd : 0 < d) (k n : ℕ) (hn : 1 ≤ n)
    (P : Fin (k + 1) → ℝ) (hP : ∀ i, 0 ≤ P i ∧ P i ≤ 1) (h₀ : P 0 = 0)
    (hk₁ : P (Fin.last k) = 1) (hmono : ∀ i : Fin k, P i.castSucc ≤ P i.succ) :
    expect n P (estimator x₀ d n) = spearmanKarber x₀ d P ∧
      expect n P (fun r => (estimator x₀ d n r - spearmanKarber x₀ d P) ^ 2) =
        d ^ 2 * (∑ i, P i * (1 - P i)) / n
    := by
  -- The proof does not need `hd`, `hP` or `hmono`; they stay in the statement, which is kept
  -- token for token, and these lines keep the unused-variable linter quiet.
  have _ := hd
  have _ := hP
  have _ := hmono
  exact ⟨mean_part x₀ d hn P, variance_part x₀ d hn P h₀ hk₁⟩

end WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted
