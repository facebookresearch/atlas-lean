/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central

/-!
# The sharp Littlewood–Offord bound

`littlewoodOffordSharpBound` bounds the number of signed sums in an open interval of length two
by applying Sperner's theorem to the sets of positive summands.
-/

public section

namespace MathlibExt.Combinatorics.ScottishBook179Wanted

open Finset

private lemma signedCount_le_middle {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (ha : ∀ i, 1 ≤ |a i|) :
    (univ.filter (fun ε : Fin n → Bool =>
      |c + ∑ i, (if ε i then (1 : ℝ) else -1) * a i| < 1)).card ≤ n.choose (n / 2) := by
  classical
  let support (ε : Fin n → Bool) := univ.filter (fun i => ε i = decide (0 ≤ a i))
  let value (s : Finset (Fin n)) := c + 2 * ∑ i ∈ s, |a i| - ∑ i, |a i|
  let family := univ.filter (fun s => |value s| < 1)
  have hinj : Function.Injective support := by
    intro ε δ heq
    funext i
    have h := Finset.ext_iff.mp heq i
    simp only [support, mem_filter, mem_univ, true_and] at h
    exact (by decide : ∀ x y b : Bool, (x = b ↔ y = b) → x = y) _ _ _ h
  have hvalue (ε : Fin n → Bool) :
      c + ∑ i, (if ε i then (1 : ℝ) else -1) * a i = value (support ε) := by
    simp only [value, support, sum_filter, mul_sum, add_sub_assoc, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · cases ε i <;> simp [hi, abs_of_nonneg hi]
      ring
    · cases ε i <;> simp [hi, abs_of_neg (lt_of_not_ge hi)]
      ring
  have hanti : IsAntichain (· ⊆ ·) (family : Set (Finset (Fin n))) := by
    intro s hs t ht hne hst
    have hs' := (abs_lt.mp (mem_filter.mp hs).2).1
    have ht' := (abs_lt.mp (mem_filter.mp ht).2).2
    obtain ⟨i, hi⟩ := sdiff_nonempty.mpr (fun hts => hne (Subset.antisymm hst hts))
    have hdiff : 1 ≤ ∑ j ∈ t \ s, |a j| :=
      (ha i).trans (single_le_sum (fun j _ => abs_nonneg (a j)) hi)
    have hsum := sum_sdiff hst (f := fun j => |a j|)
    dsimp [value] at hs' ht'
    linarith
  refine le_trans (card_le_card_of_injOn (t := family) support ?_ hinj.injOn) ?_
  · intro ε hε
    exact mem_filter.mpr ⟨mem_univ _, (hvalue ε) ▸ (mem_filter.mp hε).2⟩
  · simpa using hanti.sperner

-- Squaring the estimate keeps the central-binomial recurrence in natural numbers.
private lemma centralBinom_sq_bound (k : ℕ) : (2 * k + 1) * k.centralBinom ^ 2 ≤ 16 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine Nat.le_of_mul_le_mul_left (c := (k + 1) ^ 2) ?_ (by positivity)
    calc
      _ = (2 * k + 3) * ((k + 1) * (k + 1).centralBinom) ^ 2 := by ring
      _ = (2 * k + 3) * (2 * (2 * k + 1) * k.centralBinom) ^ 2 := by
        rw [Nat.succ_mul_centralBinom_succ]
      _ ≤ (k + 1) ^ 2 * 16 * ((2 * k + 1) * k.centralBinom ^ 2) := by ring_nf; omega
      _ ≤ (k + 1) ^ 2 * 16 * 16 ^ k := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ring

private lemma middle_sq_bound (n : ℕ) : n * (n.choose (n / 2)) ^ 2 ≤ 4 ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * k / 2 = k by omega, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    exact (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans (centralBinom_sq_bound k)
  · have hodd : (2 * k + 1).choose k ≤ 2 * k.centralBinom := by
      rw [← Nat.choose_symm_half, Nat.choose_succ_succ', two_mul k.centralBinom]
      exact Nat.add_le_add_left (Nat.choose_le_centralBinom _ _) _
    rw [show (2 * k + 1) / 2 = k by omega, pow_succ 4, pow_mul]
    calc
      _ ≤ (2 * k + 1) * (2 * k.centralBinom) ^ 2 := by gcongr
      _ = ((2 * k + 1) * k.centralBinom ^ 2) * 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (centralBinom_sq_bound k)

/--
**Sharp Littlewood–Offord bound.** There is a real constant $A \ge 0$ such that for every
integer $n \ge 1$ and all real numbers $a_0, a_1, \dots, a_n$ with $|a_i| \ge 1$ for every $i$,
the number of sign vectors $(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ with
$|a_0 + \varepsilon_1 a_1 + \dots + \varepsilon_n a_n| < 1$ is at most $A \cdot 2^n / \sqrt{n}$.

This answers Offord's Problem 179 from the Scottish Book. In the original notation the bound is
on the exceptional set of signed sums $a_0 + \varepsilon_1 a_1 + \dots + \varepsilon_n a_n$
whose absolute value is below $\min_\nu |a_\nu|$; the statement here is the rescaled form with
$\min_\nu |a_\nu| = 1$.

Source: A. C. Offord, Problem 179 of the Scottish
Book; the Littlewood-Offord lemma (Littlewood-Offord, 1938) and Erdős's
proof giving the sharp `O(2 ^ n / √n)` bound, attained when all the
`a nu` are equal. See the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem littlewoodOffordSharpBound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → ℝ),
      (∀ i, 1 ≤ |a i|) →
      ((Finset.univ.filter (fun ε : Fin n → Bool =>
        |a 0 + ∑ i : Fin n, (if ε i then (1 : ℝ) else -1) * a (Fin.succ i)| < 1)).card :
        ℝ) ≤ A * (2 : ℝ) ^ n / Real.sqrt n := by
  refine ⟨1, zero_le_one, ?_⟩
  intro n hn a ha
  have hcount := signedCount_le_middle (a 0) (fun i => a (Fin.succ i)) (fun i => ha i.succ)
  refine (Nat.cast_le.mpr hcount).trans ?_
  rw [one_mul, le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hn))]
  have hsq : (n : ℝ) * (n.choose (n / 2) : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
    exact_mod_cast middle_sq_bound n
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_comm, pow_right_comm]
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq

end MathlibExt.Combinatorics.ScottishBook179Wanted
