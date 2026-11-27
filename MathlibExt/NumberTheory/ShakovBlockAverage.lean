/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ShakovTwoRegular
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block averages of Shakov's sequence

We derive a recurrence for the sums over dyadic blocks of Shakov's sequence and
solve it to obtain a closed formula for their averages.
-/

namespace MathlibExt.NumberTheory.ShakovTwoRegularWanted

namespace block_average

/-- Group an interval with even endpoints into consecutive pairs. -/
private theorem sum_Ico_double {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    (∑ t ∈ Finset.Ico (2 * a) (2 * b), f t) =
      ∑ k ∈ Finset.Ico a b, (f (2 * k) + f (2 * k + 1)) := by
  calc
    _ = ∑ p ∈ Finset.Ico a b ×ˢ (Finset.univ : Finset (Fin 2)), f (2 * p.1 + p.2.val) := by
      refine Finset.sum_nbij' (fun t ↦ (t / 2, ⟨t % 2, Nat.mod_lt _ (by decide)⟩))
        (fun p ↦ 2 * p.1 + p.2.val) ?_ ?_ ?_ ?_ ?_
      · simp only [Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_Ico]
        omega
      · intro p hp
        have hp₁ := Finset.mem_Ico.mp (Finset.mem_product.mp hp).1
        have hp₂ := p.2.isLt
        exact Finset.mem_Ico.mpr (by omega)
      · intro t _
        change 2 * (t / 2) + t % 2 = t
        omega
      · intro p _
        have hp₂ := p.2.isLt
        refine Prod.ext ?_ (Fin.ext ?_)
        · change (2 * p.1 + p.2.val) / 2 = p.1
          omega
        · change (2 * p.1 + p.2.val) % 2 = p.2.val
          omega
      · intro t _
        change f t = f (2 * (t / 2) + t % 2)
        congr 1
        omega
    _ = _ := by
      rw [Finset.sum_product]
      exact Finset.sum_congr rfl fun k _ ↦ Fin.sum_univ_two (fun i : Fin 2 ↦ f (2 * k + i.val))

/-- The real-valued sum over the dyadic block starting at the given power of two. -/
private def blockSum (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), (shakovSeq t : ℝ)

/-- Adding the four defining equations gives the sum of the four grandchildren of `k`. -/
private theorem sum_grandchildren (k : ℕ) (hk : 1 ≤ k) :
    (shakovSeq (2 * (2 * k)) : ℝ) + (shakovSeq (2 * (2 * k) + 1) : ℝ) +
        ((shakovSeq (2 * (2 * k + 1)) : ℝ) + (shakovSeq (2 * (2 * k + 1) + 1) : ℝ)) =
      5 * ((shakovSeq (2 * k) : ℝ) + (shakovSeq (2 * k + 1) : ℝ)) -
        2 * (shakovSeq k : ℝ) := by
  have step (i : ℕ) (hi : i < 4) :
      shakovSeq (4 * k + i) =
        if i = 0 then 2 * shakovSeq (2 * k) - shakovSeq k
        else if i = 1 then 2 * shakovSeq (2 * k) + shakovSeq (2 * k + 1)
        else if i = 2 then 2 * shakovSeq (2 * k + 1) + shakovSeq (2 * k)
        else 2 * shakovSeq (2 * k + 1) - shakovSeq k := by
    have h : 4 * k + i - 4 + 4 = 4 * k + i := by omega
    conv_lhs => rw [← h, shakovSeq.eq_5, h]
    rw [show (4 * k + i) / 4 = k by omega, show (4 * k + i) % 4 = i by omega]
  rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 by omega,
    show 2 * (2 * k + 1) = 4 * k + 2 by omega,
    show 2 * (2 * k) + 1 = 4 * k + 1 by omega,
    show 2 * (2 * k) = 4 * k + 0 by omega,
    step 0 (by decide), step 1 (by decide), step 2 (by decide), step 3 (by decide)]
  push_cast
  ring

private theorem blockSum_recurrence (n : ℕ) :
    blockSum (n + 2) = 5 * blockSum (n + 1) - 2 * blockSum n := by
  have split (m : ℕ) :=
    sum_Ico_double (fun t ↦ (shakovSeq t : ℝ)) (2 ^ m) (2 ^ (m + 1))
  have splitPairs := sum_Ico_double
    (fun t ↦ (shakovSeq (2 * t) : ℝ) + (shakovSeq (2 * t + 1) : ℝ)) (2 ^ n) (2 ^ (n + 1))
  simp only [← pow_succ'] at split splitPairs
  unfold blockSum
  rw [split (n + 1), splitPairs, split n, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k hk ↦
    sum_grandchildren k ((Nat.one_le_pow n 2 (by decide)).trans (Finset.mem_Ico.mp hk).1)

private theorem blockSum_eq (n : ℕ) :
    blockSum n = 2 * (((5 + Real.sqrt 17) / 2) ^ n - ((5 - Real.sqrt 17) / 2) ^ n) /
      Real.sqrt 17 := by
  let a : ℝ := (5 + Real.sqrt 17) / 2
  let b : ℝ := (5 - Real.sqrt 17) / 2
  change blockSum n = 2 * (a ^ n - b ^ n) / Real.sqrt 17
  have hab : a - b = Real.sqrt 17 := by dsimp [a, b]; ring
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs₀ : Real.sqrt 17 ≠ 0 := by positivity
  have ha : a ^ 2 = 5 * a - 2 := by dsimp [a]; nlinarith
  have hb : b ^ 2 = 5 * b - 2 := by dsimp [b]; nlinarith
  have pow_step (x : ℝ) (hx : x ^ 2 = 5 * x - 2) (k : ℕ) :
      x ^ (k + 2) = 5 * x ^ (k + 1) - 2 * x ^ k := by
    rw [pow_add, hx, pow_succ]
    ring
  induction n using Nat.twoStepInduction with
  | zero => norm_num [blockSum, Nat.Ico_succ_singleton, shakovSeq.eq_2]
  | one =>
    have h : Finset.Ico 2 4 = {2, 3} := by decide
    norm_num [blockSum, h, shakovSeq.eq_3, shakovSeq.eq_4, hab, hs₀, mul_div_assoc]
  | more n ih₀ ih₁ =>
    rw [blockSum_recurrence, ih₀, ih₁, pow_step a ha n, pow_step b hb n]
    ring

end block_average

open block_average in
/-- **Block averages of Shakov's sequence.** Let $s$ be Shakov's $2$-regular sequence.
For every natural number $n$,
$$
\frac{1}{2^n} \sum_{2^n \le t < 2^{n+1}} s(t) =
\frac{(5 + \sqrt{17})^n - (5 - \sqrt{17})^n}{2^{2n-1} \sqrt{17}},
$$
where the exponent $2n - 1$ is read as $0$ when $n = 0$ (both sides are then $0$).

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 7. -/
public theorem block_average (n : ℕ) :
    (1 / (2 : ℝ) ^ n) *
        (∑ t ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)),
          (shakovSeq t : ℝ)) =
      ((5 + Real.sqrt 17) ^ n - (5 - Real.sqrt 17) ^ n) /
        ((2 : ℝ) ^ (2 * n - 1) * Real.sqrt 17) := by
  change (1 / (2 : ℝ) ^ n) * blockSum n = _
  cases n with
  | zero => norm_num [blockSum, Nat.Ico_succ_singleton, shakovSeq.eq_2]
  | succ n =>
    rw [blockSum_eq]
    simp only [div_pow, ← sub_div]
    rw [show 2 * (n + 1) - 1 = (n + 1) + n by omega,
      pow_add (2 : ℝ) (n + 1) n, pow_succ' (2 : ℝ) n]
    have h₂ : (2 : ℝ) ^ n ≠ 0 := by positivity
    have hs : Real.sqrt 17 ≠ 0 := by positivity
    field_simp

end MathlibExt.NumberTheory.ShakovTwoRegularWanted
