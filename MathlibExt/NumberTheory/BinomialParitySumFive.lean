/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomialModTwoRunLength
import Mathlib.Data.Nat.Choose.Lucas

/-!
# A binomial parity sum with upper argument `n + 5 * k`

We prove the run length transform identity of Rampersad and Wiebe by applying Lucas's theorem
to the low binary digits of both binomial coefficients and tracking the resulting carries.
-/

namespace MetaMathlibExt
namespace runLengthTransform_choose_add_five_mul_two_mul_add_two_mul

-- The carries a and b are added to the upper and lower arguments of the first binomial.
private def term (a b n k : ℕ) : ℤ :=
  (((n + 5 * k + a).choose (2 * n + 2 * k + b) * n.choose k) % 2 : ℕ)

private def count (a b n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), term a b n k

private theorem choose_step (x y a b : ℕ) :
    (2 * x + a).choose (2 * y + b) ≡
      (a % 2).choose (b % 2) * (x + a / 2).choose (y + b / 2) [MOD 2] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  convert! Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := 2) (n := 2 * x + a) (k := 2 * y + b) using 2 <;> congr 1 <;> omega

private theorem choose_digit {r s : ℕ} (hr : r < 2) (hs : s < 2) :
    r.choose s = if s ≤ r then 1 else 0 := by
  interval_cases r <;> interval_cases s <;> decide

-- Each surviving pair of low digits contributes exactly the term for the next two carries.
private theorem term_step (a b n k d e : ℕ) (hd : d < 2) (he : e < 2) :
    term a b (2 * n + d) (2 * k + e) =
      if e ≤ d ∧ (2 * d + 2 * e + b) % 2 ≤ (d + 5 * e + a) % 2 then
        term ((d + 5 * e + a) / 2) ((2 * d + 2 * e + b) / 2) n k else 0 := by
  let u := d + 5 * e + a
  let v := 2 * d + 2 * e + b
  have h := (choose_step (n + 5 * k) (2 * n + 2 * k) u v).mul (choose_step n k d e)
  rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he, Nat.div_eq_of_lt hd, Nat.div_eq_of_lt he,
    add_zero, add_zero, choose_digit hd he, choose_digit (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))] at h
  have htop : 2 * n + d + 5 * (2 * k + e) + a = 2 * (n + 5 * k) + u := by dsimp [u]; omega
  have hbot : 2 * (2 * n + d) + 2 * (2 * k + e) + b = 2 * (2 * n + 2 * k) + v := by
    dsimp [v]; omega
  unfold term
  rw [htop, hbot, h]
  by_cases h₁ : e ≤ d <;> by_cases h₂ : v % 2 ≤ u % 2 <;>
    dsimp only [v, u] at h₂ ⊢ <;> simp [h₁, h₂]

private theorem sum_pairs (f : ℕ → ℤ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k =
      ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

private def branch (a b n d e : ℕ) : ℤ :=
  if e ≤ d ∧ (2 * d + 2 * e + b) % 2 ≤ (d + 5 * e + a) % 2 then
    count ((d + 5 * e + a) / 2) ((2 * d + 2 * e + b) / 2) n else 0

private theorem count_step (a b n d : ℕ) (hd : d < 2) :
    count a b (2 * n + d) = branch a b n d 0 + branch a b n d 1 := by
  have pad : count a b (2 * n + d) = ∑ k ∈ Finset.range (2 * (n + 1)), term a b (2 * n + d) k := by
    unfold count
    rw [Nat.mul_succ]
    interval_cases d
    · simp only [add_zero, Finset.sum_range_succ (n := 2 * n + 1)]
      simp [term]
    · rfl
  rw [pad, sum_pairs, Finset.sum_add_distrib]
  have evenTerm (k : ℕ) := term_step a b n k d 0 hd (by decide)
  simp only [add_zero] at evenTerm
  simp only [evenTerm, term_step a b n _ d 1 hd (by decide)]
  simp [branch, count, Finset.sum_ite_irrel]

-- Include a pending run of c ones when reading the remaining digits.
private def weight (S : ℕ → ℤ) (bs : List ℕ) (c : ℕ) : ℤ :=
  ((bitRunLengths bs c).map S).prod

private theorem weight_nil (S : ℕ → ℤ) (h0 : S 0 = 1) (c : ℕ) :
    weight S [] c = S c := by
  by_cases hc : c = 0 <;> simp [weight, bitRunLengths, hc, h0]

private theorem weight_cons (S : ℕ → ℤ) (h0 : S 0 = 1) (d : ℕ) (bs : List ℕ) (c : ℕ) :
    weight S (d :: bs) c =
      if d = 1 then weight S bs (c + 1) else S c * weight S bs 0 := by
  by_cases hd : d = 1 <;> by_cases hc : c = 0 <;> simp [weight, bitRunLengths, hd, hc, h0]

private theorem weight_rec (S : ℕ → ℤ) (h0 : S 0 = 1)
    (hs : ∀ c, S (c + 4) = S (c + 3) + S (c + 2) - S (c + 1) + S c)
    (bs : List ℕ) (c : ℕ) :
    weight S bs (c + 4) = weight S bs (c + 3) + weight S bs (c + 2) -
      weight S bs (c + 1) + weight S bs c := by
  induction bs generalizing c with
  | nil => simpa only [weight_nil S h0] using hs c
  | cons d bs ih =>
    simp only [weight_cons S h0]
    by_cases hd : d = 1
    · simpa only [hd, ↓reduceIte] using ih (c + 1)
    · simp only [ite_eq_right hd, ← add_mul, ← sub_mul, hs]

-- Only eight carry pairs are reachable from (0, 0). The first four equations combine their
-- counts to give the weights for zero through three pending ones. The last four relations
-- ensure that a zero resets these weights and a one advances them by the recurrence.
private def Matches (n : ℕ) (f : ℕ → ℤ) : Prop :=
  count 0 0 n = f 0 ∧
  count 3 2 n = f 1 ∧
  count 2 2 n + count 4 3 n = f 2 ∧
  count 1 2 n + count 2 2 n + count 4 3 n = f 3 ∧
  count 0 1 n = 0 ∧
  count 1 1 n = count 0 0 n ∧
  count 3 3 n + count 4 3 n = count 3 2 n ∧
  count 1 2 n + count 3 3 n + count 3 2 n = count 4 3 n + count 2 2 n + count 0 0 n

private theorem matches_digits (S : ℕ → ℤ) (h0 : S 0 = 1) (h1 : S 1 = 1)
    (h2 : S 2 = 1) (h3 : S 3 = 1)
    (hs : ∀ c, S (c + 4) = S (c + 3) + S (c + 2) - S (c + 1) + S c)
    (bs : List ℕ) (hbs : ∀ d ∈ bs, d < 2) :
    Matches (Nat.ofDigits 2 bs) (weight S bs) := by
  induction bs with
  | nil => norm_num [Matches, count, term, weight_nil S h0, h0, h1, h2, h3, Nat.choose]
  | cons d bs ih =>
    let n := Nat.ofDigits 2 bs
    have hd := hbs d List.mem_cons_self
    have htail := ih (fun t ht => hbs t (List.mem_cons_of_mem d ht))
    change Matches n (weight S bs) at htail
    obtain ⟨ha, hb, hc, he, hf, hg, hh, hi⟩ := htail
    rw [Nat.ofDigits_cons, Nat.add_comm]
    change Matches (2 * n + d) (weight S (d :: bs))
    have hfour := weight_rec S h0 hs bs 0
    simp only [Nat.zero_add] at hfour
    unfold Matches
    simp only [count_step _ _ n d hd, branch, weight_cons S h0]
    interval_cases d <;> norm_num [h0, h1, h2, h3] <;> omega

end runLengthTransform_choose_add_five_mul_two_mul_add_two_mul

open runLengthTransform_choose_add_five_mul_two_mul_add_two_mul in
/-- **Sum of $\binom{n+5k}{2n+2k}\binom{n}{k} \bmod 2$ as a run length transform.** Let
$S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = S(1) = S(2) = S(3) = 1$ and
$S(m) = S(m - 1) + S(m - 2) - S(m - 3) + S(m - 4)$ for every $m \ge 4$. Then for every natural
number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+5k}{2n+2k}\binom{n}{k} \bmod 2\bigr)$ equals
the value at $n$ of the run length transform of $S$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 10. -/
public theorem runLengthTransform_choose_add_five_mul_two_mul_add_two_mul (S : ℕ → ℤ)
    (h0 : S 0 = 1) (h1 : S 1 = 1) (h2 : S 2 = 1)
    (h3 : S 3 = 1) (hrec : ∀ m, 4 ≤ m → S m = S (m - 1) + S (m - 2) - S (m - 3) + S (m - 4))
        (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 5 * k).choose (2 * n + 2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform S n := by
  have hs (c : ℕ) : S (c + 4) = S (c + 3) + S (c + 2) - S (c + 1) + S c := by
    simpa using hrec (c + 4) (by omega)
  have h := (matches_digits S h0 h1 h2 h3 hs (Nat.digits 2 n)
    (fun _ hd => Nat.digits_lt_base (by decide) hd)).1
  simpa only [Nat.ofDigits_digits, count, term, add_zero, Nat.cast_sum, runLengthTransform,
    binaryRunLengths, weight] using h

end MetaMathlibExt
