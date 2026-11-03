/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.MotzkinCentralTrinomial
public import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-! # Motzkin numbers

The Motzkin numbers (OEIS A001006) as the Catalan-weighted binomial sum
`M(n) = ∑_{k=0}^{n} C(n,2k) C(k)`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2).

`motzkinNumber_succ` proves the Motzkin recurrence
`M(n + 1) = M(n) + ∑_{k < n} M(k) M(n - 1 - k)` (Donaghey and Shapiro 1977) from this sum, via
the convolution identity `∑_{a + b = n} M(a) M(b) = ∑_k C(n + 1, 2k + 1) C(k + 1)`.
-/

/-- The Motzkin numbers (OEIS A001006) `M(n) = ∑_{k=0}^{n} C(n,2k) C(k)`, with `C(k)` the
Catalan numbers (OEIS A000108). Terms with `2k > n` vanish.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
def motzkinNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose (2 * k) * catalan k

/-- `M(0) = 1`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_zero : motzkinNumber 0 = 1 := by
  simp [motzkinNumber]

/-- `M(1) = 1`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_one : motzkinNumber 1 = 1 := by
  simp [motzkinNumber, Finset.sum_range_succ]

/-- `M(2) = 2`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_two : motzkinNumber 2 = 2 := by
  simp [motzkinNumber, Finset.sum_range_succ, catalan_one,
    Nat.choose_eq_zero_of_lt (by norm_num : 2 < 4)]

/-- The defining sum may stop at `k = ⌊n/2⌋`, since `C(n,2k) = 0` for `2k > n`.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 19 (2). -/
theorem motzkinNumber_eq_sum_range_half (n : ℕ) :
    motzkinNumber n = ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k := by
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    simp only [Finset.mem_range] at hk hnot
    rw [Nat.choose_eq_zero_of_lt (by omega : n < 2 * k), Nat.zero_mul]

/-- The central trinomial coefficients satisfy `T(n+1) = T(n) + 2n M(n-1)` for `n ≥ 1`
(`MetaMathlibExt.motzkin_central_trinomial_recurrence` specialized to `motzkinNumber`).

Source: P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky, *Motzkin Numbers,
Central Trinomial Coefficients and Hybrid Polynomials*, Journal of Integer Sequences 11 (2008),
Article 08.1.1, equation (34). -/
theorem trinomialCoefficient_succ_eq_add_motzkinNumber (n : ℕ) (hn : 1 ≤ n) :
    trinomialCoefficient (n + 1) (n + 1) =
      trinomialCoefficient n n + 2 * n * motzkinNumber (n - 1) :=
  motzkin_central_trinomial_recurrence motzkinNumber motzkinNumber_eq_sum_range_half n hn

/-! ### The Motzkin recurrence -/

section Recurrence

open Finset

private theorem choose_sum (n q : ℕ) :
    (∑ a ∈ range (n + 1), a.choose q) = (n + 1).choose (q + 1) := by
  induction n with
  | zero =>
    cases q with
    | zero => simp
    | succ q => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < q + 1 + 1)]
  | succ n ih =>
    rw [sum_range_succ, ih]
    cases q with
    | zero => simp
    | succ q =>
      rw [Nat.choose_succ_succ (n + 1) (q + 1)]
      exact Nat.add_comm _ _

private theorem choose_convolution (n p q : ℕ) :
    (∑ ab ∈ antidiagonal n, ab.1.choose p * ab.2.choose q) =
      (n + 1).choose (p + q + 1) := by
  induction n generalizing p q with
  | zero =>
    cases p <;> cases q <;> simp [Nat.choose_succ_succ, Nat.choose_zero_succ, ← Nat.add_assoc]
  | succ n ih =>
    cases p with
    | zero =>
      simp only [Nat.choose_zero_right, one_mul, zero_add]
      rw [← Nat.sum_antidiagonal_swap]
      simp only [Prod.snd_swap]
      rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => a.choose q)]
      exact choose_sum (n + 1) q
    | succ p =>
      rw [Nat.sum_antidiagonal_succ]
      simp only [Nat.choose_zero_succ, zero_mul, zero_add]
      conv_lhs => simp only [Nat.choose_succ_succ, add_mul]
      rw [sum_add_distrib, ih, ih]
      simpa only [Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using
        (Nat.choose_succ_succ (n + 1) (p + q + 1)).symm

private theorem motzkinNumber_eq_sum (n r : ℕ) (h : n < r) :
    motzkinNumber n = ∑ k ∈ range r, n.choose (2 * k) * catalan k := by
  unfold motzkinNumber
  apply sum_subset (range_mono (by omega))
  intro k hk hkn
  rw [Nat.choose_eq_zero_of_lt, zero_mul]
  simp only [mem_range] at hk hkn
  omega

private theorem sum_diagonals (r : ℕ) (f : ℕ → ℕ → ℕ)
    (h : ∀ i j, r ≤ i + j → f i j = 0) :
    (∑ i ∈ range r, ∑ j ∈ range r, f i j) =
      ∑ k ∈ range r, ∑ ij ∈ antidiagonal k, f ij.1 ij.2 := by
  rw [← sum_product' (range r) (range r) f]
  have hf : ∀ k ∈ range r,
      ((range r ×ˢ range r).filter (fun ij => ij.1 + ij.2 = k)) = antidiagonal k := by
    intro k hk
    ext ij
    simp only [mem_filter, mem_product, mem_range, mem_antidiagonal] at *
    omega
  calc
    _ = ∑ ij ∈ (range r ×ˢ range r).filter (fun ij => ij.1 + ij.2 ∈ range r),
        f ij.1 ij.2 := by
      symm
      apply sum_subset (filter_subset _ _)
      intro ij hij hn
      apply h
      simp only [mem_filter, hij, true_and, mem_range] at hn
      omega
    _ = ∑ k ∈ range r,
        ∑ ij ∈ (range r ×ˢ range r).filter (fun ij => ij.1 + ij.2 = k),
          f ij.1 ij.2 := (sum_fiberwise_eq_sum_filter _ _ _ _).symm
    _ = _ := sum_congr rfl fun k hk => by rw [hf k hk]

private theorem motzkinNumber_convolution (n : ℕ) :
    (∑ ab ∈ antidiagonal n, motzkinNumber ab.1 * motzkinNumber ab.2) =
      ∑ k ∈ range (n + 1), (n + 1).choose (2 * k + 1) * catalan (k + 1) := by
  calc
    _ = ∑ ab ∈ antidiagonal n, ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
        (ab.1.choose (2 * i) * ab.2.choose (2 * j)) * (catalan i * catalan j) := by
      apply sum_congr rfl
      intro ab hab
      have hab' := mem_antidiagonal.mp hab
      rw [motzkinNumber_eq_sum ab.1 (n + 1) (by omega),
        motzkinNumber_eq_sum ab.2 (n + 1) (by omega), sum_mul_sum]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ac_rfl
    _ = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ∑ ab ∈ antidiagonal n,
        (ab.1.choose (2 * i) * ab.2.choose (2 * j)) * (catalan i * catalan j) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
        (n + 1).choose (2 * i + 2 * j + 1) * (catalan i * catalan j) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [← sum_mul, choose_convolution]
    _ = ∑ k ∈ range (n + 1), ∑ ij ∈ antidiagonal k,
        (n + 1).choose (2 * ij.1 + 2 * ij.2 + 1) *
          (catalan ij.1 * catalan ij.2) := by
      apply sum_diagonals
      intro i j hij
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [catalan_succ', mul_sum]
      apply sum_congr rfl
      intro ij hij
      have hij' := mem_antidiagonal.mp hij
      rw [show 2 * ij.1 + 2 * ij.2 + 1 = 2 * k + 1 by omega]

private theorem motzkinNumber_pascal (n : ℕ) :
    motzkinNumber (n + 1) = motzkinNumber n +
      ∑ k ∈ range (n + 1), n.choose (2 * k + 1) * catalan (k + 1) := by
  have hp (k : ℕ) : (n + 1).choose (2 * (k + 1)) =
      n.choose (2 * (k + 1)) + n.choose (2 * k + 1) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.choose_succ_succ']
    exact add_comm _ _
  rw [motzkinNumber_eq_sum (n + 1) (n + 2) (by omega),
    motzkinNumber_eq_sum n (n + 2) (by omega)]
  rw [sum_range_succ' (fun k => (n + 1).choose (2 * k) * catalan k) (n + 1),
    sum_range_succ' (fun k => n.choose (2 * k) * catalan k) (n + 1)]
  simp only [mul_zero, Nat.choose_zero_right, catalan_zero, mul_one]
  simp_rw [hp, add_mul]
  rw [sum_add_distrib]
  omega

/-- **The Motzkin recurrence**: `M(n + 1) = M(n) + ∑_{k < n} M(k) M(n - 1 - k)`, proved here
from the Catalan-weighted sum defining `motzkinNumber`. (Combinatorially, a Motzkin path of
length `n + 1` starts with a flat step, or with an up step whose matching down step splits the
rest into two shorter Motzkin paths; that path model is not formalized here.)

Source: R. Donaghey and L. W. Shapiro, *Motzkin numbers*, Journal of Combinatorial Theory,
Series A 23 (1977), 291–301. -/
theorem motzkinNumber_succ (n : ℕ) :
    motzkinNumber (n + 1) = motzkinNumber n +
      ∑ k : Fin n, motzkinNumber k.val * motzkinNumber (n - 1 - k.val) := by
  cases n with
  | zero =>
    simp [motzkinNumber, sum_range_succ]
  | succ n =>
    rw [motzkinNumber_pascal, sum_range_succ]
    rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < 2 * (n + 1) + 1), zero_mul,
      add_zero, ← motzkinNumber_convolution]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => motzkinNumber a * motzkinNumber b),
      sum_range]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]

end Recurrence

end

end MetaMathlibExt
