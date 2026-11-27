/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.Digits

/-!
# p-adic expansions

Every `p`-adic integer has a unique `p`-adic expansion, and every sequence
of digits in `[0, p - 1]` is the expansion of a `p`-adic integer. The digits
are `PadicInt.padicDigit` from `MathlibExt/NumberTheory/Padics/Digits.lean`.
The bundled expansion map `PadicInt.padicExpansion : ℤ_[p] → ℕ → Fin p`
is bijective, as in ATLAS `NumberTheoryI` Proposition 8.17.
-/

@[expose] public section

set_option autoImplicit false

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **$p$-adic digits determine a $p$-adic integer.** Let $p$ be a prime. If two $p$-adic
integers $a, a' \in \mathbb{Z}_p$ have the same $n$-th $p$-adic digit for every $n \ge 0$, then
$a = a'$. -/
theorem eq_of_padicDigit_eq {a a' : ℤ_[p]}
    (h : ∀ n, padicDigit a n = padicDigit a' n) : a = a' := by
  suffices happr : ∀ n, a.appr n = a'.appr n by
    apply ext_of_toZModPow.mp
    intro n
    have h1 : toZModPow n a = ((a.appr n : ℕ) : ZMod (p ^ n)) := rfl
    have h2 : toZModPow n a' = ((a'.appr n : ℕ) : ZMod (p ^ n)) := rfl
    rw [h1, h2, happr n]
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [appr_succ_eq a n, appr_succ_eq a' n, ih, h n]

/-- **Existence of a $p$-adic integer with prescribed digits.** Let $p$ be a prime. For every
sequence $(b_n)_{n \ge 0}$ of natural numbers with $b_n < p$ for all $n$, there is a $p$-adic
integer $a \in \mathbb{Z}_p$ whose $n$-th $p$-adic digit is $b_n$ for every $n \ge 0$.

The witness is the $p$-adic limit of the partial sums $\sum_{k=0}^{n-1} b_k p^k$, which are its
approximations modulo $p^n$. -/
theorem exists_padicDigit_eq (b : ℕ → ℕ) (hb : ∀ n, b n < p) :
    ∃ a : ℤ_[p], ∀ n, padicDigit a n = b n := by
  have hp : 0 < p := (Nat.Prime.pos (Fact.out : p.Prime))
  -- Partial sums of the digit series, as integers.
  set S : ℕ → ℤ :=
    fun n => ∑ k ∈ Finset.range n, (b k : ℤ) * (p : ℤ) ^ k with hS
  have hsucc : ∀ n, S (n + 1) = S n + (b n : ℤ) * (p : ℤ) ^ n := by
    intro n
    rw [hS]
    simp [Finset.sum_range_succ]
  have hdvd : ∀ i, (p : ℤ) ^ i ∣ S (i + 1) - S i := by
    intro i
    rw [hsucc i, add_sub_cancel_left]
    exact ⟨(b i : ℤ), by rw [mul_comm]⟩
  -- The partial sums stay below `p ^ n`.
  have hsum_lt : ∀ n,
      ∑ k ∈ Finset.range n, b k * p ^ k < p ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hbn : b n ≤ p - 1 := by
        have hb_n := hb n
        omega
      have hle : b n * p ^ n ≤ p ^ n * (p - 1) := by
        calc b n * p ^ n ≤ (p - 1) * p ^ n :=
              mul_le_mul_of_nonneg_right hbn (Nat.zero_le _)
          _ = p ^ n * (p - 1) := mul_comm _ _
      have heq : p ^ n + p ^ n * (p - 1) = p ^ (n + 1) := by
        rw [pow_succ]
        have hpp : p ^ n * p = p ^ n * (1 + (p - 1)) := by
          congr 1
          omega
        rw [hpp, mul_add, mul_one]
      calc ∑ k ∈ Finset.range n, b k * p ^ k + b n * p ^ n
          < p ^ n + p ^ n * (p - 1) := add_lt_add_of_lt_of_le ih hle
        _ = p ^ (n + 1) := heq
  -- The witness, via `PadicInt.ofIntSeq`.
  set a := PadicInt.ofIntSeq S
    (isCauSeq_padicNorm_of_pow_dvd_sub S p hdvd) with ha
  refine ⟨a, fun n => ?_⟩
  -- Its approximations are the partial sums.
  have happ : ∀ n, a.appr n = ∑ k ∈ Finset.range n, b k * p ^ k := by
    intro n
    have hcast : (S n : ℤ) =
        ((∑ k ∈ Finset.range n, b k * p ^ k : ℕ) : ℤ) := by
      rw [hS, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => by push_cast; ring)
    have hTo : toZModPow n a =
        ((∑ k ∈ Finset.range n, b k * p ^ k : ℕ) : ZMod (p ^ n)) := by
      have h1 := toZModPow_ofIntSeq_of_pow_dvd_sub S p hdvd n
      rw [← ha] at h1
      rw [h1, hcast]
      simp
    have h2 : toZModPow n a = ((a.appr n : ℕ) : ZMod (p ^ n)) := rfl
    rw [h2] at hTo
    rw [ZMod.natCast_eq_natCast_iff'] at hTo
    rw [Nat.mod_eq_of_lt (appr_lt a n), Nat.mod_eq_of_lt (hsum_lt n)] at hTo
    exact hTo
  -- Reading off the `n`-th digit from consecutive approximations.
  have hsucc : (∑ k ∈ Finset.range (n + 1), b k * p ^ k)
      = (∑ k ∈ Finset.range n, b k * p ^ k) + b n * p ^ n :=
    Finset.sum_range_succ _ _
  show (a.appr (n + 1) - a.appr n) / p ^ n = b n
  rw [happ (n + 1), happ n, hsucc]
  have hdiff : (∑ k ∈ Finset.range n, b k * p ^ k) + b n * p ^ n -
      (∑ k ∈ Finset.range n, b k * p ^ k) = b n * p ^ n := by omega
  rw [hdiff, mul_comm (b n) (p ^ n)]
  exact Nat.mul_div_cancel_left _ (pow_pos hp n)

/-- **Existence and uniqueness of $p$-adic integers with prescribed digits.** Let $p$ be a prime.
For every sequence $(b_n)_{n \ge 0}$ of natural numbers with $b_n < p$ for all $n$, there is
exactly one $p$-adic integer $a \in \mathbb{Z}_p$ whose $n$-th $p$-adic digit is $b_n$ for every
$n \ge 0$.

Source: ATLAS `NumberTheoryI`, Proposition 8.17. -/
theorem existsUnique_padicDigit_eq (b : ℕ → ℕ) (hb : ∀ n, b n < p) :
    ∃! a : ℤ_[p], ∀ n, padicDigit a n = b n := by
  obtain ⟨a, ha⟩ := exists_padicDigit_eq b hb
  exact ⟨a, ha, fun a' ha' =>
    eq_of_padicDigit_eq (fun n => (ha' n).trans (ha n).symm)⟩

/-- **The $p$-adic expansion map is injective.** Let $p$ be a prime. If two $p$-adic integers
$a, a' \in \mathbb{Z}_p$ have the same $p$-adic expansion, then $a = a'$. -/
theorem padicExpansion_injective :
    Function.Injective (padicExpansion (p := p)) := by
  intro a a' h
  apply eq_of_padicDigit_eq
  intro n
  simpa only [padicExpansion_val] using
    congrArg (fun f : ℕ → Fin p => (f n).val) h

/-- **The $p$-adic expansion map is surjective.** Let $p$ be a prime. Every sequence
$(b_n)_{n \ge 0}$ with values in $\{0, 1, \dots, p - 1\}$ is the $p$-adic expansion of some
$p$-adic integer $a \in \mathbb{Z}_p$. -/
theorem padicExpansion_surjective :
    Function.Surjective (padicExpansion (p := p)) := by
  intro b
  obtain ⟨a, ha⟩ := exists_padicDigit_eq (fun n => (b n).val)
    (fun n => (b n).isLt)
  exact ⟨a, funext fun n => Fin.ext (ha n)⟩

/-- **The $p$-adic expansion map is bijective.** Let $p$ be a prime. The map sending a $p$-adic
integer $a \in \mathbb{Z}_p$ to its $p$-adic expansion is a bijection from $\mathbb{Z}_p$ onto
the set of all sequences $(b_n)_{n \ge 0}$ with values in $\{0, 1, \dots, p - 1\}$.

Source: ATLAS `NumberTheoryI`, Proposition 8.17. -/
theorem padicExpansion_bijective :
    Function.Bijective (padicExpansion (p := p)) :=
  ⟨padicExpansion_injective, padicExpansion_surjective⟩

end PadicInt
