/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.RatResidue
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Dvd

/-!
# A truncated sum of Bernoulli numbers modulo a prime

For every prime $p ≥ 5$, the sum of the Bernoulli numbers through $B_{p-3}$ has
denominator prime to $p$ and residue $-1$ modulo $p$. The proof reduces the binomial
recurrence for `bernoulli'` at $p-1$. Its binomial coefficients reduce to $(-1)^j$,
which converts each summand to `bernoulli j`. The last term $B_{p-2}$ vanishes.
-/

namespace MetaMathlibExt

open Finset

namespace sum_bernoulli_to_prime_sub_three_mod_prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every denominator in the recurrence for the positive-sign Bernoulli numbers is a unit
modulo `p` when the index is below `p - 1`. -/
private lemma integral_bernoulli' (n : ℕ) (hn : n + 1 < p) :
    Rat.padicValuation p (bernoulli' n) ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [bernoulli'_def]
    refine (Rat.padicValuation p).map_sub_le (by simp) ((Rat.padicValuation p).map_sum_le ?_)
    intro j hj
    have hjn := mem_range.mp hj
    have hunit : Int.padicValuation p (↑(n - j + 1) : ℤ) = 1 := by
      rw [Int.padicValuation_eq_one_iff, Int.natCast_dvd_natCast]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [← Nat.cast_sub hjn.le, ← Nat.cast_add_one, map_mul, map_div₀,
      Rat.padicValuation_natCast, Rat.padicValuation_natCast, hunit, div_one]
    exact mul_le_one' (Int.padicValuation_le_one _ _) (ih j hjn (by omega))

/-- Pascal's identity makes successive entries in row `p - 1` negatives modulo `p`. -/
private lemma choose_mod_prime (j : ℕ) (hj : j < p) :
    ((p - 1).choose j : ZMod p) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hzero := (ZMod.natCast_eq_zero_iff _ p).2 (hp.out.dvd_choose_self (by omega) hj)
    have hpascal := Nat.choose_succ_succ (p - 1) j
    rw [show (p - 1).succ = p by omega] at hpascal
    rw [hpascal, Nat.cast_add, ih (by omega)] at hzero
    rw [pow_succ, mul_neg_one]
    exact eq_neg_of_add_eq_zero_right hzero

/-- Reduction of an integer-weighted sum of `bernoulli' j` below the first possible
multiple of `p` in a denominator. -/
private lemma reduce_weighted_sum (a : ℕ → ℤ) (n : ℕ) (hn : n < p) :
    Rat.padicValuation p (∑ j ∈ range n, (a j : ℚ) * bernoulli' j) ≤ 1 ∧
      ((∑ j ∈ range n, (a j : ℚ) * bernoulli' j : ℚ) : ZMod p) =
        ∑ j ∈ range n, (a j : ZMod p) * (bernoulli' j : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hs, hcast⟩ := ih (by omega)
    have hB := integral_bernoulli' n hn
    have hterm : Rat.padicValuation p ((a n : ℚ) * bernoulli' n) ≤ 1 := by
      rw [map_mul, Rat.padicValuation_cast]
      exact mul_le_one' (Int.padicValuation_le_one _ _) hB
    have den_ne {x : ℚ} (hx : Rat.padicValuation p x ≤ 1) : (x.den : ZMod p) ≠ 0 :=
      mt (ZMod.natCast_eq_zero_iff _ _).mp (Rat.padicValuation_le_one_iff.mp hx)
    rw [sum_range_succ, sum_range_succ]
    refine ⟨(Rat.padicValuation p).map_add_le hs hterm, ?_⟩
    rw [Rat.cast_add_of_ne_zero (den_ne hs) (den_ne hterm), hcast,
      Rat.cast_mul_of_ne_zero (by simp) (den_ne hB), Rat.cast_intCast]

end sum_bernoulli_to_prime_sub_three_mod_prime

open sum_bernoulli_to_prime_sub_three_mod_prime

/--
**The congruence $\sum_{j=0}^{p-3} B_j \equiv -1 \pmod p$.** Let $B_j$ denote the Bernoulli
numbers with $B_1 = -\tfrac12$. For every prime $p \ge 5$, the rational number
$S = B_0 + B_1 + \dots + B_{p-3}$ has denominator not divisible by $p$, and its residue modulo
$p$ (its numerator times the inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $-1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (24).
-/
public theorem sum_bernoulli_to_prime_sub_three_mod_prime (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬p ∣ (∑ j ∈ Finset.range (p - 2), bernoulli j).den ∧
      ratResidue p (∑ j ∈ Finset.range (p - 2), bernoulli j) =
        ratResidue p (-1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hlt : p - 1 < p := by omega
  have hsum := reduce_weighted_sum (p := p) (fun j => (-1 : ℤ) ^ j) (p - 1) hlt
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ← bernoulli.eq_def] at hsum
  have hrec := (reduce_weighted_sum (p := p) (fun j => ((p - 1).choose j : ℤ))
    (p - 1) hlt).2
  simp only [Int.cast_natCast, sum_bernoulli', Rat.cast_natCast] at hrec
  rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub] at hrec
  have hodd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨k - 1, by omega⟩
  have htrunc : ∑ j ∈ range (p - 1), bernoulli j = ∑ j ∈ range (p - 2), bernoulli j := by
    rw [show p - 1 = (p - 2) + 1 by omega, sum_range_succ,
      bernoulli_eq_zero_of_odd hodd (by omega), add_zero]
  rw [htrunc] at hsum
  refine ⟨Rat.padicValuation_le_one_iff.mp hsum.1, ?_⟩
  have hres (x : ℚ) : ratResidue p x = (x : ZMod p) := by
    rw [Rat.cast_def, div_eq_mul_inv]
    rfl
  rw [hres, hres, Rat.cast_neg, Rat.cast_one, hsum.2]
  refine Eq.trans ?_ hrec.symm
  exact sum_congr rfl fun j hj => by rw [choose_mod_prime j ((mem_range.mp hj).trans hlt)]

end MetaMathlibExt
