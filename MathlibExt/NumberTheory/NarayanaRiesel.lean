/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Riesel numbers in Narayana's cows sequence

The Narayana terms in 27 index classes modulo 718391520 are Riesel numbers.
-/

namespace MetaMathlibExt

namespace isRieselNumber_narayanaCowsSequence

open Matrix

private abbrev R := ZMod 11184810

private def step : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 0, 0, 1; 1, 0, 1]

private def state (n : ℕ) : Fin 3 → R :=
  ![narayanaCowsSequence n, narayanaCowsSequence (n + 1), narayanaCowsSequence (n + 2)]

private theorem state_eq (n : ℕ) : state n = (step ^ n) *ᵥ ![0, 1, 1] := by
  induction n with
  | zero => rw [pow_zero, one_mulVec]; rfl
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ← ih]
    funext i
    fin_cases i <;> simp [state, step, mulVec, dotProduct, Fin.sum_univ_succ,
      narayanaCowsSequence]
    ac_rfl

private theorem step_pow_eq (n : ℕ) : step ^ n = npowBinRec n step := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [pow_succ, npowBinRec_succ, ih]

private theorem step_period : step ^ 718391520 = 1 := by
  rw [step_pow_eq]
  decide +kernel

private theorem state_period (t : ℕ) : state t = state (t % 718391520) := by
  have hpow : step ^ t = step ^ (t % 718391520) := calc
    step ^ t = step ^ (t % 718391520 + 718391520 * (t / 718391520)) := by
      rw [Nat.mod_add_div]
    _ = step ^ (t % 718391520) := by rw [pow_add, pow_mul, step_period, one_pow, mul_one]
  rw [state_eq t, state_eq (t % 718391520), hpow]

private theorem riesel_of_modEq {k : ℕ} (hk : k ≡ 8086751 [MOD 11184810]) :
    IsRieselNumber k := by
  refine ⟨Nat.odd_iff.mpr (hk.of_dvd (by decide : 2 ∣ 11184810)), ?_⟩
  intro n _
  -- The six primes cover every exponent class modulo 24.
  have hcover : ∀ r : Fin 24, ∃ p ∈ [3, 5, 7, 13, 17, 241],
      2 ≤ p ∧ p ≤ 241 ∧ p ∣ 11184810 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧
      8086751 * 2 ^ (r : ℕ) ≡ 1 [MOD p] := by decide
  obtain ⟨p, _, hp, hp_le, hp_dvd, hp_period, hr⟩ :=
    hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hp_period.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hfactor : p ∣ k * 2 ^ n - 1 := (((hk.of_dvd hp_dvd).mul hpow).trans hr).symm.dvd'
  have hk_le : 8086751 ≤ k := calc
    8086751 = k % 11184810 := hk.symm
    _ ≤ k := Nat.mod_le _ _
  have hmul := Nat.le_mul_of_pos_right k (by positivity : 0 < 2 ^ n)
  exact Nat.not_prime_of_dvd_of_lt hfactor hp (by omega)

end isRieselNumber_narayanaCowsSequence

open isRieselNumber_narayanaCowsSequence in
/-- **Narayana numbers that are Riesel numbers.** Let $(N_t)$ be Narayana's cows sequence, with
$N_0 = 0$ and $N_1 = N_2 = 1$. If $t$ is congruent modulo $718391520$ to one of the $27$ residues
$3629412$, $13386852$, $73151172$, $96325092$, $101203812$, $119499012$, $175604292$,
$198778212$, $212194692$, $240247332$, $268299972$, $328064292$, $337821732$, $360995652$,
$384169572$, $402464772$, $425638692$, $467107812$, $476865252$, $495160452$, $564682212$,
$587856132$, $592734852$, $611030052$, $629325252$, $652499172$, $703725732$, then $N_t$ is a
Riesel number: $N_t$ is odd and $N_t \cdot 2^n - 1$ is not prime for every $n \ge 1$.

With this indexing, $N_t$ is odd exactly when $t \bmod 7 \in \{1, 2, 3, 5\}$.

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 2 (`integers-2024-A10-thm-2`). -/
public theorem isRieselNumber_narayanaCowsSequence {t : ℕ}
    (ht : t % 718391520 ∈ ({3629412, 13386852, 73151172, 96325092, 101203812, 119499012,
      175604292, 198778212, 212194692, 240247332, 268299972, 328064292, 337821732, 360995652,
      384169572, 402464772, 425638692, 467107812, 476865252, 495160452, 564682212, 587856132,
      592734852, 611030052, 629325252, 652499172, 703725732} : Finset ℕ)) :
    IsRieselNumber (narayanaCowsSequence t) := by
  apply riesel_of_modEq
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  change state t 0 = 8086751
  rw [state_period, state_eq, step_pow_eq]
  -- The same residue is obtained by repeated squaring at all 27 representative indices.
  generalize t % 718391520 = r at ht ⊢
  fin_cases ht <;> decide +kernel

end MetaMathlibExt
