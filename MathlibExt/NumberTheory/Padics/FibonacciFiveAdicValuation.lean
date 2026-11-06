/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
5-adic valuation of Fibonacci numbers (Lengyel, via Fatehizadeh–Yaqubi Lemma `Leg1`):
Amirali Fatehizadeh and Daniel Yaqubi, “Average of the Fibonacci Numbers,”
Journal of Integer Sequences 25 (2022), Lemma `Leg1`, which cites T. Lengyel,
“The order of Fibonacci and Lucas numbers,” Fibonacci Quarterly 33 (1995), 234–239.
URL: `https://cs.uwaterloo.ca/journals/JIS/VOL25/Yaqubi/yaq6.tex`,
full TeX SHA-256:
`460e70d342c78a6138fb5662d3463e293a93f52e776e0bef4489d30066b10f79`,
exact source-span SHA-256:
`5288719f067ff9fd73a43a94ec267e1c3a1f38063485b97f1a92b6b76b14c95f`.
Archive concept/task:
`jis_grounded_a056c7c9f8cca3c414818070` /
`jis_grounded_a056c7c9f8cca3c414818070__lengyel_fibonacci_five_adic`.
-/

namespace MetaMathlibExt

@[expose] public section

private lemma five_dvd_fib_iff (n : ℕ) : 5 ∣ Nat.fib n ↔ 5 ∣ n := by
  have h5 : Nat.fib 5 = 5 := by decide
  have hgcd := Nat.fib_gcd n 5
  rw [h5] at hgcd
  constructor
  · intro h
    have hgn : (Nat.fib n).gcd 5 = 5 := Nat.gcd_eq_right h
    rw [hgn] at hgcd
    have hdvd : n.gcd 5 ∣ 5 := Nat.gcd_dvd_right n 5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
    · rw [h1] at hgcd
      simp at hgcd
    · exact h1 ▸ Nat.gcd_dvd_left n 5
  · intro h
    have h2 : Nat.fib 5 ∣ Nat.fib n := Nat.fib_dvd 5 n h
    rwa [h5] at h2

private lemma fib_mod5_pair :
    ∀ m, Nat.fib (m + 20) % 5 = Nat.fib m % 5 ∧
      Nat.fib (m + 21) % 5 = Nat.fib (m + 1) % 5 := by
  intro m
  induction m with
  | zero => constructor <;> decide
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e0 : k + 1 + 20 = k + 21 := by ring
    have e1 : k + 20 + 2 = k + 1 + 21 := by ring
    have e2 : k + 2 = k + 1 + 1 := by ring
    have f1 : Nat.fib (k + 1 + 21) = Nat.fib (k + 20) + Nat.fib (k + 21) := by
      have h := Nat.fib_add_two (n := k + 20)
      rwa [e1] at h
    have f2 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := by
      have h := Nat.fib_add_two (n := k)
      rwa [e2] at h
    refine ⟨by rw [e0]; exact ih2, ?_⟩
    rw [f1, f2]
    exact Nat.ModEq.add ih1 ih2

private lemma fib_mod5_period (k : ℕ) : Nat.fib (k + 20) ≡ Nat.fib k [MOD 5] :=
  (fib_mod5_pair k).1

private lemma fib_mod5_equiv (m : ℕ) :
    Nat.fib m ≡ Nat.fib (m % 20) [MOD 5] ∧
      Nat.fib (m + 1) ≡ Nat.fib (m % 20 + 1) [MOD 5] := by
  have hqm : 20 * (m / 20) + m % 20 = m := Nat.div_add_mod m 20
  have key : ∀ q r, Nat.fib (20 * q + r) ≡ Nat.fib r [MOD 5] := by
    intro q
    induction q with
    | zero =>
      intro r
      have hr : 20 * 0 + r = r := by ring
      rw [hr]
    | succ q ih =>
      intro r
      have h : 20 * (q + 1) + r = (20 * q + r) + 20 := by ring
      rw [h]
      exact (fib_mod5_period _).trans (ih r)
  constructor
  · conv_lhs => rw [← hqm]
    exact key (m / 20) (m % 20)
  · have h1 : m + 1 = 20 * (m / 20) + (m % 20 + 1) := by omega
    conv_lhs => rw [h1]
    exact key (m / 20) (m % 20 + 1)

private lemma R_residue5 (r : ℕ) (hr : r < 20) :
    ((Nat.fib (r + 1) : ℕ) : ZMod 5) ^ 4
      - 2 * ((Nat.fib r : ℕ) : ZMod 5) * ((Nat.fib (r + 1) : ℕ) : ZMod 5) ^ 3
      + 4 * ((Nat.fib r : ℕ) : ZMod 5) ^ 2 * ((Nat.fib (r + 1) : ℕ) : ZMod 5) ^ 2
      - 3 * ((Nat.fib r : ℕ) : ZMod 5) ^ 3 * ((Nat.fib (r + 1) : ℕ) : ZMod 5)
      + ((Nat.fib r : ℕ) : ZMod 5) ^ 4 = 1 := by
  interval_cases r <;> decide

private lemma fib_five_mul_int (m : ℕ) :
    ((Nat.fib (5 * m) : ℕ) : ℤ) = ((Nat.fib m : ℕ) : ℤ) *
      (5 * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 4
        - 10 * ((Nat.fib m : ℕ) : ℤ) * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 3
        + 20 * ((Nat.fib m : ℕ) : ℤ) ^ 2 * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 2
        - 15 * ((Nat.fib m : ℕ) : ℤ) ^ 3 * ((Nat.fib (m + 1) : ℕ) : ℤ)
        + 5 * ((Nat.fib m : ℕ) : ℤ) ^ 4) := by
  have hle1 : Nat.fib m ≤ 2 * Nat.fib (m + 1) := by
    have h := Nat.fib_le_fib_succ (n := m)
    omega
  have hle2 : Nat.fib (2 * m) ≤ 2 * Nat.fib (2 * m + 1) := by
    have h := Nat.fib_le_fib_succ (n := 2 * m)
    omega
  have h1 : ((Nat.fib (2 * m) : ℕ) : ℤ)
      = 2 * ((Nat.fib m : ℕ) : ℤ) * ((Nat.fib (m + 1) : ℕ) : ℤ)
        - ((Nat.fib m : ℕ) : ℤ) ^ 2 := by
    have h := Nat.fib_two_mul m
    zify [hle1] at h
    linear_combination h
  have h2 : ((Nat.fib (2 * m + 1) : ℕ) : ℤ)
      = ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 2 + ((Nat.fib m : ℕ) : ℤ) ^ 2 := by
    have h := Nat.fib_two_mul_add_one m
    exact_mod_cast h
  have e3 : ((Nat.fib (4 * m) : ℕ) : ℤ)
      = 2 * ((Nat.fib (2 * m) : ℕ) : ℤ) * ((Nat.fib (2 * m + 1) : ℕ) : ℤ)
        - ((Nat.fib (2 * m) : ℕ) : ℤ) ^ 2 := by
    have h := Nat.fib_two_mul (2 * m)
    zify [hle2] at h
    rw [show 2 * (2 * m) = 4 * m from by ring] at h
    linear_combination h
  have e4 : ((Nat.fib (4 * m + 1) : ℕ) : ℤ)
      = ((Nat.fib (2 * m + 1) : ℕ) : ℤ) ^ 2 + ((Nat.fib (2 * m) : ℕ) : ℤ) ^ 2 := by
    have h := Nat.fib_two_mul_add_one (2 * m)
    have hc : ((Nat.fib (2 * (2 * m) + 1) : ℕ) : ℤ)
        = ((Nat.fib (2 * m + 1) : ℕ) : ℤ) ^ 2 + ((Nat.fib (2 * m) : ℕ) : ℤ) ^ 2 := by
      exact_mod_cast h
    rw [show 2 * (2 * m) + 1 = 4 * m + 1 from by ring] at hc
    linear_combination hc
  have em2 : ((Nat.fib (m + 2) : ℕ) : ℤ)
      = ((Nat.fib m : ℕ) : ℤ) + ((Nat.fib (m + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.fib_add_two (n := m)
  have e5 : ((Nat.fib (5 * m + 1) : ℕ) : ℤ)
      = ((Nat.fib (4 * m) : ℕ) : ℤ) * ((Nat.fib m : ℕ) : ℤ)
        + ((Nat.fib (4 * m + 1) : ℕ) : ℤ) * ((Nat.fib (m + 1) : ℕ) : ℤ) := by
    have h := Nat.fib_add (4 * m) m
    rw [show 4 * m + m + 1 = 5 * m + 1 from by ring] at h
    exact_mod_cast h
  have e6 : ((Nat.fib (5 * m + 2) : ℕ) : ℤ)
      = ((Nat.fib (4 * m) : ℕ) : ℤ) * ((Nat.fib (m + 1) : ℕ) : ℤ)
        + ((Nat.fib (4 * m + 1) : ℕ) : ℤ) * ((Nat.fib (m + 2) : ℕ) : ℤ) := by
    have h := Nat.fib_add (4 * m) (m + 1)
    rw [show 4 * m + (m + 1) + 1 = 5 * m + 2 from by ring,
      show (m + 1) + 1 = m + 2 from by ring] at h
    exact_mod_cast h
  have e7 : ((Nat.fib (5 * m) : ℕ) : ℤ)
      = ((Nat.fib (5 * m + 2) : ℕ) : ℤ) - ((Nat.fib (5 * m + 1) : ℕ) : ℤ) := by
    have h : ((Nat.fib (5 * m + 2) : ℕ) : ℤ)
        = ((Nat.fib (5 * m) : ℕ) : ℤ) + ((Nat.fib (5 * m + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.fib_add_two (n := 5 * m)
    linarith
  rw [e7, e6, e5, em2, e4, e3, h1, h2]
  ring

private lemma fib_five_mul_nat (m : ℕ) (hm : 1 ≤ m) :
    ∃ R : ℕ, Nat.fib (5 * m) = Nat.fib m * (5 * R) ∧ ¬ 5 ∣ R := by
  have hInt := fib_five_mul_int m
  set Rint : ℤ := ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 4
      - 2 * ((Nat.fib m : ℕ) : ℤ) * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 3
      + 4 * ((Nat.fib m : ℕ) : ℤ) ^ 2 * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 2
      - 3 * ((Nat.fib m : ℕ) : ℤ) ^ 3 * ((Nat.fib (m + 1) : ℕ) : ℤ)
      + ((Nat.fib m : ℕ) : ℤ) ^ 4 with hR
  have hQ : 5 * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 4
        - 10 * ((Nat.fib m : ℕ) : ℤ) * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 3
        + 20 * ((Nat.fib m : ℕ) : ℤ) ^ 2 * ((Nat.fib (m + 1) : ℕ) : ℤ) ^ 2
        - 15 * ((Nat.fib m : ℕ) : ℤ) ^ 3 * ((Nat.fib (m + 1) : ℕ) : ℤ)
        + 5 * ((Nat.fib m : ℕ) : ℤ) ^ 4 = 5 * Rint := by
    rw [hR]; ring
  have hInt2 : ((Nat.fib (5 * m) : ℕ) : ℤ)
      = ((Nat.fib m : ℕ) : ℤ) * (5 * Rint) := by
    rw [← hQ]; exact hInt
  have hF5pos : (0 : ℤ) < ((Nat.fib (5 * m) : ℕ) : ℤ) := by
    have h : 0 < Nat.fib (5 * m) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast h
  have hApos : (0 : ℤ) < ((Nat.fib m : ℕ) : ℤ) := by
    have h : 0 < Nat.fib m := Nat.fib_pos.mpr (by omega)
    exact_mod_cast h
  have hpos : (0 : ℤ) < ((Nat.fib m : ℕ) : ℤ) * (5 * Rint) := hInt2 ▸ hF5pos
  have h5Rpos : (0 : ℤ) < 5 * Rint := by
    by_contra hc
    have hc' : 5 * Rint ≤ 0 := le_of_not_gt hc
    have hle : ((Nat.fib m : ℕ) : ℤ) * (5 * Rint) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hApos.le hc'
    linarith
  have hRpos : (0 : ℤ) < Rint := by linarith
  set Rnat : ℕ := Rint.toNat with hRnat_def
  have hRnat : ((Rnat : ℕ) : ℤ) = Rint := by
    rw [hRnat_def]
    exact Int.toNat_of_nonneg hRpos.le
  have hNat : Nat.fib (5 * m) = Nat.fib m * (5 * Rnat) := by
    have h2 : ((Nat.fib (5 * m) : ℕ) : ℤ)
        = ((Nat.fib m * (5 * Rnat) : ℕ) : ℤ) := by
      push_cast
      rw [hRnat]
      exact hInt2
    exact_mod_cast h2
  have hAR : ((Nat.fib m : ℕ) : ZMod 5) = ((Nat.fib (m % 20) : ℕ) : ZMod 5) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact (fib_mod5_equiv m).1
  have hBR : ((Nat.fib (m + 1) : ℕ) : ZMod 5)
      = ((Nat.fib (m % 20 + 1) : ℕ) : ZMod 5) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact (fib_mod5_equiv m).2
  have hR1 : ((Rint : ℤ) : ZMod 5) = 1 := by
    rw [hR]
    push_cast
    rw [hAR, hBR]
    exact R_residue5 (m % 20) (by omega)
  have hR5 : ¬ 5 ∣ Rnat := by
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hcast : ((Rnat : ℕ) : ZMod 5) = ((Rint : ℤ) : ZMod 5) := by
      rw [← hRnat]
      exact (Int.cast_natCast Rnat).symm
    have h1 : ((Rnat : ℕ) : ZMod 5) = 1 := hcast.trans hR1
    rw [hk] at h1
    have h2 : ((5 * k : ℕ) : ZMod 5) = 0 := by
      have h5 : ((5 : ℕ) : ZMod 5) = 0 := by decide
      simp only [Nat.cast_mul, h5, zero_mul]
    rw [h2] at h1
    exact (by decide : (0 : ZMod 5) ≠ 1) h1
  exact ⟨Rnat, hNat, hR5⟩

private lemma padicVal_fib_five (m : ℕ) (hm : 1 ≤ m) :
    padicValNat 5 (Nat.fib (5 * m)) = padicValNat 5 (Nat.fib m) + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨R, hR_eq, hR5⟩ := fib_five_mul_nat m hm
  have hFm : Nat.fib m ≠ 0 := by
    have h : 0 < Nat.fib m := Nat.fib_pos.mpr (by omega)
    omega
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hR5 (dvd_zero 5)
  have h5R : 5 * R ≠ 0 := mul_ne_zero (by norm_num) hR0
  have h1 : padicValNat 5 (5 * R) = 1 := by
    rw [padicValNat.mul (by norm_num) hR0, padicValNat_self,
      padicValNat.eq_zero_of_not_dvd hR5, add_zero]
  rw [hR_eq, padicValNat.mul hFm h5R, h1]

/-- **The $5$-adic valuation of Fibonacci numbers.** Writing $F_n$ for the $n$-th Fibonacci number
and $v_5$ for the $5$-adic valuation, $v_5(F_n) = v_5(n)$ for every integer $n \ge 1$.

Proves `Wanted` entry `lengyel_fibonacci_five_adic`.

Source: Fatehizadeh–Yaqubi, Lemma `Leg1`, citing Lengyel (1995).
The source prints `n ≥ 0`, but its p-adic valuation is defined for positive
integers, so this formalizes the audited `1 ≤ n` restriction. Only the 5-adic
clause is formalized; the source's separate 2-adic and 3-adic clauses are out
of scope.
-/
theorem lengyel_fibonacci_five_adic
    (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 5 (Nat.fib n) = padicValNat 5 n := by
  revert hn
  refine Nat.strong_induction_on n (fun n ih hn => ?_)
  by_cases h5 : 5 ∣ n
  · obtain ⟨m, rfl⟩ := h5
    have hm : 1 ≤ m := by omega
    have hmlt : m < 5 * m := by omega
    rw [padicVal_fib_five m hm, ih m hmlt hm,
      padicValNat_base_mul (show (1 : ℕ) < 5 by norm_num) (show m ≠ 0 by omega)]
  · have hfib : ¬ 5 ∣ Nat.fib n := mt (five_dvd_fib_iff n).mp h5
    rw [padicValNat.eq_zero_of_not_dvd hfib, padicValNat.eq_zero_of_not_dvd h5]

end

end MetaMathlibExt
