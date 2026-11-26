/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Logic.Function.Iterate
public import MathlibExt.NumberTheory.Digits.NegativeBaseDigitSquareCongruence
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Happy numbers in base `-2`

This module defines `IsNegBaseHappy` and proves `isNegBaseHappy_neg_two_iff`: there is an
integer `n` such that `n + 3 * i` is `(-2)`-happy for every natural number `i`, and an integer
`a` is `(-2)`-happy if and only if `a ≡ 1 [ZMOD 3]`.

Statements from Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The
Fibonacci Quarterly 62 (2024), no. 2, 125–129.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Happy integers in a negative base.** Let $b$ be an integer and let $S_{2,b}$ be the
base-$b$ digit-square sum, which for $b \le -2$ sends an integer to the sum of the squares of its
base-$b$ digits. An integer $a$ is $b$-happy if $S_{2,b}^k(a) = 1$ for some $k \ge 1$, where
$S_{2,b}^k$ denotes the $k$-th iterate of $S_{2,b}$.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def IsNegBaseHappy (b a : ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum b)^[k] a = 1

end

private def digitRank (a : ℤ) : ℕ := 2 * a.natAbs + if a < 0 then 1 else 0

private theorem digitRank_lt {B q d : ℤ} (hB : 2 ≤ B) (hd0 : 0 ≤ d) (hd : d < B)
    (ha : -B * q + d ≠ 0) : digitRank q < digitRank (-B * q + d) := by
  set a := -B * q + d with ea
  have haq : (a.natAbs : ℤ) = |a| := Int.natCast_natAbs a
  have hqq : (q.natAbs : ℤ) = |q| := Int.natCast_natAbs q
  by_cases hq : q < 0
  · have hmul := mul_le_mul_of_nonneg_right hB (show 0 ≤ -q by omega)
    have h : -q < a := by nlinarith
    rw [abs_of_neg hq] at hqq
    rw [abs_of_nonneg (show 0 ≤ a by omega)] at haq
    simp only [digitRank, ite_eq_left hq, ite_eq_right (show ¬a < 0 by omega), add_zero]
    omega
  · by_cases hq0 : q = 0
    · have hap : 0 < a := by rw [hq0, mul_zero, zero_add] at ea; omega
      rw [abs_of_nonneg hap.le] at haq
      simp only [digitRank, hq0, Int.natAbs_zero, mul_zero, lt_irrefl, ite_false,
        ite_eq_right (not_lt.mpr hap.le), add_zero]
      omega
    · have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ q by omega)
        (show 0 ≤ B - 1 by omega)
      have h : q ≤ -a := by nlinarith
      have han : a < 0 := by omega
      rw [abs_of_nonneg (show 0 ≤ q by omega)] at hqq
      rw [abs_of_neg han] at haq
      simp only [digitRank, ite_eq_right hq, ite_eq_left han, add_zero]
      omega

private theorem digitSumAux_zero (B : ℤ) (f : ℕ) : negBaseSqDigitSumAux (-B) f 0 = 0 := by
  cases f <;> simp [negBaseSqDigitSumAux]

private theorem digitSumAux_stable {B : ℤ} (hB : 2 ≤ B) {f g : ℕ} {a : ℤ}
    (hf : digitRank a ≤ f) (hg : digitRank a ≤ g) :
    negBaseSqDigitSumAux (-B) f a = negBaseSqDigitSumAux (-B) g a := by
  induction f generalizing a g with
  | zero =>
    have ha : a = 0 := by
      have := Int.natAbs_eq_zero (a := a)
      unfold digitRank at hf
      omega
    subst a
    simp only [digitSumAux_zero]
  | succ f ih =>
    by_cases ha : a = 0
    · subst a
      simp only [digitSumAux_zero]
    have hgpos : 0 < g := by
      have := Int.natAbs_eq_zero (a := a)
      unfold digitRank at hg
      omega
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hgpos.ne'
    let d := a % (-B)
    let q := (a - d) / (-B)
    have hb : -B ≠ 0 := by omega
    have hd0 : 0 ≤ d := Int.emod_nonneg _ hb
    have hd : d < B := by
      dsimp [d]
      rw [Int.emod_neg]
      exact Int.emod_lt_of_pos _ (by omega)
    have ea : -B * q + d = a := by
      have hdecomp := Int.mul_ediv_add_emod a (-B)
      have hquot : q = a / (-B) := by
        dsimp [q, d]
        rw [show a - a % (-B) = (-B) * (a / (-B)) by linarith]
        rw [mul_comm, Int.mul_ediv_cancel _ hb]
      rw [hquot, hdecomp]
    have hqa : digitRank q < digitRank a := by
      rw [← ea]
      exact digitRank_lt hB hd0 hd (ea ▸ ha)
    simp only [negBaseSqDigitSumAux, ite_eq_right ha]
    rw [ih (show digitRank q ≤ f by omega) (show digitRank q ≤ g by omega)]

private theorem digitSum_cons {B q d : ℤ} (hB : 2 ≤ B) (hd0 : 0 ≤ d) (hd : d < B) :
    negBaseSqDigitSum (-B) (-B * q + d) = d ^ 2 + negBaseSqDigitSum (-B) q := by
  let a := -B * q + d
  have hb : -B ≠ 0 := by omega
  have hr : a % (-B) = d := by
    dsimp [a]
    rw [Int.add_emod, Int.mul_emod_right, zero_add, Int.emod_emod, Int.emod_neg,
      Int.emod_eq_of_lt hd0 hd]
  have hq : (a - d) / (-B) = q := by
    rw [show a - d = q * (-B) by dsimp [a]; ring, Int.mul_ediv_cancel _ hb]
  change negBaseSqDigitSum (-B) a = _
  by_cases ha : a = 0
  · have hdz : d = 0 := by simpa [ha] using hr.symm
    have hqz : q = 0 := by simpa [ha, hdz] using hq.symm
    simp [ha, hdz, hqz]
  have hqa : digitRank q < digitRank a := digitRank_lt hB hd0 hd ha
  have bound (z : ℤ) : digitRank z ≤ 2 * z.natAbs + 1 := by
    unfold digitRank
    split <;> omega
  unfold negBaseSqDigitSum
  rw [show 2 * a.natAbs + 2 = (2 * a.natAbs + 1) + 1 from rfl, negBaseSqDigitSumAux,
    ite_eq_right ha, hr, hq]
  congr 1
  exact digitSumAux_stable hB (by have := bound a; omega) (by have := bound q; omega)

private theorem aux_nonneg (b : ℤ) (f : ℕ) (a : ℤ) : 0 ≤ negBaseSqDigitSumAux b f a := by
  induction f generalizing a with
  | zero => simp [negBaseSqDigitSumAux]
  | succ f ih =>
    unfold negBaseSqDigitSumAux
    by_cases ha : a = 0
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      have h1 : 0 ≤ (a % b) ^ 2 := Int.sq_nonneg _
      have h2 : 0 ≤ negBaseSqDigitSumAux b f ((a - a % b) / b) := ih _
      omega

private theorem s_nonneg (a : ℤ) : 0 ≤ negBaseSqDigitSum (-2) a := by
  unfold negBaseSqDigitSum
  exact aux_nonneg _ _ _

private theorem s_le_four_of_le7 (a : ℤ) (ha : a.natAbs ≤ 7) :
    negBaseSqDigitSum (-2) a ≤ 4 := by
  have hb : -7 ≤ a ∧ a ≤ 7 := by omega
  obtain ⟨hlo, hhi⟩ := hb
  interval_cases a <;> decide

private theorem s_mid_lt (a : ℤ) (h1 : 4 ≤ a.natAbs) (h2 : a.natAbs ≤ 7) :
    (negBaseSqDigitSum (-2) a).natAbs < a.natAbs := by
  have hb : -7 ≤ a ∧ a ≤ 7 := by omega
  obtain ⟨hlo, hhi⟩ := hb
  interval_cases a <;> first | decide | (exfalso; omega)

private theorem decomp (a : ℤ) :
    ∃ q d : ℤ, 0 ≤ d ∧ d < 2 ∧ a = -2 * q + d ∧
      negBaseSqDigitSum (-2) a = d ^ 2 + negBaseSqDigitSum (-2) q ∧
      (2 ≤ a.natAbs → q.natAbs < a.natAbs) := by
  let d := a % (-2)
  let q := (a - d) / (-2)
  have hb : (-2 : ℤ) ≠ 0 := by omega
  have hd0 : 0 ≤ d := Int.emod_nonneg _ hb
  have hd : d < 2 := by
    dsimp [d]
    rw [Int.emod_neg]
    exact Int.emod_lt_of_pos _ (by omega)
  have ea : -2 * q + d = a := by
    have hdecomp := Int.mul_ediv_add_emod a (-2)
    have hquot : q = a / (-2) := by
      dsimp [q, d]
      rw [show a - a % (-2) = (-2) * (a / (-2)) by linarith]
      rw [mul_comm, Int.mul_ediv_cancel _ hb]
    rw [hquot, hdecomp]
  have hS : negBaseSqDigitSum (-2) a = d ^ 2 + negBaseSqDigitSum (-2) q := by
    rw [← ea]
    exact digitSum_cons (by omega) hd0 hd
  refine ⟨q, d, hd0, hd, ea.symm, hS, ?_⟩
  intro h2
  have ha : a = -2 * q + d := ea.symm
  omega

private theorem s_modEq (a : ℤ) : negBaseSqDigitSum (-2) a ≡ a [ZMOD 3] := by
  have hall : ∀ n : ℕ, ∀ a : ℤ, a.natAbs < n → negBaseSqDigitSum (-2) a ≡ a [ZMOD 3] := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha_lt
      by_cases hsmall : a.natAbs ≤ 1
      · have hb : -1 ≤ a ∧ a ≤ 1 := by omega
        obtain ⟨hlo, hhi⟩ := hb
        interval_cases a <;> decide
      · have hge : 2 ≤ a.natAbs := by omega
        obtain ⟨q, d, hd0, hd, ha_eq, hS, hlt⟩ := decomp a
        have hq_lt : q.natAbs < a.natAbs := hlt hge
        have ih_q : negBaseSqDigitSum (-2) q ≡ q [ZMOD 3] := ih a.natAbs ha_lt q hq_lt
        have hd2 : d ^ 2 = d := by
          have hb2 : 0 ≤ d ∧ d ≤ 1 := by omega
          obtain ⟨hlo2, hhi2⟩ := hb2
          interval_cases d <;> decide
        have hbase : (-2 : ℤ) ≡ 1 [ZMOD 3] := by decide
        have h1 : (-2) * q ≡ q [ZMOD 3] := by
          simpa using Int.ModEq.mul_right q hbase
        have hcongr : d ^ 2 + negBaseSqDigitSum (-2) q ≡ (-2) * q + d [ZMOD 3] := by
          calc d ^ 2 + negBaseSqDigitSum (-2) q = d + negBaseSqDigitSum (-2) q := by rw [hd2]
            _ ≡ d + q [ZMOD 3] := Int.ModEq.add_left d ih_q
            _ = q + d := by ring
            _ ≡ (-2) * q + d [ZMOD 3] := Int.ModEq.add_right d h1.symm
        rw [hS, ha_eq]
        exact hcongr
  exact hall (a.natAbs + 1) a (by omega)

private theorem iterate_modEq (k : ℕ) (a : ℤ) :
    (negBaseSqDigitSum (-2))^[k] a ≡ a [ZMOD 3] := by
  induction k generalizing a with
  | zero => rw [Function.iterate_zero_apply]
  | succ n ih =>
    have hsucc : (negBaseSqDigitSum (-2))^[n.succ] a =
        negBaseSqDigitSum (-2) ((negBaseSqDigitSum (-2))^[n] a) :=
      Function.iterate_succ_apply' _ n a
    rw [hsucc]
    exact (s_modEq _).trans (ih _)

private theorem s_lt_of_large (a : ℤ) (ha : 8 ≤ a.natAbs) :
    (negBaseSqDigitSum (-2) a).natAbs < a.natAbs := by
  have hall : ∀ n : ℕ, ∀ a : ℤ, a.natAbs < n → 8 ≤ a.natAbs →
      (negBaseSqDigitSum (-2) a).natAbs < a.natAbs := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha_lt ha8
      obtain ⟨q, d, hd0, hd, ha_eq, hS, hlt⟩ := decomp a
      have hge2 : 2 ≤ a.natAbs := by omega
      have hq_lt : q.natAbs < a.natAbs := hlt hge2
      have hd2 : d ^ 2 = d := by
        have hb2 : 0 ≤ d ∧ d ≤ 1 := by omega
        obtain ⟨hlo2, hhi2⟩ := hb2
        interval_cases d <;> decide
      have hSnn : 0 ≤ negBaseSqDigitSum (-2) a := s_nonneg a
      have hSqnn : 0 ≤ negBaseSqDigitSum (-2) q := s_nonneg q
      by_cases hq8 : 8 ≤ q.natAbs
      · have ih_q : (negBaseSqDigitSum (-2) q).natAbs < q.natAbs :=
          ih a.natAbs ha_lt q hq_lt hq8
        have hcast_q : ((negBaseSqDigitSum (-2) q).natAbs : ℤ) =
            negBaseSqDigitSum (-2) q := by
          rw [Int.natCast_natAbs, abs_of_nonneg hSqnn]
        have hcast_a : ((negBaseSqDigitSum (-2) a).natAbs : ℤ) =
            negBaseSqDigitSum (-2) a := by
          rw [Int.natCast_natAbs, abs_of_nonneg hSnn]
        omega
      · have hq_le7 : q.natAbs ≤ 7 := by omega
        have hSq_le4 : negBaseSqDigitSum (-2) q ≤ 4 := s_le_four_of_le7 q hq_le7
        have hcast_a : ((negBaseSqDigitSum (-2) a).natAbs : ℤ) =
            negBaseSqDigitSum (-2) a := by
          rw [Int.natCast_natAbs, abs_of_nonneg hSnn]
        omega
  exact hall (a.natAbs + 1) a (by omega) ha

private theorem s_lt_of_ge4 (a : ℤ) (ha : 4 ≤ a.natAbs) :
    (negBaseSqDigitSum (-2) a).natAbs < a.natAbs := by
  by_cases h : 8 ≤ a.natAbs
  · exact s_lt_of_large a h
  · have hle : a.natAbs ≤ 7 := by omega
    exact s_mid_lt a ha hle
private theorem iterate_one_apply (f : ℤ → ℤ) (x : ℤ) : f^[1] x = f x := by
  have h1 : (1 : ℕ) = Nat.succ 0 := rfl
  rw [h1, Function.iterate_succ_apply', Function.iterate_zero_apply]

private theorem happy_one : IsNegBaseHappy (-2) 1 := by
  refine ⟨1, by omega, ?_⟩
  have h1 : (negBaseSqDigitSum (-2))^[1] (1 : ℤ) = negBaseSqDigitSum (-2) 1 :=
    iterate_one_apply _ _
  rw [h1]
  decide

private theorem happy_neg_two : IsNegBaseHappy (-2) (-2) := by
  refine ⟨1, by omega, ?_⟩
  have h1 : (negBaseSqDigitSum (-2))^[1] (-2 : ℤ) = negBaseSqDigitSum (-2) (-2) :=
    iterate_one_apply _ _
  rw [h1]
  decide

private theorem happy_of_iterate_happy (a b : ℤ) (k : ℕ)
    (hk : (negBaseSqDigitSum (-2))^[k] a = b) (hb : IsNegBaseHappy (-2) b) :
    IsNegBaseHappy (-2) a := by
  obtain ⟨j, hj0, hj⟩ := hb
  refine ⟨j + k, by omega, ?_⟩
  have hadd : (negBaseSqDigitSum (-2))^[j + k] a =
      (negBaseSqDigitSum (-2))^[j] ((negBaseSqDigitSum (-2))^[k] a) :=
    Function.iterate_add_apply _ j k a
  rw [hk, hj] at hadd
  exact hadd

private theorem happy_iff : ∀ a : ℤ, IsNegBaseHappy (-2) a ↔ a ≡ 1 [ZMOD 3] := by
  intro a
  constructor
  · rintro ⟨k, _, hk⟩
    have hmod := iterate_modEq k a
    rw [hk] at hmod
    exact hmod.symm
  · intro ha_mod
    have hall : ∀ n : ℕ, ∀ a : ℤ, a.natAbs < n → a ≡ 1 [ZMOD 3] →
        IsNegBaseHappy (-2) a := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro a ha_lt ha_mod
        by_cases hsmall : a.natAbs ≤ 3
        · have hb : -3 ≤ a ∧ a ≤ 3 := by omega
          obtain ⟨hlo, hhi⟩ := hb
          interval_cases a <;> first
            | exact happy_one
            | exact happy_neg_two
            | (exfalso; exact absurd ha_mod (by decide))
        · have hge4 : 4 ≤ a.natAbs := by omega
          have hlt : (negBaseSqDigitSum (-2) a).natAbs < a.natAbs :=
            s_lt_of_ge4 a hge4
          have hmod_S : negBaseSqDigitSum (-2) a ≡ 1 [ZMOD 3] :=
            (s_modEq a).trans ha_mod
          have hhappy_S : IsNegBaseHappy (-2) (negBaseSqDigitSum (-2) a) :=
            ih a.natAbs ha_lt (negBaseSqDigitSum (-2) a) hlt hmod_S
          have h1 : (negBaseSqDigitSum (-2))^[1] a = negBaseSqDigitSum (-2) a :=
            iterate_one_apply _ _
          exact happy_of_iterate_happy a (negBaseSqDigitSum (-2) a) 1 h1 hhappy_S
    exact hall (a.natAbs + 1) a (by omega) ha_mod

/-- **Happy numbers in base $-2$.** There is an integer $n$ such that $n + 3i$ is $(-2)$-happy for
every natural number $i$, and an integer $a$ is $(-2)$-happy if and only if $a \equiv 1 \pmod 3$.

This is part (1) of the Grundman–Harris theorem.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem isNegBaseHappy_neg_two_iff :
    (∃ n : ℤ, ∀ i : ℕ, IsNegBaseHappy (-2) (n + 3 * i)) ∧
      ∀ a : ℤ, IsNegBaseHappy (-2) a ↔ a ≡ 1 [ZMOD 3] := by
  constructor
  · refine ⟨1, fun i => (happy_iff _).mpr ?_⟩
    simp
  · exact happy_iff

end MetaMathlibExt
