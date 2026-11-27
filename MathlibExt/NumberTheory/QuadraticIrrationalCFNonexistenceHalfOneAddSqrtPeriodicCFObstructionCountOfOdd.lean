/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence
import MathlibExt.NumberTheory.QuadraticIrrationalCFClassification
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Seq.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.NumberTheory.Real.GoldenRatio
import MathlibExt.NumberTheory.SymmetricContinuantParity
import MathlibExt.NumberTheory.SymmetricConvergentDenParity

/-!
# Every parity pattern is realized by `(1 + √d) / 2` for odd period length

For odd $l$, every parity pattern in $(\mathbb{Z}/2)^{(l-1)/2}$ is realized by a symmetric
block $a_1, \dots, a_{l-1}$ of positive integers with the prescribed parities, for which
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$ for some natural numbers
$d$ and $a_0$ with $d$ not a perfect square; the overlined block repeats forever. Hence the
number of parity patterns that are not realized is $0$.

Statements from Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic
Irrational Number with a Given Sequence*, INTEGERS 26 (2026), Article A69.
-/

namespace MetaMathlibExt

-- Consecutive convergent denominators are coprime.
private theorem coprime_den (a : ℕ → ℕ) (n : ℕ) :
    (convergentDen a (n + 1)).Coprime (convergentDen a n) := by
  induction n with
  | zero => simp [convergentDen]
  | succ n ih =>
    rw [convergentDen_add_two, Nat.coprime_mul_right_add_left]
    exact ih.symm

-- A number coprime to an even number is odd.
private theorem odd_of_even_coprime {m n : ℕ} (hm : Even m) (h : m.Coprime n) :
    Odd n :=
  Nat.Coprime.odd_of_left (Nat.Coprime.of_dvd_left (even_iff_two_dvd.mp hm) h)

-- Two coprime numbers with even sum are both odd.
private theorem odd_of_even_add_coprime {x y : ℕ} (h : Even (x + y))
    (hc : x.Coprime y) : Odd x ∧ Odd y := by
  rw [Nat.even_iff] at h
  rcases Nat.even_or_odd x with hx | hx
  · exfalso
    rw [Nat.even_iff] at hx
    have hy : y % 2 = 0 := by omega
    have h2 : 2 ∣ Nat.gcd x y := Nat.dvd_gcd (by omega) (by omega)
    have h1 : Nat.gcd x y = 1 := hc
    omega
  · have hy : y % 2 = 1 := by
      rw [Nat.odd_iff] at hx
      omega
    exact ⟨hx, Nat.odd_iff.mpr hy⟩

-- One step of the Casoratian identity for continuants.
private theorem casoratian_step (a : ℕ → ℕ) (n : ℕ) :
    ((convergentDen a (n + 3) : ℤ) * (convergentDen (fun k => a (k + 1)) (n + 1)) -
      (convergentDen a (n + 2)) * (convergentDen (fun k => a (k + 1)) (n + 2))) =
    -(((convergentDen a (n + 2) : ℤ) * (convergentDen (fun k => a (k + 1)) n) -
      (convergentDen a (n + 1)) * (convergentDen (fun k => a (k + 1)) (n + 1)))) := by
  have hq : convergentDen a (n + 3) =
      a (n + 3) * convergentDen a (n + 2) + convergentDen a (n + 1) :=
    convergentDen_add_two a (n + 1)
  have hr : convergentDen (fun k => a (k + 1)) (n + 2) =
      a (n + 3) * convergentDen (fun k => a (k + 1)) (n + 1) +
        convergentDen (fun k => a (k + 1)) n :=
    convergentDen_add_two (fun k => a (k + 1)) n
  rw [hq, hr]
  push_cast
  ring

-- The Casoratian identity for continuants.
private theorem casoratian (a : ℕ → ℕ) (n : ℕ) :
    (convergentDen a (n + 2) : ℤ) * (convergentDen (fun k => a (k + 1)) n) -
      (convergentDen a (n + 1)) * (convergentDen (fun k => a (k + 1)) (n + 1)) =
      (-1 : ℤ) ^ (n + 2) := by
  induction n with
  | zero =>
    simp [convergentDen]
    ring
  | succ n ih =>
    change (convergentDen a (n + 3) : ℤ) *
        (convergentDen (fun k => a (k + 1)) (n + 1)) -
        (convergentDen a (n + 2)) * (convergentDen (fun k => a (k + 1)) (n + 2)) =
      (-1 : ℤ) ^ (n + 3)
    rw [casoratian_step a n, ih]
    change -(-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ (n + 2 + 1)
    rw [pow_succ]
    ring

-- For odd length, the parity criterion for `(1 + √d) / 2` always holds.
private theorem criterion_of_odd (l : ℕ) (hl : Odd l) (hl3 : 3 ≤ l) (a : ℕ → ℕ)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    Odd (convergentDen a (l - 1)) ∨
      (Odd (convergentDen a (l - 2)) ∧
        Odd (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
        Even (convergentDen a (l - 1))) := by
  by_cases hodd : Odd (convergentDen a (l - 1))
  · exact Or.inl hodd
  · rw [Nat.not_odd_iff_even] at hodd
    refine Or.inr ⟨?_, ?_, hodd⟩
    · have hc := coprime_den a (l - 2)
      rw [show l - 2 + 1 = l - 1 by omega] at hc
      exact odd_of_even_coprime hodd hc
    · obtain ⟨t, rfl⟩ := hl
      by_cases ht1 : t = 1
      · subst ht1
        exact odd_one
      · have ht2 : 2 ≤ t := by omega
        have hl5 : 5 ≤ 2 * t + 1 := by omega
        by_cases hr : Odd (convergentDen (fun n => a (n + 1)) (2 * t + 1 - 3))
        · exact hr
        · exfalso
          rw [Nat.not_odd_iff_even] at hr
          have hq := convergentDen_parity_of_odd (2 * t + 1) ⟨t, rfl⟩ (by omega) a hsymm
          have hrr :=
            shifted_convergentDen_parity_of_odd (2 * t + 1) ⟨t, rfl⟩ hl5 a hsymm
          rw [show (2 * t + 1 - 1) / 2 = t by omega,
            show (2 * t + 1 - 3) / 2 = t - 1 by omega] at hq
          rw [show (2 * t + 1 - 1) / 2 - 1 = t - 1 by omega,
            show (2 * t + 1 - 3) / 2 - 1 = t - 2 by omega] at hrr
          rw [Nat.ModEq] at hq hrr
          have hqeven : Even (convergentDen a t + convergentDen a (t - 1)) := by
            rw [Nat.even_iff]
            have h0 : convergentDen a (2 * t + 1 - 1) % 2 = 0 :=
              Nat.even_iff.mp hodd
            omega
          have hr_even :
              Even (convergentDen (fun n => a (n + 1)) (t - 1) +
                convergentDen (fun n => a (n + 1)) (t - 2)) := by
            rw [Nat.even_iff]
            have h0 : convergentDen (fun n => a (n + 1)) (2 * t + 1 - 3) % 2 = 0 :=
              Nat.even_iff.mp hr
            omega
          have hcq := coprime_den a (t - 1)
          rw [show t - 1 + 1 = t by omega] at hcq
          obtain ⟨hqt, hqt1⟩ := odd_of_even_add_coprime hqeven hcq
          have hcr := coprime_den (fun k => a (k + 1)) (t - 2)
          rw [show t - 2 + 1 = t - 1 by omega] at hcr
          obtain ⟨hrt1, hrt2⟩ := odd_of_even_add_coprime hr_even hcr
          have hcas := casoratian a (t - 2)
          rw [show t - 2 + 2 = t by omega, show t - 2 + 1 = t - 1 by omega] at hcas
          have e1 : Odd (convergentDen a t : ℤ) := (Int.odd_natCast _).mpr hqt
          have e2 : Odd (convergentDen (fun n => a (n + 1)) (t - 2) : ℤ) :=
            (Int.odd_natCast _).mpr hrt2
          have e3 : Odd (convergentDen a (t - 1) : ℤ) := (Int.odd_natCast _).mpr hqt1
          have e4 : Odd (convergentDen (fun n => a (n + 1)) (t - 1) : ℤ) :=
            (Int.odd_natCast _).mpr hrt1
          have hEven : Even ((convergentDen a t : ℤ) *
              (convergentDen (fun n => a (n + 1)) (t - 2)) -
              (convergentDen a (t - 1) : ℤ) *
              (convergentDen (fun n => a (n + 1)) (t - 1))) :=
            (e1.mul e2).sub_odd (e3.mul e4)
          rw [hcas] at hEven
          have hOdd : Odd ((-1 : ℤ) ^ t) := Odd.pow ⟨-1, by decide⟩
          exact (Int.not_even_iff_odd.mpr hOdd) hEven

-- The value prescribed by a parity pattern at one index: `2` for `0`, `1` else.
private def repVal (t : ℕ) (v : Fin t → ZMod 2) (k : ℕ) : ℕ :=
  if h : k < t then (if v ⟨k, h⟩ = 0 then 2 else 1) else 1

private theorem repVal_pos (t : ℕ) (v : Fin t → ZMod 2) (k : ℕ) :
    0 < repVal t v k := by
  unfold repVal
  split
  · split <;> decide
  · decide

-- The symmetric sequence with the parities prescribed by `v`.
private def symmRep (t : ℕ) (v : Fin t → ZMod 2) : ℕ → ℕ := fun i =>
  if _ : i % (2 * t + 1) = 0 then 1
  else repVal t v (min (i % (2 * t + 1)) (2 * t + 1 - i % (2 * t + 1)) - 1)

private theorem symmRep_pos (t : ℕ) (v : Fin t → ZMod 2) (i : ℕ) :
    0 < symmRep t v i := by
  unfold symmRep
  split
  · decide
  · exact repVal_pos t v _

private theorem symmRep_symm (t : ℕ) (v : Fin t → ZMod 2) (i : ℕ) (h1 : 1 ≤ i)
    (hlt : i < 2 * t + 1) : symmRep t v i = symmRep t v (2 * t + 1 - i) := by
  unfold symmRep
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 2 * t + 1 - i < 2 * t + 1),
    dite_eq_right (by omega : ¬ i = 0),
    dite_eq_right (by omega : ¬ 2 * t + 1 - i = 0)]
  have hmin : min (2 * t + 1 - i) (2 * t + 1 - (2 * t + 1 - i)) =
      min i (2 * t + 1 - i) := by
    rw [Nat.sub_sub_self (by omega : i ≤ 2 * t + 1), min_comm]
  rw [hmin]

private theorem symmRep_match (t : ℕ) (v : Fin t → ZMod 2) (j : Fin t) :
    ((symmRep t v ((j : ℕ) + 1) : ℕ) : ZMod 2) = v j := by
  have hj1 : ((j : ℕ) + 1) % (2 * t + 1) = (j : ℕ) + 1 :=
    Nat.mod_eq_of_lt (by have := j.isLt; omega)
  unfold symmRep
  rw [hj1, dite_eq_right (by omega : ¬ (j : ℕ) + 1 = 0)]
  have hmin : min ((j : ℕ) + 1) (2 * t + 1 - ((j : ℕ) + 1)) = (j : ℕ) + 1 :=
    Nat.min_eq_left (by have := j.isLt; omega)
  rw [hmin, Nat.add_sub_cancel]
  unfold repVal
  rw [dite_eq_left j.isLt]
  have hjfin : (⟨(j : ℕ), j.isLt⟩ : Fin t) = j := by cases j; rfl
  rw [hjfin]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (v j) with h0 | h1
  · rw [ite_eq_left h0, h0]
    decide
  · rw [ite_eq_right (by rw [h1]; decide), h1]
    simp

-- Read a regular continued fraction including its integer part at index zero.
-- (The fixed-point digit computation here follows the one for the symmetric
-- block matrix in `QuadraticIrrationalCFClassification`.)
private noncomputable def digit (x : ℝ) : ℕ → Option ℝ
  | 0 => some (GenContFract.of x).h
  | n + 1 => (GenContFract.of x).partDens.get? n

private theorem prepend (b : ℕ) {t : ℝ} (ht : 1 < t) :
    digit (b + t⁻¹) 0 = some b ∧ ∀ n, digit (b + t⁻¹) (n + 1) = digit t n := by
  have hi : 0 < t⁻¹ := inv_pos.mpr (zero_lt_one.trans ht)
  have hj : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans ht)).mpr ht
  have hf : ⌊(b : ℝ) + t⁻¹⌋ = (b : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hfr : Int.fract ((b : ℝ) + t⁻¹) = t⁻¹ := by simp [Int.fract, hf]
  refine ⟨by simp [digit, hf], ?_⟩
  intro n
  cases n with
  | zero =>
    have h := GenContFract.of_s_head (hfr.trans_ne hi.ne')
    change (GenContFract.of ((b : ℝ) + t⁻¹)).s.get? 0 = _ at h
    simpa [digit, hfr] using GenContFract.partDen_eq_s_b h
  | succ n =>
    simp only [digit, GenContFract.partDens, Stream'.Seq.map_get?, GenContFract.of_s_succ,
      hfr, inv_inv]

private theorem phi_gt_one : 1 < (1 + √((5 : ℕ) : ℝ)) / 2 := by
  rw [Nat.cast_ofNat]
  exact Real.one_lt_goldenRatio

private theorem phi_eq : (1 + √((5 : ℕ) : ℝ)) / 2 =
    1 + ((1 + √((5 : ℕ) : ℝ)) / 2)⁻¹ := by
  rw [Nat.cast_ofNat]
  change Real.goldenRatio = 1 + Real.goldenRatio⁻¹
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

private theorem phi_hasPeriodicCF (a : ℕ → ℕ) :
    HasPeriodicCF ((1 + √((5 : ℕ) : ℝ)) / 2) 1 a 1 (2 * 1 - 1) := by
  have hpre := prepend 1 phi_gt_one
  rw [show ((1 : ℕ) : ℝ) = 1 from Nat.cast_one] at hpre
  rw [← phi_eq] at hpre
  obtain ⟨h0, ht⟩ := hpre
  refine ⟨?_, ?_⟩
  · simpa [digit] using h0
  · intro n
    have hn : ∀ k, digit ((1 + √((5 : ℕ) : ℝ)) / 2) k = some 1 := by
      intro k
      induction k with
      | zero => simpa using h0
      | succ k ih => rw [ht k, ih]
    have hpd : (GenContFract.of ((1 + √((5 : ℕ) : ℝ)) / 2)).partDens.get? n =
        digit ((1 + √((5 : ℕ) : ℝ)) / 2) (n + 1) := rfl
    rw [hpd, hn, show (n + 1) % 1 = 0 by omega]
    norm_num

-- Every parity pattern is realized at odd length `2 * t + 1`.
private theorem realizable (t : ℕ) (v : Fin t → ZMod 2) :
    ∃ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < 2 * t + 1 → 0 < a i) ∧
      (∀ i, 1 ≤ i → i < 2 * t + 1 → a i = a (2 * t + 1 - i)) ∧
      (∀ j : Fin t, ((a ((j : ℕ) + 1) : ℕ) : ZMod 2) = v j) ∧
      ∃ d a₀ : ℕ, ¬IsSquare d ∧
        HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a (2 * t + 1) (2 * a₀ - 1) := by
  by_cases ht : t = 0
  · subst ht
    refine ⟨fun _ => 1, ?_, ?_, ?_, 5, 1, ?_, ?_⟩
    · intro i h1 h2
      change (0 : ℕ) < 1
      omega
    · intro i h1 h2
      change (1 : ℕ) = 1
      rfl
    · intro j
      exact Fin.elim0 j
    · rintro ⟨r, hr⟩
      by_cases h3 : 3 ≤ r
      · have h9 : 3 * 3 ≤ r * r := Nat.mul_le_mul h3 h3
        omega
      · have hle : r ≤ 2 := by omega
        have h4 : r * r ≤ 2 * 2 := Nat.mul_le_mul hle hle
        omega
    · exact phi_hasPeriodicCF _
  · have hl3 : 3 ≤ 2 * t + 1 := by omega
    have hpos : ∀ i, 1 ≤ i → i < 2 * t + 1 → 0 < symmRep t v i :=
      fun i _ _ => symmRep_pos t v i
    have hsymm :
        ∀ i, 1 ≤ i → i < 2 * t + 1 → symmRep t v i = symmRep t v (2 * t + 1 - i) :=
      fun i h1 hlt => symmRep_symm t v i h1 hlt
    have hmatch :
        ∀ j : Fin t, ((symmRep t v ((j : ℕ) + 1) : ℕ) : ZMod 2) = v j :=
      fun j => symmRep_match t v j
    refine ⟨symmRep t v, hpos, hsymm, hmatch, ?_⟩
    have hcrit := criterion_of_odd (2 * t + 1) ⟨t, rfl⟩ hl3 (symmRep t v) hsymm
    obtain ⟨d, a₀, -, hnsq, hcf⟩ :=
      (half_one_add_sqrt_hasPeriodicCF_exists_iff_parity (2 * t + 1) hl3 _ hpos
        hsymm).mpr hcrit
    exact ⟨d, a₀, hnsq, hcf⟩

@[expose] public section

/-- **Every parity pattern is realized by $(1 + \sqrt{d})/2$ for odd period length.** Let $l$ be
odd. For every parity pattern $(v_1, \dots, v_{(l-1)/2}) \in (\mathbb{Z}/2)^{(l-1)/2}$ there are
positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i \le l - 1$ and
$a_j \equiv v_j \pmod 2$ for $1 \le j \le (l-1)/2$, a natural number $d$ that is not a perfect
square and a natural number $a_0$ with
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$. That is, the number $A'_l$
of patterns that are not realized is $0$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 5
(`integers-2026-A69-thm-5`). -/
public theorem half_one_add_sqrt_periodicCF_obstruction_count_of_odd (l : ℕ)
    (hl : Odd l) :
    Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
        (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
        (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
        ∃ d a₀ : ℕ, ¬IsSquare d ∧
          HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)} = 0 := by
  obtain ⟨t, rfl⟩ := hl
  rw [show (2 * t + 1) / 2 = t by omega]
  rw [Set.ncard_eq_zero ((Set.finite_univ).subset (Set.subset_univ _)),
    Set.eq_empty_iff_forall_notMem]
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv
  exact absurd (realizable t v) hv

end

end MetaMathlibExt
