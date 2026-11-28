/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.BronzeMetallicIdentities
import MathlibExt.NumberTheory.Recurrences.SubsequenceSecondOrderRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Floor of greedy mixed bronze sums

For natural-number digits satisfying the greedy prefix inequalities through $n+1$, the floor
of their weighted sum in the mixed bronze basis of Theorem 8 times $(5+\sqrt{13})/6$ is the
sum with the same digits in the shifted basis of Theorem 10 (2). This includes the zero sum
and permits leading zero digits.

The error in each block of three digits is bounded using Proposition 3 (4)–(6). We track a
second, stronger bound for small prefixes: any block with four digits counted with multiplicity
can occur only after such a prefix.

## References

* Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with
  Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, pp. 1–38, Theorems 8 and 10 (2) and
  Proposition 3 (4)–(6).
* The two-bound block induction adapts the strategy of `floor_greedy_bronze_companion_sum_mul`
  in `MathlibExt.NumberTheory.OlympicGamesNumerationFloorGreedyBronzeCompanionSumMul`
  (Theorem 10 (1)).
* The even-subsequence recurrence uses `subsequence_secondOrderRecurrence` from
  `MathlibExt.NumberTheory.Recurrences.SubsequenceSecondOrderRecurrence`.
-/

namespace MetaMathlibExt

open Finset

local notation "B" => lucasU bronzeLucasParams
local notation "C" => bronzeCompanionFirst
local notation "D" => bronzeCompanionSecond
local notation "β" => (((5 + Real.sqrt 13) / 6) : ℝ)
local notation "γ" => (((Real.sqrt 13 - 3) / 2) : ℝ)
local notation "A" => ((1 + γ) / 3)
local notation "θ" => (γ ^ 2)

private theorem bronzePair_step (m : ℕ) :
    B (2 * (m + 1)) = 3 * B (2 * m + 1) + B (2 * m) ∧
      B (2 * (m + 1) + 1) = 10 * B (2 * m + 1) + 3 * B (2 * m) := by
  have h₀ := lucasU_bronzeLucasParams_add_two (2 * m)
  have h₁ := lucasU_bronzeLucasParams_add_two (2 * m + 1)
  rw [show 2 * (m + 1) = 2 * m + 2 by omega]
  constructor
  · exact h₀
  · simp only [Nat.add_assoc, Nat.reduceAdd] at h₁ ⊢
    omega

private theorem bronzePair_bounds (m : ℕ) :
    0 ≤ B (2 * m) ∧ 3 * B (2 * m) < B (2 * m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      obtain ⟨hp, hb⟩ := bronzePair_step m
      rw [hp, hb]
      omega

-- Only the even-indexed companions enter the mixed weights. Their subsequences obey the same
-- recurrence as the shifted bronze subsequences, so the initial values suffice.
private theorem mixedBronze_even_weights (m : ℕ) :
    D (2 * m) = B (2 * m + 1) - B (2 * m) ∧
      B (2 * m + 1) + C (2 * m + 2) = 5 * B (2 * m + 1) + B (2 * m) := by
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m h₀ h₁ =>
      let params : LucasSequenceParams := ⟨3, -1, by decide⟩
      have ht : 0 < (2 : ℕ) := by decide
      have hB := subsequence_secondOrderRecurrence params B
        (by simpa [params] using lucasU_bronzeLucasParams_add_two) 2
      have hp := (hB 0 ht).1 m
      have hb := (hB 1 ht).1 m
      have hD := (subsequence_secondOrderRecurrence params D
        (by simpa [params] using bronzeCompanionSecond_add_two) 2 0 ht).1 m
      have hC := (subsequence_secondOrderRecurrence params C
        (by simpa [params] using bronzeCompanionFirst_add_two) 2 2 ht).1 m
      have hV : lucasV params 2 = 11 := by decide
      have hQ : params.q ^ 2 = 1 := by decide
      simp only [hV, hQ, Nat.add_zero, one_mul] at hp hb hD hC
      constructor <;> omega

-- If the block uses one digit more than its usual budget, the incoming prefix must be small.
private theorem mixedBronze_digit_budget {p b u x y z : ℤ}
    (hp : 0 ≤ p) (hb : 3 * p < b) (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h₁ : u + x * (b - p) < 3 * b)
    (h₂ : u + x * (b - p) + y * (3 * b) < 5 * b + p)
    (h₃ : u + x * (b - p) + y * (3 * b) + z * (5 * b + p) < 7 * b + 2 * p) :
    (x + y + z ≤ 3 ∨ x + y + z ≤ 4 ∧ u < 4 * p - b) ∧
      (u + x * (b - p) + y * (3 * b) + z * (5 * b + p) < 2 * b + p →
        x + y + z ≤ 2 ∨ x + y + z ≤ 3 ∧ u < 4 * p - b) := by
  have hxb := mul_nonneg hx (show 0 ≤ b - p by omega)
  have hyb := mul_nonneg hy (show 0 ≤ 3 * b by omega)
  have hx₄ : x ≤ 4 := by
    by_contra! h
    have := mul_le_mul_of_nonneg_right h (show 0 ≤ b - p by omega)
    linarith only [this, h₁, hp, hb, hu]
  have hy₁ : y ≤ 1 := by
    by_contra! h
    have := mul_le_mul_of_nonneg_right h (show 0 ≤ 3 * b by omega)
    linarith only [this, h₂, hp, hb, hu, hxb]
  have hz₁ : z ≤ 1 := by
    by_contra! h
    have := mul_le_mul_of_nonneg_right h (show 0 ≤ 5 * b + p by omega)
    linarith only [this, h₃, hp, hb, hu, hxb, hyb]
  interval_cases x <;> interval_cases y <;> interval_cases z <;>
    norm_num at h₁ h₂ h₃ ⊢ <;> omega

private theorem gamma_bounds : 1 / 5 < γ ∧ γ < 1 / 2 := by
  have hlo : (17 : ℝ) / 5 < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 13 < 4 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  constructor <;> linarith only [hlo, hhi]

private noncomputable def digitCap (m : ℕ) : ℝ := A * θ ^ m

private noncomputable def prefixCap (m : ℕ) : ℝ := 1 - (1 - 2 * A) * θ ^ m

private theorem prefixCap_succ (m : ℕ) :
    prefixCap (m + 1) = prefixCap m + 3 * digitCap (m + 1) := by
  have hγ : γ ^ 2 + 3 * γ = 1 := by
    linear_combination (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)) / 4
  simp only [prefixCap, digitCap, pow_succ θ]
  linear_combination -((1 + γ) / 3 * θ ^ m) * hγ

-- The correction terms for the three mixed weights are nonnegative and each is at most A θ^m.
private theorem mixedBronze_error_coefficients (m : ℕ) :
    (D (2 * m) : ℝ) * β - B (2 * m + 1) = digitCap m ∧
      (3 * B (2 * m + 1) : ℝ) * β - C (2 * m + 2) = γ * θ ^ m ∧
      ((B (2 * m + 1) + C (2 * m + 2) : ℤ) : ℝ) * β - D (2 * m + 2) =
        (5 * γ - 1) / 3 * θ ^ m := by
  obtain ⟨-, -, -, h₄, h₅, h₆⟩ := bronze_mul_metallic_identities m
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hs₀ : Real.sqrt (13 : ℝ) ≠ 0 := by positivity
  have h₄c : (13 - 3 * Real.sqrt 13) / (2 * Real.sqrt 13) = γ := by
    field_simp
    nlinarith only [hs]
  have h₅c : (65 - 17 * Real.sqrt 13) / (6 * Real.sqrt 13) = (5 * γ - 1) / 3 := by
    field_simp
    nlinarith only [hs]
  have h₆c : (13 - Real.sqrt 13) / (6 * Real.sqrt 13) = A := by
    field_simp
    nlinarith only [hs]
  rw [h₄c, pow_mul] at h₄
  rw [h₅c, pow_mul] at h₅
  rw [h₆c, pow_mul] at h₆
  refine ⟨sub_eq_of_eq_add ?_, sub_eq_of_eq_add ?_, sub_eq_of_eq_add ?_⟩
  · simpa only [digitCap, add_comm] using h₆
  · simpa only [add_comm] using h₄
  · simpa only [add_comm] using h₅

-- The second bound saves one digit's error whenever the completed weighted prefix is small.
private theorem mixedBronze_prefix_bound (R : ℕ → ℤ) (e : ℕ → ℝ) (a : ℕ → ℕ)
    (hw : ∀ m, R (3 * m) = B (2 * m + 1) - B (2 * m) ∧
      R (3 * m + 1) = 3 * B (2 * m + 1) ∧
      R (3 * m + 2) = 5 * B (2 * m + 1) + B (2 * m))
    (he : ∀ m, e (3 * m) ≤ digitCap m ∧ e (3 * m + 1) ≤ digitCap m ∧
      e (3 * m + 2) ≤ digitCap m)
    (hR₀ : ∀ k, 0 ≤ R k) (ha : ∀ j, ∑ k ∈ range j, (a k : ℤ) * R k < R j) (m : ℕ) :
    let P (j : ℕ) := ∑ k ∈ range j, (a k : ℤ) * R k
    let E (j : ℕ) := ∑ k ∈ range j, (a k : ℝ) * e k
    E (3 * m + 3) ≤ prefixCap m ∧
      (P (3 * m + 3) < 2 * B (2 * m + 1) + B (2 * m) →
        E (3 * m + 3) ≤ prefixCap m - digitCap m) := by
  let P (j : ℕ) := ∑ k ∈ range j, (a k : ℤ) * R k
  let E (j : ℕ) := ∑ k ∈ range j, (a k : ℝ) * e k
  change E (3 * m + 3) ≤ prefixCap m ∧
    (P (3 * m + 3) < 2 * B (2 * m + 1) + B (2 * m) → E (3 * m + 3) ≤ _)
  have hP (j : ℕ) : P (j + 1) = P j + (a j : ℤ) * R j := sum_range_succ _ _
  have hE (j : ℕ) : E (j + 1) = E j + (a j : ℝ) * e j := sum_range_succ _ _
  let digits (i : ℕ) := a (3 * i) + a (3 * i + 1) + a (3 * i + 2)
  have hAdded (i k : ℕ) (hk : digits i ≤ k) :
      E (3 * i + 3) ≤ E (3 * i) + (k : ℝ) * digitCap i := by
    obtain ⟨h₀, h₁, h₂⟩ := he i
    have hcap : 0 ≤ digitCap i :=
      mul_nonneg (by linarith only [gamma_bounds.1]) (pow_nonneg (sq_nonneg γ) _)
    calc
      E (3 * i + 3) = E (3 * i) + (a (3 * i) : ℝ) * e (3 * i) +
          (a (3 * i + 1) : ℝ) * e (3 * i + 1) + (a (3 * i + 2) : ℝ) * e (3 * i + 2) := by
        rw [hE (3 * i + 2), hE (3 * i + 1), hE (3 * i)]
      _ ≤ E (3 * i) + (digits i : ℝ) * digitCap i := by
        simp only [digits, Nat.cast_add, add_mul]
        simp only [← add_assoc]
        exact add_le_add (add_le_add (add_le_add_right
          (mul_le_mul_of_nonneg_left h₀ (Nat.cast_nonneg _)) _)
          (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)))
          (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _))
      _ ≤ _ := by
        have hk' : (digits i : ℝ) ≤ k := by exact_mod_cast hk
        exact add_le_add_right (mul_le_mul_of_nonneg_right hk' hcap) _
  have hWeightsNext (i : ℕ) : R (3 * i + 3) = 7 * B (2 * i + 1) + 2 * B (2 * i) := by
    rw [show 3 * i + 3 = 3 * (i + 1) by omega, (hw (i + 1)).1,
      (bronzePair_step i).1, (bronzePair_step i).2]
    omega
  have hBudget (i : ℕ) :
      (digits i ≤ 3 ∨ digits i ≤ 4 ∧ P (3 * i) < 4 * B (2 * i) - B (2 * i + 1)) ∧
      (P (3 * i + 3) < 2 * B (2 * i + 1) + B (2 * i) →
        digits i ≤ 2 ∨ digits i ≤ 3 ∧ P (3 * i) < 4 * B (2 * i) - B (2 * i + 1)) := by
    obtain ⟨hw₀, hw₁, hw₂⟩ := hw i
    have h₁ := ha (3 * i + 1)
    have h₂ := ha (3 * i + 2)
    have h₃ := ha (3 * i + 3)
    change P _ < _ at h₁ h₂ h₃
    rw [hP (3 * i), hw₀, hw₁] at h₁
    rw [hP (3 * i + 1), hP (3 * i), hw₀, hw₁, hw₂] at h₂
    rw [hP (3 * i + 2), hP (3 * i + 1), hP (3 * i), hw₀, hw₁, hw₂, hWeightsNext] at h₃
    have hu : 0 ≤ P (3 * i) := sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hR₀ k)
    obtain ⟨hp, hb⟩ := bronzePair_bounds i
    have h := mixedBronze_digit_budget hp hb hu (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) h₁ h₂ h₃
    rw [hP (3 * i + 2), hP (3 * i + 1), hP (3 * i), hw₀, hw₁, hw₂]
    exact_mod_cast h
  induction m with
  | zero =>
      have h₁ := ha 1
      have h₂ := ha 2
      have h₃ := ha 3
      have hw₀ : R 0 = 1 := (hw 0).1.trans (by decide)
      have hw₁ : R 1 = 3 := (hw 0).2.1.trans (by decide)
      have hw₂ : R 2 = 5 := (hw 0).2.2.trans (by decide)
      have hw₃ : R 3 = 7 := (hWeightsNext 0).trans (by decide)
      have hP₀ : P 0 = 0 := sum_range_zero _
      have hE₀ : E 0 = 0 := sum_range_zero _
      change P 1 < R 1 at h₁
      change P 2 < R 2 at h₂
      change P 3 < R 3 at h₃
      have hP₃ : P 3 = (a 0 : ℤ) + 3 * (a 1 : ℤ) + 5 * (a 2 : ℤ) := by
        rw [hP 2, hP 1, hP 0, hP₀, hw₀, hw₁, hw₂]
        ring
      rw [hP 0, hP₀, hw₀, hw₁] at h₁
      rw [hP 1, hP 0, hP₀, hw₀, hw₁, hw₂] at h₂
      rw [hP₃, hw₃] at h₃
      have hD : digits 0 = a 0 + a 1 + a 2 := rfl
      have hbase : prefixCap 0 = 2 * A := by simp [prefixCap]
      have hcap : digitCap 0 = A := by simp [digitCap]
      have h₂a := hAdded 0 2 (by rw [hD]; omega)
      change E 3 ≤ E 0 + (2 : ℝ) * digitCap 0 at h₂a
      rw [hE₀, zero_add, hcap] at h₂a
      refine ⟨hbase ▸ h₂a, ?_⟩
      intro hs
      have hSmall : P 3 < 2 := hs
      rw [hP₃] at hSmall
      have h₁a := hAdded 0 1 (by rw [hD]; omega)
      norm_num only [Nat.mul_zero, zero_add, Nat.cast_one, hE₀, one_mul, hcap] at h₁a
      rw [hbase, hcap]
      linarith only [h₁a]
  | succ i ih =>
      have hIdx : 3 * (i + 1) = 3 * i + 3 := by omega
      have hCut : 4 * B (2 * (i + 1)) - B (2 * (i + 1) + 1) =
          2 * B (2 * i + 1) + B (2 * i) := by
        rw [(bronzePair_step i).1, (bronzePair_step i).2]
        omega
      obtain ⟨hOrd, hSmall⟩ := hBudget (i + 1)
      rw [hIdx, hCut] at hOrd hSmall
      have hStep := prefixCap_succ i
      have hcap : digitCap (i + 1) ≤ digitCap i := by
        have hg := gamma_bounds
        have hθ : θ ≤ 1 := pow_le_one₀ (by linarith only [hg.1]) (by linarith only [hg.2])
        simp only [digitCap, pow_succ θ, ← mul_assoc]
        exact mul_le_of_le_one_right
          (mul_nonneg (by linarith only [hg.1]) (pow_nonneg (sq_nonneg γ) _)) hθ
      rw [hIdx]
      constructor
      · rcases hOrd with h | ⟨h, ht⟩
        · have hAdd := hAdded (i + 1) 3 h
          norm_num only [hIdx, Nat.cast_ofNat] at hAdd
          linarith only [hAdd, ih.1, hStep]
        · have hAdd := hAdded (i + 1) 4 h
          -- The saved digit is from the preceding block, whose unit of error is larger.
          norm_num only [hIdx, Nat.cast_ofNat] at hAdd
          linarith only [hAdd, ih.2 ht, hStep, hcap]
      · intro hs
        rcases hSmall hs with h | ⟨h, ht⟩
        · have hAdd := hAdded (i + 1) 2 h
          norm_num only [hIdx, Nat.cast_ofNat] at hAdd
          linarith only [hAdd, ih.1, hStep]
        · have hAdd := hAdded (i + 1) 3 h
          norm_num only [hIdx, Nat.cast_ofNat] at hAdd
          linarith only [hAdd, ih.2 ht, hStep, hcap]

/-- **Floor of greedy mixed bronze sums times $(5 + \sqrt{13})/6$.** Let $B_n$ be the bronze
numbers ($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ and $R'$ be the integer sequences with $R_{3m} = D_{2m}$,
$R_{3m+1} = 3B_{2m+1}$, $R_{3m+2} = B_{2m+1} + C_{2m+2}$ and $R'_{3m} = D_{2m}$,
$R'_{3m+1} = B_{2m+1}$, $R'_{3m+2} = C_{2m+2}$ for all $m \ge 0$. Let $n$ be a natural number
and $a_0, a_1, a_2, \dots$ natural numbers such that $\sum_{k=0}^{m-1} a_k R_k < R_m$ for every
$m \le n + 1$, and let $t = \sum_{k=0}^{n} a_k R_k$. Then
$\lfloor t (5 + \sqrt{13})/6 \rfloor = \sum_{k=0}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 8;
$n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (2). -/
public theorem floor_greedy_mixed_bronze_sum_mul (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then 3 * lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else lucasU bronzeLucasParams (2 * (k / 3) + 1) + bronzeCompanionFirst (2 * (k / 3) + 2))
    (hR' : ∀ k, R' k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else bronzeCompanionFirst (2 * (k / 3) + 2))
    (n : ℕ) (a : ℕ → ℕ) (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, (a k : ℤ) * R k < R m) :
    ⌊((∑ k ∈ range (n + 1), (a k : ℤ) * R k : ℤ) : ℝ) * ((5 + Real.sqrt 13) / 6)⌋ =
      ∑ k ∈ range (n + 1), (a k : ℤ) * R' (k + 1) := by
  -- Read the input and output weights in blocks, leaving the final output in the next block.
  have hRows (m : ℕ) :
      (R (3 * m) = D (2 * m) ∧ R (3 * m + 1) = 3 * B (2 * m + 1) ∧
        R (3 * m + 2) = B (2 * m + 1) + C (2 * m + 2)) ∧
      (R' (3 * m + 1) = B (2 * m + 1) ∧ R' (3 * m + 2) = C (2 * m + 2) ∧
        R' (3 * m + 3) = D (2 * m + 2)) := by
    have h₀ : (3 * m) / 3 = m := by omega
    have h₁ : (3 * m + 1) / 3 = m := by omega
    have h₂ : (3 * m + 2) / 3 = m := by omega
    have h₃ : (3 * m + 3) / 3 = m + 1 := by omega
    have h₀' : (3 * m) % 3 = 0 := by omega
    have h₁' : (3 * m + 1) % 3 = 1 := by omega
    have h₂' : (3 * m + 2) % 3 = 2 := by omega
    have h₃' : (3 * m + 3) % 3 = 0 := by omega
    norm_num [hR, hR', h₀, h₁, h₂, h₃, h₀', h₁', h₂', h₃', Nat.mul_add]
  have hWeights (m : ℕ) : R (3 * m) = B (2 * m + 1) - B (2 * m) ∧
      R (3 * m + 1) = 3 * B (2 * m + 1) ∧
      R (3 * m + 2) = 5 * B (2 * m + 1) + B (2 * m) := by
    obtain ⟨h₀, h₁, h₂⟩ := (hRows m).1
    obtain ⟨hD, hC⟩ := mixedBronze_even_weights m
    exact ⟨h₀.trans hD, h₁, h₂.trans hC⟩
  let e (k : ℕ) := (R k : ℝ) * β - R' (k + 1)
  have hErrors (m : ℕ) : (0 ≤ e (3 * m) ∧ e (3 * m) ≤ digitCap m) ∧
      (0 ≤ e (3 * m + 1) ∧ e (3 * m + 1) ≤ digitCap m) ∧
      (0 ≤ e (3 * m + 2) ∧ e (3 * m + 2) ≤ digitCap m) := by
    obtain ⟨⟨h₀, h₁, h₂⟩, h₁', h₂', h₃'⟩ := hRows m
    obtain ⟨hD, hB, hC⟩ := mixedBronze_error_coefficients m
    have hpow : 0 ≤ θ ^ m := pow_nonneg (sq_nonneg _) _
    have hg := gamma_bounds
    simp only [e, Nat.add_assoc, Nat.reduceAdd, h₀, h₁, h₂, h₁', h₂', h₃', Int.cast_mul,
      Int.cast_ofNat, hD, hB, hC]
    refine ⟨⟨?_, le_rfl⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact mul_nonneg (by linarith only [hg.1]) hpow
    · exact mul_nonneg (by linarith only [hg.1]) hpow
    · exact mul_le_mul_of_nonneg_right (by linarith only [hg.2]) hpow
    · exact mul_nonneg (by linarith only [hg.1]) hpow
    · exact mul_le_mul_of_nonneg_right (by linarith only [hg.2]) hpow
  have hIndex (k : ℕ) : ∃ m, k = 3 * m ∨ k = 3 * m + 1 ∨ k = 3 * m + 2 := ⟨k / 3, by omega⟩
  have hIncreasing : StrictMono R := by
    apply strictMono_nat_of_lt_succ
    intro k
    obtain ⟨m, rfl | rfl | rfl⟩ := hIndex k
    all_goals
      obtain ⟨hp, hb⟩ := bronzePair_bounds m
      obtain ⟨h₀, h₁, h₂⟩ := hWeights m
    · rw [h₀, h₁]
      omega
    · rw [h₁, h₂]
      omega
    · rw [h₂, show 3 * m + 2 + 1 = 3 * (m + 1) by omega, (hWeights (m + 1)).1,
        (bronzePair_step m).1, (bronzePair_step m).2]
      omega
  have hR₀ (k : ℕ) : 0 ≤ R k :=
    (sum_range_zero (fun j => (a j : ℤ) * R j) ▸ ha 0 (by omega)).le.trans
      (hIncreasing.monotone (Nat.zero_le k))
  let N := n + 1
  let a' (k : ℕ) := if k < N then a k else 0
  -- Padding the final block with zeros does not change either sum or spoil greediness.
  have hPad {M : Type} [AddCommMonoid M] (f : ℕ → M) (j : ℕ) :
      (∑ k ∈ range j, if k < N then f k else 0) = ∑ k ∈ range (min j N), f k := by
    rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter, mem_range, lt_min_iff]
  have ha' (j : ℕ) : ∑ k ∈ range j, (a' k : ℤ) * R k < R j := by
    simp only [a', Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
    rw [hPad (fun k => (a k : ℤ) * R k) j]
    exact (ha _ (min_le_right _ _)).trans_le (hIncreasing.monotone (min_le_left _ _))
  have hBound := (mixedBronze_prefix_bound R e a' hWeights
    (fun m => ⟨(hErrors m).1.2, (hErrors m).2.1.2, (hErrors m).2.2.2⟩) hR₀ ha' (n / 3)).1
  simp only [a', Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul] at hBound
  rw [hPad (fun k => (a k : ℝ) * e k), min_eq_right (show N ≤ 3 * (n / 3) + 3 by dsimp [N]; omega)]
    at hBound
  have h₁ : ∑ k ∈ range N, (a k : ℝ) * e k < 1 := by
    apply hBound.trans_lt
    have hpos : 0 < (1 - 2 * A) * θ ^ (n / 3) :=
      mul_pos (by linarith only [gamma_bounds.2]) (pow_pos (sq_pos_of_pos (by linarith only
        [gamma_bounds.1] : 0 < γ)) _)
    exact sub_lt_self _ hpos
  have h₀ : 0 ≤ ∑ k ∈ range N, (a k : ℝ) * e k := by
    apply sum_nonneg
    intro k _
    apply mul_nonneg (Nat.cast_nonneg _)
    obtain ⟨m, rfl | rfl | rfl⟩ := hIndex k
    · exact (hErrors m).1.1
    · exact (hErrors m).2.1.1
    · exact (hErrors m).2.2.1
  have hSum : ∑ k ∈ range N, (a k : ℝ) * e k =
      ((∑ k ∈ range N, (a k : ℤ) * R k : ℤ) : ℝ) * β -
        ((∑ k ∈ range N, (a k : ℤ) * R' (k + 1) : ℤ) : ℝ) := by
    push_cast
    simp_rw [e, mul_sub, ← mul_assoc, sum_sub_distrib, sum_mul]
  rw [hSum] at h₀ h₁
  exact Int.floor_eq_iff.mpr ⟨by linarith only [h₀], by linarith only [h₁]⟩

end MetaMathlibExt
