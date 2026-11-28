/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Ring.Real
public import MathlibExt.Combinatorics.InfiniteWord.CloitreSequence
public import Mathlib.Algebra.Group.Even
public import MathlibExt.NumberTheory.ContinuedFractions.Folding

import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Digit frequencies in Cloitre's approximants and the folding lemma

The proportions of digits `1` and `2` in Cloitre's finite approximants tend to `2/3` and `1/3`.

For a positive starting value and entries that are positive after the first, evaluation of
`finiteContFrac` from that starting value is the Möbius map of a product of `2 × 2` matrices.
Its determinant and reversal-transpose identity give `finiteContFrac_add_inv_mul_den_sq`: for
`[a₀; a₁, …, aₜ]` with `t` even and positive tail entries, and for every integer `x ≥ 1`,
adding `1 / (x * q ^ 2)` appends the fold `x, -aₜ, …, -a₁`, where `q` is the denominator in
lowest terms.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 and Theorem 17.
-/

namespace MetaMathlibExt

private theorem cloitreApprox_structure (k : ℕ) :
    ∃ l : List ℕ, cloitreApprox (k + 2) = [1, 1] ++ l ++ [1, 1] ∧
      l.count 1 = 2 * l.count 2 ∧ l.length = 3 * l.count 2 ∧ k ≤ l.length := by
  induction k with
  | zero =>
      exact ⟨[2, 1, 1], rfl, by decide, by decide, by decide⟩
  | succ k ih =>
      obtain ⟨l, hl, hcount, hlength, hbound⟩ := ih
      refine ⟨l ++ [1, 1, 2] ++ l.reverse, ?_, ?_, ?_, ?_⟩
      · change cloitreApprox (k + 2) ++ cloitreMirror (cloitreApprox (k + 2)) = _
        simp [hl, cloitreMirror, cloitreComplementFirst, List.reverse_append, List.append_assoc]
      · simp only [List.count_append, List.count_reverse]
        norm_num
        omega
      · simp only [List.length_append, List.length_reverse, List.count_append, List.count_reverse]
        norm_num
        omega
      · simp only [List.length_append, List.length_reverse]
        norm_num
        omega

private theorem cloitreApprox_statistics (k : ℕ) :
    ((cloitreApprox (k + 2)).count 1 : ℝ) =
        2 * ((cloitreApprox (k + 2)).count 2 : ℝ) + 4 ∧
      ((cloitreApprox (k + 2)).length : ℝ) =
        3 * ((cloitreApprox (k + 2)).count 2 : ℝ) + 4 ∧
      k + 4 ≤ (cloitreApprox (k + 2)).length := by
  obtain ⟨l, hl, hcount, hlength, hbound⟩ := cloitreApprox_structure k
  have hc : (l.count 1 : ℝ) = 2 * (l.count 2 : ℝ) := by exact_mod_cast hcount
  have hn : (l.length : ℝ) = 3 * (l.count 2 : ℝ) := by exact_mod_cast hlength
  simp only [hl, List.count_append, List.length_append]
  norm_num
  exact ⟨by linarith, by linarith, by omega⟩

/-- **Digit frequencies in Cloitre's approximants.** Let $A_k$ be the $k$-th approximant of
Cloitre's sequence. As $k \to \infty$, the proportion of entries of $A_k$ equal to $1$ tends to
$2/3$, and the proportion of entries equal to $2$ tends to $1/3$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 17
(`jis-2026-26.3.6-thm-17`). -/
public theorem tendsto_cloitreApprox_count_div_length :
    Filter.Tendsto (fun k => ((cloitreApprox k).count 1 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (2 / 3)) ∧
      Filter.Tendsto (fun k => ((cloitreApprox k).count 2 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (1 / 3)) := by
  have hg : Filter.Tendsto (fun k => ((cloitreApprox (k + 2)).length : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro k
    exact_mod_cast (show k ≤ (cloitreApprox (k + 2)).length by
      have := (cloitreApprox_statistics k).2.2
      omega)
  have hi := tendsto_inv_atTop_zero.comp hg
  have h₁ : Filter.Tendsto (fun k => (2 / 3 : ℝ) + (4 / 3) *
      ((cloitreApprox (k + 2)).length : ℝ)⁻¹) Filter.atTop (nhds (2 / 3)) := by
    simpa using (tendsto_const_nhds (x := (2 / 3 : ℝ))).add (hi.const_mul (4 / 3))
  have h₂ : Filter.Tendsto (fun k => (1 / 3 : ℝ) - (4 / 3) *
      ((cloitreApprox (k + 2)).length : ℝ)⁻¹) Filter.atTop (nhds (1 / 3)) := by
    simpa using (tendsto_const_nhds (x := (1 / 3 : ℝ))).sub (hi.const_mul (4 / 3))
  constructor
  · apply (Filter.tendsto_add_atTop_iff_nat 2).mp
    apply h₁.congr
    intro k
    obtain ⟨hc, hl, _⟩ := cloitreApprox_statistics k
    have hn : ((cloitreApprox (k + 2)).length : ℝ) ≠ 0 := by
      have := Nat.cast_nonneg (α := ℝ) ((cloitreApprox (k + 2)).count 2)
      linarith
    field_simp [hn]
    linarith
  · apply (Filter.tendsto_add_atTop_iff_nat 2).mp
    apply h₂.congr
    intro k
    obtain ⟨_, hl, _⟩ := cloitreApprox_statistics k
    have hn : ((cloitreApprox (k + 2)).length : ℝ) ≠ 0 := by
      have := Nat.cast_nonneg (α := ℝ) ((cloitreApprox (k + 2)).count 2)
      linarith
    field_simp [hn]
    linarith

@[expose] public section

-- Evaluation from a starting value.
private def cfEval (l : List ℤ) (y : ℚ) : ℚ :=
  l.foldr (fun (a : ℤ) (x : ℚ) => (a : ℚ) + x⁻¹) y

private theorem cfEval_nil (y : ℚ) : cfEval [] y = y := rfl

private theorem cfEval_cons (c : ℤ) (l : List ℤ) (y : ℚ) :
    cfEval (c :: l) y = (c : ℚ) + (cfEval l y)⁻¹ := rfl

private theorem cfEval_append (l₁ l₂ : List ℤ) (y : ℚ) :
    cfEval (l₁ ++ l₂) y = cfEval l₁ (cfEval l₂ y) := List.foldr_append

private theorem finiteContFrac_eq_cfEval (l : List ℤ) : finiteContFrac l = cfEval l 0 := rfl

-- Matrix for one partial quotient, and their product.
private def cfMat (c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![c, 1; 1, 0]

private def cfMatProd : List ℤ → Matrix (Fin 2) (Fin 2) ℤ
  | l => (l.map cfMat).prod

private theorem cfMatProd_nil : cfMatProd [] = 1 := by
  simp [cfMatProd, List.prod_nil]

private theorem cfMatProd_cons (c : ℤ) (l : List ℤ) :
    cfMatProd (c :: l) = cfMat c * cfMatProd l := by
  simp [cfMatProd, List.map_cons, List.prod_cons]

private theorem cfMatProd_append (l₁ l₂ : List ℤ) :
    cfMatProd (l₁ ++ l₂) = cfMatProd l₁ * cfMatProd l₂ := by
  simp [cfMatProd, List.map_append, List.prod_append]

-- Entries of cfMat.
private theorem cfMat_00 (c : ℤ) : cfMat c 0 0 = c := rfl
private theorem cfMat_01 (c : ℤ) : cfMat c 0 1 = 1 := rfl
private theorem cfMat_10 (c : ℤ) : cfMat c 1 0 = 1 := rfl
private theorem cfMat_11 (c : ℤ) : cfMat c 1 1 = 0 := rfl

-- Entries of a product cfMat c * N.
private theorem mul_cfMat_00 (c : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ) :
    (cfMat c * N) 0 0 = c * N 0 0 + N 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, cfMat_00, cfMat_01]

private theorem mul_cfMat_01 (c : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ) :
    (cfMat c * N) 0 1 = c * N 0 1 + N 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, cfMat_00, cfMat_01]

private theorem mul_cfMat_10 (c : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ) :
    (cfMat c * N) 1 0 = N 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, cfMat_10, cfMat_11]

private theorem mul_cfMat_11 (c : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ) :
    (cfMat c * N) 1 1 = N 0 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, cfMat_10, cfMat_11]

-- Entries of 1.
private theorem one_00 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 :=
  Matrix.one_apply_eq 0
private theorem one_01 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 :=
  Matrix.one_apply_ne (by decide)
private theorem one_10 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 :=
  Matrix.one_apply_ne (by decide)
private theorem one_11 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 :=
  Matrix.one_apply_eq 1

-- Evaluation from a positive start with positive entries stays positive.
private theorem cfEval_pos : ∀ (l : List ℤ) (y : ℚ), (∀ b ∈ l, 1 ≤ b) → 0 < y →
    0 < cfEval l y := by
  intro l; induction l with
  | nil => intro y ha hy; simpa [cfEval_nil] using hy
  | cons c l' ih =>
    intro y ha hy
    rw [cfEval_cons]
    have hc : (0 : ℚ) < (c : ℤ) := by
      exact_mod_cast (show 0 < c from lt_of_lt_of_le zero_lt_one (ha c (by simp)))
    exact add_pos hc (inv_pos.mpr (ih y (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hy))

-- Entries of the product are nonnegative for positive lists.
private theorem matProd_nonneg : ∀ (l : List ℤ), (∀ b ∈ l, 1 ≤ b) →
    0 ≤ cfMatProd l 0 0 ∧ 0 ≤ cfMatProd l 0 1 ∧
    0 ≤ cfMatProd l 1 0 ∧ 0 ≤ cfMatProd l 1 1 := by
  intro l; induction l with
  | nil =>
    intro ha
    rw [cfMatProd_nil]
    simp only [one_00, one_01, one_10, one_11]
    exact ⟨zero_le_one, le_refl 0, le_refl 0, zero_le_one⟩
  | cons c l' ih =>
    intro ha
    obtain ⟨h00, h01, h10, h11⟩ := ih (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hc : (0 : ℤ) ≤ c := zero_le_one.trans (ha c (by simp))
    rw [cfMatProd_cons, mul_cfMat_00, mul_cfMat_01, mul_cfMat_10, mul_cfMat_11]
    exact ⟨add_nonneg (mul_nonneg hc h00) h10, add_nonneg (mul_nonneg hc h01) h11,
      h00, h01⟩

-- The head entry is at least one for nonempty positive lists.
private theorem matProd_head_ge_one : ∀ (l : List ℤ), (∀ b ∈ l, 1 ≤ b) → l ≠ [] →
    1 ≤ cfMatProd l 0 0 := by
  intro l; induction l with
  | nil => intro ha hne; exact absurd rfl hne
  | cons c l' ih =>
    intro ha hne
    have ha' : ∀ b ∈ l', 1 ≤ b := fun b hb => ha b (List.mem_cons_of_mem _ hb)
    cases hl' : l' with
    | nil =>
      subst hl'
      rw [cfMatProd_cons, mul_cfMat_00, cfMatProd_nil, one_00, one_10]
      simpa using ha c (by simp)
    | cons d l'' =>
      subst hl'
      rw [cfMatProd_cons, mul_cfMat_00]
      have h00 : 1 ≤ cfMatProd (d :: l'') 0 0 :=
        ih ha' (by simp)
      have h10 : 0 ≤ cfMatProd (d :: l'') 1 0 :=
        (matProd_nonneg (d :: l'') ha').2.2.1
      have hN00 : 0 ≤ cfMatProd (d :: l'') 0 0 := zero_le_one.trans h00
      have hmul : (1 : ℤ) * cfMatProd (d :: l'') 0 0 ≤
          c * cfMatProd (d :: l'') 0 0 :=
        mul_le_mul_of_nonneg_right (ha c (by simp)) hN00
      have hle : (1 : ℤ) ≤ c * cfMatProd (d :: l'') 0 0 :=
        h00.trans (by simpa using hmul)
      omega

-- A list of length at least two has two head elements.
private theorem cons_cons_of_length_two {α : Type} (l : List α) (h : 2 ≤ l.length) :
    ∃ c d rest, l = c :: d :: rest := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | c :: d :: rest => exact ⟨c, d, rest, rfl⟩

-- Evaluation from a positive start is the Möbius map of the matrix product,
-- with nonzero denominator.
private theorem cfEval_mobius : ∀ (l : List ℤ) (y : ℚ), 0 < y →
    (∀ b ∈ l.drop 1, 1 ≤ b) →
    cfEval l y = (((cfMatProd l 0 0 : ℤ) : ℚ) * y + ((cfMatProd l 0 1 : ℤ) : ℚ)) /
      (((cfMatProd l 1 0 : ℤ) : ℚ) * y + ((cfMatProd l 1 1 : ℤ) : ℚ)) ∧
    (((cfMatProd l 1 0 : ℤ) : ℚ) * y + ((cfMatProd l 1 1 : ℤ) : ℚ)) ≠ 0 := by
  intro l; induction l with
  | nil =>
    intro y hy ha
    rw [cfEval_nil, cfMatProd_nil, one_00, one_01, one_10, one_11]
    refine ⟨?_, ?_⟩ <;> simp
  | cons c l' ih =>
    intro y hy ha
    have ha' : ∀ b ∈ l'.drop 1, 1 ≤ b :=
      fun b hb => ha b (by simpa using List.mem_of_mem_drop hb)
    have hal : ∀ b ∈ l', 1 ≤ b := fun b hb => ha b (by simpa using hb)
    obtain ⟨ihEq, ihNe⟩ := ih y hy ha'
    have hEpos : 0 < cfEval l' y := cfEval_pos l' y hal hy
    have hEne : cfEval l' y ≠ 0 := ne_of_gt hEpos
    have hEnum : (((cfMatProd l' 0 0 : ℤ) : ℚ) * y +
        ((cfMatProd l' 0 1 : ℤ) : ℚ)) ≠ 0 := by
      intro hcon
      apply hEne
      rw [ihEq, hcon, zero_div]
    rw [cfEval_cons, cfMatProd_cons, mul_cfMat_00, mul_cfMat_01, mul_cfMat_10,
      mul_cfMat_11, ihEq]
    simp only [Int.cast_add, Int.cast_mul]
    refine ⟨?_, hEnum⟩
    field_simp
    ring

-- A continued fraction is the ratio of the head column of the product,
-- with positive denominator.
private theorem contFrac_eq_ratio : ∀ (m : List ℤ), m ≠ [] →
    (∀ b ∈ m.drop 1, 1 ≤ b) →
    finiteContFrac m = (((cfMatProd m 0 0 : ℤ) : ℚ)) / (((cfMatProd m 1 0 : ℤ) : ℚ)) ∧
    0 < cfMatProd m 1 0 := by
  intro m; induction m with
  | nil => intro hne ha; exact absurd rfl hne
  | cons c l' ih =>
    intro hne ha
    cases hl' : l' with
    | nil =>
      subst hl'
      rw [finiteContFrac_singleton, cfMatProd_cons, cfMatProd_nil, mul_one, cfMat_00,
        cfMat_10]
      exact ⟨by simp, zero_lt_one⟩
    | cons d l'' =>
      subst hl'
      have ha' : ∀ b ∈ List.drop 1 (d :: l''), 1 ≤ b :=
        fun b hb => ha b (by simpa using List.mem_of_mem_drop hb)
      obtain ⟨ihEq, ihPos⟩ := ih (by simp) ha'
      have hN00 : (0 : ℤ) < cfMatProd (d :: l'') 0 0 :=
        lt_of_lt_of_le zero_lt_one
          (matProd_head_ge_one (d :: l'') (fun b hb => ha b (by simpa using hb))
            (by simp))
      rw [finiteContFrac_cons, cfMatProd_cons, mul_cfMat_00, mul_cfMat_10, ihEq]
      refine ⟨?_, hN00⟩
      simp only [Int.cast_add, Int.cast_mul]
      have hN00' : (((cfMatProd (d :: l'') 0 0 : ℤ)) : ℚ) ≠ 0 :=
        by exact_mod_cast ne_of_gt hN00
      have hN10' : (((cfMatProd (d :: l'') 1 0 : ℤ)) : ℚ) ≠ 0 :=
        by exact_mod_cast ne_of_gt ihPos
      field_simp

-- The determinant of the product is (-1)^length.
private theorem matProd_det : ∀ (l : List ℤ), (cfMatProd l).det = (-1 : ℤ) ^ l.length := by
  intro l; induction l with
  | nil => simp [cfMatProd_nil, Matrix.det_one]
  | cons c l' ih =>
    have hdet : (cfMat c).det = -1 := by
      have hcf : cfMat c = !![c, 1; 1, (0 : ℤ)] := rfl
      rw [hcf, Matrix.det_fin_two_of]
      ring
    rw [cfMatProd_cons, Matrix.det_mul, ih, hdet, List.length_cons, pow_succ]
    ring

-- Each factor is symmetric.
private theorem cfMat_transpose (c : ℤ) : (cfMat c).transpose = cfMat c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, cfMat_00, cfMat_01, cfMat_10, cfMat_11]

-- Reversing the list transposes the product.
private theorem matProd_reverse : ∀ (l : List ℤ),
    cfMatProd l.reverse = (cfMatProd l).transpose := by
  intro l; induction l with
  | nil => rw [List.reverse_nil, cfMatProd_nil, Matrix.transpose_one]
  | cons c l' ih =>
    simp only [List.reverse_cons, cfMatProd_append, cfMatProd_cons, cfMatProd_nil,
      mul_one, Matrix.transpose_mul, ih, cfMat_transpose]

/-- **Folding lemma for finite continued fractions.** Let $a_0$ be an integer, let $t$ be even
and let $a_1, \dots, a_t$ be integers with $a_i \ge 1$ for every $i$, and let $q$ be the
denominator in lowest terms of the value $[a_0; a_1, \dots, a_t]$ of the finite continued
fraction. Then for every integer $x \ge 1$,
$[a_0; a_1, \dots, a_t] + 1/(x q^2) = [a_0; a_1, \dots, a_t, x, -a_t, \dots, -a_1]$.

For positive partial quotients, $q$ is the continuant $q_t$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:fold`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem finiteContFrac_add_inv_mul_den_sq (a₀ : ℤ) (a : List ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ht : Even a.length) (x : ℕ) (hx : 1 ≤ x) :
    finiteContFrac (a₀ :: a) + 1 / (x * ((finiteContFrac (a₀ :: a)).den : ℚ) ^ 2) =
      finiteContFrac (a₀ :: a ++ (x : ℤ) :: (a.map (fun b => -b)).reverse) := by
  by_cases ha_nil : a = []
  · subst ha_nil
    rw [List.cons_append, List.nil_append, List.map_nil, List.reverse_nil,
      finiteContFrac_singleton, finiteContFrac_cons, finiteContFrac_singleton,
      Rat.den_intCast]
    congr 1
    simp [one_div]
  · obtain ⟨k, hk⟩ := ht
    have hlen0 : a.length ≠ 0 :=
      fun h => ha_nil (List.eq_nil_of_length_eq_zero h)
    have hlen2 : 2 ≤ a.length := by omega
    have hdrop : ∀ (c : ℤ) (l : List ℤ), List.drop 1 (c :: l) = l := fun c l => rfl
    have ha_drop : ∀ b ∈ List.drop 1 (a₀ :: a), 1 ≤ b := by
      intro b hb; rw [hdrop] at hb; exact ha b hb
    obtain ⟨hF0, hQpos⟩ := contFrac_eq_ratio (a₀ :: a) (by simp) ha_drop
    have hdet : cfMatProd (a₀ :: a) 0 0 * cfMatProd (a₀ :: a) 1 1 -
        cfMatProd (a₀ :: a) 0 1 * cfMatProd (a₀ :: a) 1 0 = -1 := by
      have h := matProd_det (a₀ :: a)
      rw [Matrix.det_fin_two, List.length_cons, hk] at h
      have hodd : Odd (k + k + 1) := ⟨k, by ring⟩
      rw [hodd.neg_one_pow] at h
      exact h
    have hcop : IsCoprime (cfMatProd (a₀ :: a) 0 0) (cfMatProd (a₀ :: a) 1 0) :=
      ⟨-(cfMatProd (a₀ :: a) 1 1), cfMatProd (a₀ :: a) 0 1, by
        linear_combination -hdet⟩
    have hcopN : Nat.Coprime (cfMatProd (a₀ :: a) 0 0).natAbs
        (cfMatProd (a₀ :: a) 1 0).natAbs :=
      Int.isCoprime_iff_nat_coprime.mp hcop
    have hden : (((finiteContFrac (a₀ :: a)).den : ℕ) : ℤ) =
        cfMatProd (a₀ :: a) 1 0 := by
      rw [hF0]
      exact Rat.den_div_eq_of_coprime hQpos hcopN
    have hdenQ : (((finiteContFrac (a₀ :: a)).den : ℕ) : ℚ) =
        ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ) := by exact_mod_cast hden
    have hrev_ne : a.reverse ≠ [] :=
      fun h => ha_nil (List.reverse_eq_nil_iff.mp h)
    have ha_rev : ∀ b ∈ List.drop 1 a.reverse, 1 ≤ b := by
      intro b hb; exact ha b (List.mem_reverse.mp (List.mem_of_mem_drop hb))
    obtain ⟨hU, hR'pos⟩ := contFrac_eq_ratio a.reverse hrev_ne ha_rev
    have hR : 1 ≤ cfMatProd a.reverse 0 0 :=
      matProd_head_ge_one a.reverse
        (fun b hb => ha b (List.mem_reverse.mp hb)) hrev_ne
    obtain ⟨c, d, rest, hrev⟩ := cons_cons_of_length_two a.reverse (by
      rw [List.length_reverse]; exact hlen2)
    have hUgt1 : (1 : ℚ) < finiteContFrac a.reverse := by
      rw [hrev, finiteContFrac_cons]
      have hca : c ∈ a :=
        List.mem_reverse.mp (by rw [hrev]; simp)
      have hc1 : (1 : ℚ) ≤ ((c : ℤ) : ℚ) := by exact_mod_cast ha c hca
      have hFrest : 0 < finiteContFrac (d :: rest) :=
        finiteContFrac_neg_block.pos (d :: rest) (by
          intro b hb
          have hmem : b ∈ a.reverse := by
            rw [hrev]; exact List.mem_cons_of_mem c hb
          exact ha b (List.mem_reverse.mp hmem)) (by simp)
      have hpos : (0 : ℚ) < (finiteContFrac (d :: rest))⁻¹ := inv_pos.mpr hFrest
      linarith
    have hRne : (((cfMatProd a.reverse 0 0 : ℤ)) : ℚ) ≠ 0 := by
      exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
    have hR'ne : (((cfMatProd a.reverse 1 0 : ℤ)) : ℚ) ≠ 0 := by
      exact_mod_cast ne_of_gt hR'pos
    have hW : finiteContFrac ((x : ℤ) :: (a.map (fun b => -b)).reverse) =
        (x : ℚ) - ((cfMatProd a.reverse 1 0 : ℤ) : ℚ) /
          ((cfMatProd a.reverse 0 0 : ℤ) : ℚ) := by
      rw [finiteContFrac_cons, ← List.map_reverse, finiteContFrac_neg_block.map_neg, hU,
        sub_eq_add_neg]
      push_cast
      congr 1
      field_simp
    have hU1 : (1 : ℚ) < ((cfMatProd a.reverse 0 0 : ℤ) : ℚ) /
        ((cfMatProd a.reverse 1 0 : ℤ) : ℚ) := by rw [← hU]; exact hUgt1
    have hfrac : ((cfMatProd a.reverse 1 0 : ℤ) : ℚ) /
        ((cfMatProd a.reverse 0 0 : ℤ) : ℚ) < 1 := by
      have h1 : (1 : ℚ) < ((cfMatProd a.reverse 0 0 : ℤ) : ℚ) /
          ((cfMatProd a.reverse 1 0 : ℤ) : ℚ) := hU1
      field_simp at h1 ⊢
      linarith
    have hxQ : (1 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
    have hWpos : 0 < finiteContFrac ((x : ℤ) :: (a.map (fun b => -b)).reverse) := by
      rw [hW]; linarith
    have hRHS : finiteContFrac ((a₀ :: a) ++ (x : ℤ) :: (a.map (fun b => -b)).reverse) =
        cfEval (a₀ :: a)
          (finiteContFrac ((x : ℤ) :: (a.map (fun b => -b)).reverse)) := by
      rw [finiteContFrac_eq_cfEval, cfEval_append, ← finiteContFrac_eq_cfEval]
    obtain ⟨hRHSval, -⟩ := cfEval_mobius (a₀ :: a)
      (finiteContFrac ((x : ℤ) :: (a.map (fun b => -b)).reverse)) hWpos ha_drop
    have hR : cfMatProd a.reverse 0 0 = cfMatProd (a₀ :: a) 1 0 := by
      rw [matProd_reverse, Matrix.transpose_apply, cfMatProd_cons, mul_cfMat_10]
    have hR' : cfMatProd a.reverse 1 0 = cfMatProd (a₀ :: a) 1 1 := by
      rw [matProd_reverse, Matrix.transpose_apply, cfMatProd_cons, mul_cfMat_11]
    have hQne : (((cfMatProd (a₀ :: a) 1 0 : ℤ)) : ℚ) ≠ 0 :=
      by exact_mod_cast ne_of_gt hQpos
    have hxQne : ((x : ℚ)) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
    have hdetQ : ((cfMatProd (a₀ :: a) 0 0 : ℤ) : ℚ) *
          ((cfMatProd (a₀ :: a) 1 1 : ℤ) : ℚ) -
          ((cfMatProd (a₀ :: a) 0 1 : ℤ) : ℚ) *
          ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ) = -1 := by
      exact_mod_cast hdet
    have hD : ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ) *
          ((x : ℚ) - ((cfMatProd (a₀ :: a) 1 1 : ℤ) : ℚ) /
            ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ)) +
          ((cfMatProd (a₀ :: a) 1 1 : ℤ) : ℚ) =
          (x : ℚ) * ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ) := by
      field_simp
      ring
    have hN : ((cfMatProd (a₀ :: a) 0 0 : ℤ) : ℚ) *
          ((x : ℚ) - ((cfMatProd (a₀ :: a) 1 1 : ℤ) : ℚ) /
            ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ)) +
          ((cfMatProd (a₀ :: a) 0 1 : ℤ) : ℚ) =
          ((x : ℚ) * ((cfMatProd (a₀ :: a) 0 0 : ℤ) : ℚ) *
            ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ) + 1) /
          ((cfMatProd (a₀ :: a) 1 0 : ℤ) : ℚ) := by
      field_simp
      linear_combination -hdetQ
    rw [hRHS, hRHSval, hW, hR, hR', hdenQ, hF0, hD, hN]
    field_simp

end

end MetaMathlibExt
