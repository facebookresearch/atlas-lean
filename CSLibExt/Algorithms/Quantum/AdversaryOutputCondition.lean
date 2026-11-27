/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Hadamard
import MathlibExt.Analysis.InnerProductSpace.SchurGramBound
import Mathlib.Analysis.Matrix.PosDef

/-!
# Adversary output condition

The final-state Gram-matrix bound used in the generalized adversary method.
The abstract form below follows Ronald de Wolf, Quantum Computing: Lecture
Notes, arXiv:1907.09415, Chapter 12.1, Claim 1 and Exercise 2. The final
states are decomposed into their two output components; no query model is
defined or consumed here.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator BigOperators InnerProductSpace

namespace Cslib.AdversaryOutputCondition

set_option autoImplicit false

/-- An adversary matrix for `f` is real symmetric and vanishes on pairs with
the same output. -/
def IsAdversaryMatrix {X : Type*} (f : X → Bool) (Γ : Matrix X X ℝ) : Prop :=
  Γ.IsSymm ∧ ∀ x y, f x = f y → Γ x y = 0

/-- Squares preserve `≤` on nonnegative reals. -/
private theorem sq_le_sq_of_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [ha, hab,
    mul_nonneg (show (0 : ℝ) ≤ b - a by linarith)
      (show (0 : ℝ) ≤ b + a by linarith)]

/-- Analytic core of the pairwise output bound: two cross terms with
complementary correct/wrong weights. -/
private theorem aux_sum_le (P Q a b ε : ℝ) (hP0 : 0 ≤ P)
    (hQ0 : 0 ≤ Q) (hP : P ^ 2 ≤ (1 - a) * b)
    (hQ : Q ^ 2 ≤ a * (1 - b)) (ha0 : 0 ≤ a) (ha : a ≤ ε)
    (hb0 : 0 ≤ b) (hb : b ≤ ε) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) : P + Q ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  have hsum : P ^ 2 + Q ^ 2 ≤ 2 * (ε * (1 - ε)) := by
    nlinarith [hP, hQ,
      mul_nonneg (show (0 : ℝ) ≤ ε - a by linarith)
        (show (0 : ℝ) ≤ ε - b by linarith),
      mul_nonneg (show (0 : ℝ) ≤ ε - a by linarith)
        (show (0 : ℝ) ≤ 1 - 2 * ε by linarith),
      mul_nonneg (show (0 : ℝ) ≤ ε - b by linarith)
        (show (0 : ℝ) ≤ 1 - 2 * ε by linarith)]
  have h2sq : (P + Q) ^ 2 ≤ 2 * (P ^ 2 + Q ^ 2) := by
    nlinarith [sq_nonneg (P - Q)]
  have hm0 : 0 ≤ ε * (1 - ε) := mul_nonneg hε0 (by linarith)
  have hsqrt : (2 * Real.sqrt (ε * (1 - ε))) ^ 2 = 4 * (ε * (1 - ε)) := by
    rw [mul_pow, Real.sq_sqrt hm0]
    ring
  have hfin : (P + Q) ^ 2 ≤ (2 * Real.sqrt (ε * (1 - ε))) ^ 2 := by
    rw [hsqrt]
    linarith [h2sq, hsum]
  have hPQ0 : 0 ≤ P + Q := by linarith
  calc P + Q = Real.sqrt ((P + Q) ^ 2) := (Real.sqrt_sq hPQ0).symm
    _ ≤ Real.sqrt ((2 * Real.sqrt (ε * (1 - ε))) ^ 2) :=
        Real.sqrt_le_sqrt hfin
    _ = 2 * Real.sqrt (ε * (1 - ε)) := Real.sqrt_sq (by positivity)

/-- For inputs with different outputs, only the two cross terms between the
output components survive. -/
theorem inner_eq_cross_terms {X E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : X → Bool) (ψ : X → E) (u : Bool → X → E)
    (hdecomp : ∀ x, ψ x = u false x + u true x)
    (hortho : ∀ x y, inner ℂ (u false x) (u true y) = 0)
    {x y : X} (hxy : f x ≠ f y) :
    inner ℂ (ψ x) (ψ y) =
      inner ℂ (u (f x) x) (u (f x) y) +
        inner ℂ (u (f y) x) (u (f y) y) := by
  have hTF : ∀ a b, inner ℂ (u true a) (u false b) = 0 := by
    intro a b
    have h := inner_conj_symm (𝕜 := ℂ) (u true a) (u false b)
    simp only [hortho b a] at h
    first | simpa using h.symm | simpa using h
  have hexpand : inner ℂ (ψ x) (ψ y) =
      inner ℂ (u false x) (u false y) +
        inner ℂ (u true x) (u true y) := by
    simp only [hdecomp x, hdecomp y, inner_add_left, inner_add_right,
      hortho x y, hTF x y, add_zero, zero_add]
  rw [hexpand]
  cases hfx : f x <;> cases hfy : f y
  · exact absurd (hfx.trans hfy.symm) hxy
  · rfl
  · exact add_comm _ _
  · exact absurd (hfx.trans hfy.symm) hxy

/-- Pairwise form of the output condition. -/
theorem norm_inner_le_of_ne {X E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : X → Bool) (ψ : X → E) (u : Bool → X → E)
    (hdecomp : ∀ x, ψ x = u false x + u true x)
    (hortho : ∀ x y, inner ℂ (u false x) (u true y) = 0)
    (hunit : ∀ x, ‖ψ x‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (herr : ∀ x, ‖u (!f x) x‖ ^ 2 ≤ ε)
    {x y : X} (hxy : f x ≠ f y) :
    ‖inner ℂ (ψ x) (ψ y)‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  have hpy : ∀ z, ‖u false z‖ ^ 2 + ‖u true z‖ ^ 2 = 1 := by
    intro z
    have hns := norm_add_sq (𝕜 := ℂ) (u false z) (u true z)
    have h0 : RCLike.re (inner ℂ (u false z) (u true z)) = 0 := by
      rw [hortho z z]
      simp
    simp only [h0, mul_zero, zero_mul, add_zero, zero_add] at hns
    rw [← hdecomp z, hunit z] at hns
    simpa using hns.symm
  cases hfx : f x <;> cases hfy : f y
  · exact absurd (hfx.trans hfy.symm) hxy
  · have hT := inner_eq_cross_terms f ψ u hdecomp hortho hxy
    rw [hfx, hfy] at hT
    rw [hT]
    have ha : ‖u true x‖ ^ 2 ≤ ε := by
      have h := herr x
      rw [hfx] at h
      simpa using h
    have hb : ‖u false y‖ ^ 2 ≤ ε := by
      have h := herr y
      rw [hfy] at h
      simpa using h
    have hc₁ : ‖u false x‖ ^ 2 = 1 - ‖u true x‖ ^ 2 := by
      linarith [hpy x]
    have hc₂ : ‖u true y‖ ^ 2 = 1 - ‖u false y‖ ^ 2 := by
      linarith [hpy y]
    have hT1 : ‖inner ℂ (u false x) (u false y)‖ ≤
        ‖u false x‖ * ‖u false y‖ := norm_inner_le_norm _ _
    have hT2 : ‖inner ℂ (u true x) (u true y)‖ ≤
        ‖u true x‖ * ‖u true y‖ := norm_inner_le_norm _ _
    have hP : ‖inner ℂ (u false x) (u false y)‖ ^ 2 ≤
        (1 - ‖u true x‖ ^ 2) * ‖u false y‖ ^ 2 := by
      have h := sq_le_sq_of_le_of_nonneg (norm_nonneg _) hT1
      rwa [mul_pow, hc₁] at h
    have hQ : ‖inner ℂ (u true x) (u true y)‖ ^ 2 ≤
        ‖u true x‖ ^ 2 * (1 - ‖u false y‖ ^ 2) := by
      have h := sq_le_sq_of_le_of_nonneg (norm_nonneg _) hT2
      rwa [mul_pow, hc₂] at h
    refine le_trans (norm_add_le _ _)
      (aux_sum_le _ _ _ _ _ ?_ ?_ hP hQ ?_ ha ?_ hb hε0 hε) <;> positivity
  · have hT := inner_eq_cross_terms f ψ u hdecomp hortho hxy
    rw [hfx, hfy] at hT
    rw [hT]
    have ha : ‖u false x‖ ^ 2 ≤ ε := by
      have h := herr x
      rw [hfx] at h
      simpa using h
    have hb : ‖u true y‖ ^ 2 ≤ ε := by
      have h := herr y
      rw [hfy] at h
      simpa using h
    have hc₁ : ‖u true x‖ ^ 2 = 1 - ‖u false x‖ ^ 2 := by
      linarith [hpy x]
    have hc₂ : ‖u false y‖ ^ 2 = 1 - ‖u true y‖ ^ 2 := by
      linarith [hpy y]
    have hT1 : ‖inner ℂ (u true x) (u true y)‖ ≤
        ‖u true x‖ * ‖u true y‖ := norm_inner_le_norm _ _
    have hT2 : ‖inner ℂ (u false x) (u false y)‖ ≤
        ‖u false x‖ * ‖u false y‖ := norm_inner_le_norm _ _
    have hP : ‖inner ℂ (u true x) (u true y)‖ ^ 2 ≤
        (1 - ‖u false x‖ ^ 2) * ‖u true y‖ ^ 2 := by
      have h := sq_le_sq_of_le_of_nonneg (norm_nonneg _) hT1
      rwa [mul_pow, hc₁] at h
    have hQ : ‖inner ℂ (u false x) (u false y)‖ ^ 2 ≤
        ‖u false x‖ ^ 2 * (1 - ‖u true y‖ ^ 2) := by
      have h := sq_le_sq_of_le_of_nonneg (norm_nonneg _) hT2
      rwa [mul_pow, hc₂] at h
    refine le_trans (norm_add_le _ _)
      (aux_sum_le _ _ _ _ _ ?_ ?_ hP hQ ?_ ha ?_ hb hε0 hε) <;> positivity
  · exact absurd (hfx.trans hfy.symm) hxy

/-- Bilinear bound for `A ⊗ Id` against two families. -/
private theorem bilin_le {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix X X ℂ) (p q : X → E) :
    ‖∑ x, inner ℂ (p x) (∑ y, A x y • q y)‖ ≤
      ‖A‖ * Real.sqrt (∑ x, ‖p x‖ ^ 2) * Real.sqrt (∑ x, ‖q x‖ ^ 2) := by
  have h1 : ‖∑ x, inner ℂ (p x) (∑ y, A x y • q y)‖ ≤
      ∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
    exact norm_inner_le_norm _ _
  have hCS : (∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖) ^ 2 ≤
      (∑ x, ‖p x‖ ^ 2) * (∑ x, ‖∑ y, A x y • q y‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnn : 0 ≤ ∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖ :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hP : 0 ≤ ∑ x, ‖p x‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hB : 0 ≤ ∑ x, ‖∑ y, A x y • q y‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hQ0 : (∑ x, ‖∑ y, A x y • q y‖ ^ 2) ≤ ‖A‖ ^ 2 * ∑ x, ‖q x‖ ^ 2 :=
    MathlibExt.Analysis.InnerProductSpace.SchurGramBound.keyEstimate A q
  have hsqrt : ∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖ ≤
      Real.sqrt (∑ x, ‖p x‖ ^ 2) * Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2) := by
    have e : (Real.sqrt (∑ x, ‖p x‖ ^ 2) *
        Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2)) ^ 2 =
        (∑ x, ‖p x‖ ^ 2) * (∑ x, ‖∑ y, A x y • q y‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hP, Real.sq_sqrt hB]
    have hle : (∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖) ^ 2 ≤
        (Real.sqrt (∑ x, ‖p x‖ ^ 2) *
          Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2)) ^ 2 := by
      rw [e]
      exact hCS
    have h0 : 0 ≤ Real.sqrt (∑ x, ‖p x‖ ^ 2) *
        Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc ∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖
        = Real.sqrt ((∑ x, ‖p x‖ * ‖∑ y, A x y • q y‖) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((Real.sqrt (∑ x, ‖p x‖ ^ 2) *
          Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = Real.sqrt (∑ x, ‖p x‖ ^ 2) *
          Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2) := Real.sqrt_sq h0
  have hBsqrt : Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2) ≤
      ‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2) := by
    have e : (‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2)) ^ 2 =
        ‖A‖ ^ 2 * ∑ x, ‖q x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun x _ => sq_nonneg _))]
    have hle : (Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2)) ^ 2 ≤
        (‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt hB, e]
      exact hQ0
    have h0 : 0 ≤ ‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2) :=
      mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2)
        = Real.sqrt ((Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2)) ^ 2) :=
          (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
      _ ≤ Real.sqrt ((‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = ‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2) := Real.sqrt_sq h0
  calc ‖∑ x, inner ℂ (p x) (∑ y, A x y • q y)‖
      ≤ Real.sqrt (∑ x, ‖p x‖ ^ 2) *
        Real.sqrt (∑ x, ‖∑ y, A x y • q y‖ ^ 2) := le_trans h1 hsqrt
    _ ≤ Real.sqrt (∑ x, ‖p x‖ ^ 2) * (‖A‖ * Real.sqrt (∑ x, ‖q x‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hBsqrt (Real.sqrt_nonneg _)
    _ = ‖A‖ * Real.sqrt (∑ x, ‖p x‖ ^ 2) * Real.sqrt (∑ x, ‖q x‖ ^ 2) := by ring

/-- Output-split bilinear bound for adversary-supported kernels. -/
private theorem bilin_output_le {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : X → Bool) (A : Matrix X X ℂ)
    (hA0 : ∀ x y, f x = f y → A x y = 0) (a : X → E) :
    ‖∑ x, ∑ y, A x y * inner ℂ (a x) (a y)‖ ≤
      2 * ‖A‖ * Real.sqrt (∑ x, if f x = false then ‖a x‖ ^ 2 else 0) *
        Real.sqrt (∑ x, if f x = true then ‖a x‖ ^ 2 else 0) := by
  set a0 : X → E := fun x => if f x = false then a x else 0 with ha0
  set a1 : X → E := fun x => if f x = true then a x else 0 with ha1
  have hterm : ∀ x y, A x y * inner ℂ (a x) (a y) =
      A x y * inner ℂ (a0 x) (a1 y) + A x y * inner ℂ (a1 x) (a0 y) := by
    intro x y
    by_cases hxy : f x = f y
    · have h0 : A x y = 0 := hA0 x y hxy
      rw [h0]
      simp only [zero_mul, add_zero]
    · cases hfx : f x <;> cases hfy : f y
      · exact absurd (hfx.trans hfy.symm) hxy
      · have e1 : a0 x = a x := by simp [ha0, hfx]
        have e2 : a1 y = a y := by simp [ha1, hfy]
        have e3 : a1 x = 0 := by simp [ha1, hfx]
        have e4 : a0 y = 0 := by simp [ha0, hfy]
        rw [e1, e2, e3, e4]
        simp
      · have e1 : a1 x = a x := by simp [ha1, hfx]
        have e2 : a0 y = a y := by simp [ha0, hfy]
        have e3 : a0 x = 0 := by simp [ha0, hfx]
        have e4 : a1 y = 0 := by simp [ha1, hfy]
        rw [e1, e2, e3, e4]
        simp
      · exact absurd (hfx.trans hfy.symm) hxy
  have hSeq : (∑ x, ∑ y, A x y * inner ℂ (a x) (a y)) =
      (∑ x, ∑ y, A x y * inner ℂ (a0 x) (a1 y)) +
      (∑ x, ∑ y, A x y * inner ℂ (a1 x) (a0 y)) := by
    have hcongr : (∑ x, ∑ y, A x y * inner ℂ (a x) (a y)) =
        ∑ x, ∑ y, (A x y * inner ℂ (a0 x) (a1 y) +
          A x y * inner ℂ (a1 x) (a0 y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hterm x y
    have hsplit : (∑ x, ∑ y, (A x y * inner ℂ (a0 x) (a1 y) +
        A x y * inner ℂ (a1 x) (a0 y))) =
        (∑ x, ∑ y, A x y * inner ℂ (a0 x) (a1 y)) +
        (∑ x, ∑ y, A x y * inner ℂ (a1 x) (a0 y)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_add_distrib
    exact hcongr.trans hsplit
  have hT1 : (∑ x, ∑ y, A x y * inner ℂ (a0 x) (a1 y)) =
      ∑ x, inner ℂ (a0 x) (∑ y, A x y • a1 y) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact (inner_smul_right _ _ _).symm
  have hT2 : (∑ x, ∑ y, A x y * inner ℂ (a1 x) (a0 y)) =
      ∑ x, inner ℂ (a1 x) (∑ y, A x y • a0 y) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact (inner_smul_right _ _ _).symm
  have n0 : (∑ x, ‖a0 x‖ ^ 2) =
      ∑ x, if f x = false then ‖a x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · simp only [ha0]
      rw [if_pos h]
    · simp only [ha0]
      rw [if_neg h]
      simp
  have n1 : (∑ x, ‖a1 x‖ ^ 2) =
      ∑ x, if f x = true then ‖a x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · simp only [ha1]
      rw [if_pos h]
    · simp only [ha1]
      rw [if_neg h]
      simp
  have b1 := bilin_le A a0 a1
  have b2 := bilin_le A a1 a0
  rw [hSeq]
  refine le_trans (norm_add_le _ _) ?_
  rw [hT1, hT2]
  calc ‖∑ x, inner ℂ (a0 x) (∑ y, A x y • a1 y)‖ +
        ‖∑ x, inner ℂ (a1 x) (∑ y, A x y • a0 y)‖
      ≤ (‖A‖ * Real.sqrt (∑ x, ‖a0 x‖ ^ 2) * Real.sqrt (∑ x, ‖a1 x‖ ^ 2)) +
        (‖A‖ * Real.sqrt (∑ x, ‖a1 x‖ ^ 2) * Real.sqrt (∑ x, ‖a0 x‖ ^ 2)) :=
        add_le_add b1 b2
    _ = 2 * ‖A‖ * Real.sqrt (∑ x, ‖a0 x‖ ^ 2) *
        Real.sqrt (∑ x, ‖a1 x‖ ^ 2) := by ring
    _ = 2 * ‖A‖ * Real.sqrt (∑ x, if f x = false then ‖a x‖ ^ 2 else 0) *
        Real.sqrt (∑ x, if f x = true then ‖a x‖ ^ 2 else 0) := by
        rw [n0, n1]

private theorem adversary_sqrt_two_mul_le_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2 * Real.sqrt (p * q) ≤ p + q := by
  have h := sq_nonneg (Real.sqrt p - Real.sqrt q)
  rw [sub_sq, Real.sq_sqrt hp, Real.sq_sqrt hq] at h
  have hmul : Real.sqrt p * Real.sqrt q = Real.sqrt (p * q) := by
    rw [Real.sqrt_mul hp q]
  have h2 : 2 * Real.sqrt p * Real.sqrt q = 2 * Real.sqrt (p * q) := by
    rw [mul_assoc, hmul]
  rw [h2] at h
  linarith

private theorem adversary_sqrt_add_mul_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d ≤
      Real.sqrt ((a + c) * (b + d)) := by
  have hnn : 0 ≤ Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d := by
    positivity
  have hsq : (Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d) ^ 2 ≤
      (a + c) * (b + d) := by
    have e1 : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
      rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
    have e2 : (Real.sqrt c * Real.sqrt d) ^ 2 = c * d := by
      rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hd]
    have e3 : 2 * (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) ≤
        a * d + c * b := by
      have hprod : (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) =
          Real.sqrt ((a * d) * (c * b)) := by
        have r1 : Real.sqrt a * Real.sqrt d = Real.sqrt (a * d) := by
          rw [Real.sqrt_mul ha d]
        have r2 : Real.sqrt c * Real.sqrt b = Real.sqrt (c * b) := by
          rw [Real.sqrt_mul hc b]
        calc (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d)
            = (Real.sqrt a * Real.sqrt d) * (Real.sqrt c * Real.sqrt b) := by ring
          _ = Real.sqrt (a * d) * Real.sqrt (c * b) := by rw [r1, r2]
          _ = Real.sqrt ((a * d) * (c * b)) := by
              rw [Real.sqrt_mul (mul_nonneg ha hd) (c * b)]
      have hfactor : 2 * (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) =
          2 * ((Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d)) := by ring
      rw [hfactor, hprod]
      have ham := adversary_sqrt_two_mul_le_add (mul_nonneg ha hd) (mul_nonneg hc hb)
      linarith
    calc (Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d) ^ 2
        = (Real.sqrt a * Real.sqrt b) ^ 2 +
          2 * (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) +
          (Real.sqrt c * Real.sqrt d) ^ 2 := by ring
      _ ≤ a * b + (a * d + c * b) + c * d :=
          add_le_add (add_le_add (le_of_eq e1) e3) (le_of_eq e2)
      _ = (a + c) * (b + d) := by ring
  calc Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d
      = Real.sqrt ((Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d) ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt ((a + c) * (b + d)) := by
        apply Real.sqrt_le_sqrt
        exact hsq

private theorem adversary_mul_one_sub_le {q ε : ℝ}
    (_hq0 : 0 ≤ q) (hqε : q ≤ ε) (hε : ε ≤ 1 / 2) :
    q * (1 - q) ≤ ε * (1 - ε) := by
  have h1 : 0 ≤ ε - q := sub_nonneg.mpr hqε
  have h2 : 0 ≤ 1 - ε - q := by linarith
  have h3 : 0 ≤ (ε - q) * (1 - ε - q) := mul_nonneg h1 h2
  linarith

/-- Quadratic-form form of the adversary output condition. -/
theorem adversary_quadForm_le {X E : Type*}
    [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : X → Bool) (ψ : X → E) (u : Bool → X → E)
    (hdecomp : ∀ x, ψ x = u false x + u true x)
    (hortho : ∀ x y, inner ℂ (u false x) (u true y) = 0)
    (hunit : ∀ x, ‖ψ x‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (herr : ∀ x, ‖u (!f x) x‖ ^ 2 ≤ ε)
    (Γ : Matrix X X ℝ) (hΓ : IsAdversaryMatrix f Γ)
    (α : X → ℂ) (hα : ∑ x, ‖α x‖ ^ 2 = 1) :
    ‖∑ x, ∑ y, ((Γ x y : ℝ) : ℂ) * star (α x) * α y *
      inner ℂ (ψ x) (ψ y)‖ ≤
        2 * Real.sqrt (ε * (1 - ε)) *
          ‖Γ.map (fun r : ℝ => (r : ℂ))‖ := by
  have _ := hε0
  set A : Matrix X X ℂ := Γ.map (fun r : ℝ => (r : ℂ)) with hA
  set a0 : X → E := fun x => α x • u false x with ha0
  set a1 : X → E := fun x => α x • u true x with ha1
  have hA0 : ∀ x y, f x = f y → A x y = 0 := by
    intro x y hxy
    have h0 : Γ x y = 0 := hΓ.2 x y hxy
    simp [hA, h0]
  have e0 : ∀ x y, inner ℂ (a0 x) (a0 y) =
      star (α x) * α y * inner ℂ (u false x) (u false y) := by
    intro x y
    rw [ha0]
    simp only []
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply]
    ring
  have e1 : ∀ x y, inner ℂ (a1 x) (a1 y) =
      star (α x) * α y * inner ℂ (u true x) (u true y) := by
    intro x y
    rw [ha1]
    simp only []
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply]
    ring
  have hterm : ∀ x y, ((Γ x y : ℝ) : ℂ) * star (α x) * α y *
        inner ℂ (ψ x) (ψ y) =
        A x y * inner ℂ (a0 x) (a0 y) + A x y * inner ℂ (a1 x) (a1 y) := by
    intro x y
    rw [e0 x y, e1 x y]
    have hAxy : A x y = ((Γ x y : ℝ) : ℂ) := by rw [hA]; rfl
    by_cases hxy : f x = f y
    · have h0 : Γ x y = 0 := hΓ.2 x y hxy
      rw [hAxy, h0]
      simp
    · have hT := inner_eq_cross_terms f ψ u hdecomp hortho hxy
      rw [hAxy]
      cases hfx : f x <;> cases hfy : f y
      · exact absurd (hfx.trans hfy.symm) hxy
      · rw [hT]
        simp only [hfx, hfy]
        ring
      · rw [hT]
        simp only [hfx, hfy]
        ring
      · exact absurd (hfx.trans hfy.symm) hxy
  have hSeq : (∑ x, ∑ y, ((Γ x y : ℝ) : ℂ) * star (α x) * α y *
        inner ℂ (ψ x) (ψ y)) =
      (∑ x, ∑ y, A x y * inner ℂ (a0 x) (a0 y)) +
      (∑ x, ∑ y, A x y * inner ℂ (a1 x) (a1 y)) := by
    have hcongr : (∑ x, ∑ y, ((Γ x y : ℝ) : ℂ) * star (α x) * α y *
          inner ℂ (ψ x) (ψ y)) =
        ∑ x, ∑ y, (A x y * inner ℂ (a0 x) (a0 y) +
          A x y * inner ℂ (a1 x) (a1 y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hterm x y
    have hsplit : (∑ x, ∑ y, (A x y * inner ℂ (a0 x) (a0 y) +
        A x y * inner ℂ (a1 x) (a1 y))) =
        (∑ x, ∑ y, A x y * inner ℂ (a0 x) (a0 y)) +
        (∑ x, ∑ y, A x y * inner ℂ (a1 x) (a1 y)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_add_distrib
    exact hcongr.trans hsplit
  have b0 := bilin_output_le f A hA0 a0
  have b1 := bilin_output_le f A hA0 a1
  have pyth : ∀ x, ‖u false x‖ ^ 2 + ‖u true x‖ ^ 2 = 1 := by
    intro x
    have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (u false x) (u true x) (hortho x x)
    rw [← hdecomp x] at h1
    rw [hunit x] at h1
    simp only [← pow_two] at h1
    rw [one_pow] at h1
    exact h1.symm
  have na0 : ∀ x, ‖a0 x‖ ^ 2 = ‖α x‖ ^ 2 * ‖u false x‖ ^ 2 := by
    intro x
    rw [ha0]
    simp only []
    rw [norm_smul, mul_pow]
  have na1 : ∀ x, ‖a1 x‖ ^ 2 = ‖α x‖ ^ 2 * ‖u true x‖ ^ 2 := by
    intro x
    rw [ha1]
    simp only []
    rw [norm_smul, mul_pow]
  have nC0 : (∑ x, if f x = false then ‖a0 x‖ ^ 2 else 0) =
      ∑ x, if f x = false then ‖α x‖ ^ 2 * ‖u false x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · exact na0 x
    · rfl
  have nE1 : (∑ x, if f x = true then ‖a0 x‖ ^ 2 else 0) =
      ∑ x, if f x = true then ‖α x‖ ^ 2 * ‖u false x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · exact na0 x
    · rfl
  have nE0 : (∑ x, if f x = false then ‖a1 x‖ ^ 2 else 0) =
      ∑ x, if f x = false then ‖α x‖ ^ 2 * ‖u true x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · exact na1 x
    · rfl
  have nC1 : (∑ x, if f x = true then ‖a1 x‖ ^ 2 else 0) =
      ∑ x, if f x = true then ‖α x‖ ^ 2 * ‖u true x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · exact na1 x
    · rfl
  rw [nC0, nE1] at b0
  rw [nE0, nC1] at b1
  set C0 : ℝ := ∑ x, if f x = false then ‖α x‖ ^ 2 * ‖u false x‖ ^ 2 else 0 with hC0
  set E1 : ℝ := ∑ x, if f x = true then ‖α x‖ ^ 2 * ‖u false x‖ ^ 2 else 0 with hE1
  set E0 : ℝ := ∑ x, if f x = false then ‖α x‖ ^ 2 * ‖u true x‖ ^ 2 else 0 with hE0
  set C1 : ℝ := ∑ x, if f x = true then ‖α x‖ ^ 2 * ‖u true x‖ ^ 2 else 0 with hC1
  have hP : C0 + C1 = ∑ x, ‖α x‖ ^ 2 * ‖u (f x) x‖ ^ 2 := by
    rw [hC0, hC1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases _ : f x <;> simp
  have hQ : E0 + E1 = ∑ x, ‖α x‖ ^ 2 * ‖u (!f x) x‖ ^ 2 := by
    rw [hE0, hE1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases _ : f x <;> simp
  have hQle : E0 + E1 ≤ ε := by
    rw [hQ]
    calc ∑ x, ‖α x‖ ^ 2 * ‖u (!f x) x‖ ^ 2
        ≤ ∑ x, ‖α x‖ ^ 2 * ε := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left (herr x) (sq_nonneg _)
      _ = ε := by
          rw [← Finset.sum_mul, hα, one_mul]
  have hPQ : (C0 + C1) + (E0 + E1) = 1 := by
    rw [hP, hQ, ← Finset.sum_add_distrib]
    have hper : ∀ x, ‖α x‖ ^ 2 * ‖u (f x) x‖ ^ 2 +
        ‖α x‖ ^ 2 * ‖u (!f x) x‖ ^ 2 = ‖α x‖ ^ 2 := by
      intro x
      have hpy : ‖u (f x) x‖ ^ 2 + ‖u (!f x) x‖ ^ 2 = 1 := by
        cases _ : f x
        · simp only [Bool.not_false]
          exact pyth x
        · simp only [Bool.not_true]
          rw [add_comm]
          exact pyth x
      calc ‖α x‖ ^ 2 * ‖u (f x) x‖ ^ 2 + ‖α x‖ ^ 2 * ‖u (!f x) x‖ ^ 2
          = ‖α x‖ ^ 2 * (‖u (f x) x‖ ^ 2 + ‖u (!f x) x‖ ^ 2) := by ring
        _ = ‖α x‖ ^ 2 * 1 := by rw [hpy]
        _ = ‖α x‖ ^ 2 := by ring
    have hcongr : (∑ x, (‖α x‖ ^ 2 * ‖u (f x) x‖ ^ 2 +
        ‖α x‖ ^ 2 * ‖u (!f x) x‖ ^ 2)) = ∑ x, ‖α x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact hper x
    rw [hcongr, hα]
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    apply Finset.sum_nonneg
    intro x _
    split_ifs with h
    · positivity
    · exact le_rfl
  have hC1nn : 0 ≤ C1 := by
    rw [hC1]
    apply Finset.sum_nonneg
    intro x _
    split_ifs with h
    · positivity
    · exact le_rfl
  have hE0nn : 0 ≤ E0 := by
    rw [hE0]
    apply Finset.sum_nonneg
    intro x _
    split_ifs with h
    · positivity
    · exact le_rfl
  have hE1nn : 0 ≤ E1 := by
    rw [hE1]
    apply Finset.sum_nonneg
    intro x _
    split_ifs with h
    · positivity
    · exact le_rfl
  rw [hSeq]
  refine le_trans (norm_add_le _ _) ?_
  have hsum : ‖∑ x, ∑ y, A x y * inner ℂ (a0 x) (a0 y)‖ +
      ‖∑ x, ∑ y, A x y * inner ℂ (a1 x) (a1 y)‖ ≤
      2 * ‖A‖ * (Real.sqrt C0 * Real.sqrt E1 + Real.sqrt E0 * Real.sqrt C1) := by
    calc ‖∑ x, ∑ y, A x y * inner ℂ (a0 x) (a0 y)‖ +
          ‖∑ x, ∑ y, A x y * inner ℂ (a1 x) (a1 y)‖
        ≤ (2 * ‖A‖ * Real.sqrt C0 * Real.sqrt E1) +
          (2 * ‖A‖ * Real.sqrt E0 * Real.sqrt C1) := add_le_add b0 b1
      _ = 2 * ‖A‖ * (Real.sqrt C0 * Real.sqrt E1 + Real.sqrt E0 * Real.sqrt C1) := by
          ring
  have hcs : Real.sqrt C0 * Real.sqrt E1 + Real.sqrt E0 * Real.sqrt C1 ≤
      Real.sqrt ((C0 + C1) * (E0 + E1)) := by
    have h := adversary_sqrt_add_mul_le hC0nn hE1nn hC1nn hE0nn
    rw [add_comm E1 E0] at h
    rw [mul_comm (Real.sqrt E0) (Real.sqrt C1)]
    exact h
  have hPQle : (C0 + C1) * (E0 + E1) ≤ ε * (1 - ε) := by
    have hPeq : C0 + C1 = 1 - (E0 + E1) := by linarith [hPQ]
    rw [hPeq, mul_comm (1 - (E0 + E1)) (E0 + E1)]
    exact adversary_mul_one_sub_le (add_nonneg hE0nn hE1nn) hQle hε
  have hsqrt : Real.sqrt ((C0 + C1) * (E0 + E1)) ≤ Real.sqrt (ε * (1 - ε)) :=
    Real.sqrt_le_sqrt hPQle
  calc ‖∑ x, ∑ y, A x y * inner ℂ (a0 x) (a0 y)‖ +
        ‖∑ x, ∑ y, A x y * inner ℂ (a1 x) (a1 y)‖
      ≤ 2 * ‖A‖ * (Real.sqrt C0 * Real.sqrt E1 + Real.sqrt E0 * Real.sqrt C1) := hsum
    _ ≤ 2 * ‖A‖ * Real.sqrt ((C0 + C1) * (E0 + E1)) := by
        apply mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ 2 * ‖A‖ * Real.sqrt (ε * (1 - ε)) := by
        apply mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 2 * Real.sqrt (ε * (1 - ε)) * ‖A‖ := by ring

/-- Operator-norm form of the adversary output condition. -/
theorem norm_hadamard_gramMatrix_le {X E : Type*}
    [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : X → Bool) (ψ : X → E) (u : Bool → X → E)
    (hdecomp : ∀ x, ψ x = u false x + u true x)
    (hortho : ∀ x y, inner ℂ (u false x) (u true y) = 0)
    (hunit : ∀ x, ‖ψ x‖ = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (herr : ∀ x, ‖u (!f x) x‖ ^ 2 ≤ ε)
    (Γ : Matrix X X ℝ) (hΓ : IsAdversaryMatrix f Γ) :
    ‖Γ.map (fun r : ℝ => (r : ℂ)) ⊙ Matrix.gram ℂ ψ‖ ≤
      2 * Real.sqrt (ε * (1 - ε)) *
        ‖Γ.map (fun r : ℝ => (r : ℂ))‖ := by
  have _ := hε0
  set M : Matrix X X ℂ :=
    Γ.map (fun r : ℝ => (r : ℂ)) ⊙ Matrix.gram ℂ ψ with hM
  set T : EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X :=
    Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M with hT
  have hsym : ∀ i j, Γ j i = Γ i j := by
    intro i j
    have h := congrFun (congrFun hΓ.1.eq i) j
    rw [Matrix.transpose_apply] at h
    exact h
  have hA : (Γ.map (fun r : ℝ => (r : ℂ))).IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply]
    simp [hsym i j]
  have hG : (Matrix.gram ℂ ψ).IsHermitian := Matrix.isHermitian_gram ℂ ψ
  have hHerm : M.IsHermitian := by
    rw [hM]
    exact hA.hadamard hG
  have hMself : IsSelfAdjoint M := hHerm.isSelfAdjoint
  have hTself : IsSelfAdjoint T := by
    rw [hT]
    show IsSelfAdjoint (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M)
    have hstar : star (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M) =
        Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) M := by
      rw [← map_star, hMself.star_eq]
    exact hstar
  have hsymm : (T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X).IsSymmetric :=
    hTself.isSymmetric
  have hnorm : ‖M‖ = ⨆ x, |T.rayleighQuotient x| := by
    rw [Matrix.cstar_norm_def]
    rw [hT]
    exact ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsymm
  rw [hnorm]
  apply ciSup_le
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    simp only [ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    positivity
  · have hspos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hs0 : ‖x‖ ≠ 0 := ne_of_gt hspos
    have hsc0 : ((‖x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0
    have hsqpos : 0 < ‖x‖ ^ 2 := pow_pos hspos 2
    set α : X → ℂ := WithLp.ofLp x with hα
    have hx : x = WithLp.toLp 2 α := (WithLp.toLp_ofLp 2 x).symm
    have hTx : T x = WithLp.toLp 2 (M *ᵥ α) := by
      rw [hT, hx]
      exact Matrix.toEuclideanCLM_toLp M α
    have hinner : inner ℂ x (T x) =
        ∑ a, ∑ b, ((Γ a b : ℝ) : ℂ) * star (α a) * α b *
          inner ℂ (ψ a) (ψ b) := by
      rw [hx, hTx, EuclideanSpace.inner_toLp_toLp]
      simp only [dotProduct, Matrix.mulVec_apply, Matrix.row_apply]
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_mul _ _ _)]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      have hMab : M a b = ((Γ a b : ℝ) : ℂ) * inner ℂ (ψ a) (ψ b) := by
        rw [hM]
        rfl
      rw [hMab, Pi.star_apply]
      ring
    have hsymmx : inner ℂ (T x) x = inner ℂ x (T x) := hsymm x x
    have hnormα : ∑ i, ‖α i‖ ^ 2 = ‖x‖ ^ 2 := by
      have h := EuclideanSpace.norm_sq_eq x
      rw [← hα] at h
      exact h.symm
    set β : X → ℂ := fun i => α i / ((‖x‖ : ℝ) : ℂ) with hβ
    have hβnorm : ∑ i, ‖β i‖ ^ 2 = 1 := by
      have hper : ∀ i, ‖β i‖ ^ 2 = ‖α i‖ ^ 2 / ‖x‖ ^ 2 := by
        intro i
        rw [hβ]
        simp only []
        rw [norm_div, Complex.norm_of_nonneg (le_of_lt hspos)]
        rw [div_pow]
      rw [Finset.sum_congr rfl (fun i _ => hper i)]
      rw [← Finset.sum_div, hnormα]
      exact div_self (pow_ne_zero 2 hs0)
    have hαβ : ∀ i, α i = ((‖x‖ : ℝ) : ℂ) * β i := by
      intro i
      rw [hβ]
      simp only []
      field_simp
    have hstarα : ∀ i, star (α i) = ((‖x‖ : ℝ) : ℂ) * star (β i) := by
      intro i
      rw [hαβ i, star_mul]
      have hsstar : star (((‖x‖ : ℝ) : ℂ)) = ((‖x‖ : ℝ) : ℂ) := by simp
      rw [hsstar, mul_comm]
    have hQscale : (∑ a, ∑ b, ((Γ a b : ℝ) : ℂ) * star (α a) * α b *
          inner ℂ (ψ a) (ψ b)) =
        (((‖x‖ ^ 2 : ℝ) : ℂ)) * ∑ a, ∑ b, ((Γ a b : ℝ) : ℂ) * star (β a) *
          β b * inner ℂ (ψ a) (ψ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hstarα a, hαβ b]
      push_cast
      ring
    have hquad := adversary_quadForm_le f ψ u hdecomp hortho hunit hε0 hε herr
      Γ hΓ β hβnorm
    show |T.reApplyInnerSelf x / ‖x‖ ^ 2| ≤ _
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hsymmx, hinner,
      abs_div, abs_of_nonneg (sq_nonneg ‖x‖), div_le_iff₀ hsqpos]
    calc |RCLike.re (∑ a, ∑ b, ((Γ a b : ℝ) : ℂ) * star (α a) * α b *
            inner ℂ (ψ a) (ψ b))|
        ≤ ‖∑ a, ∑ b, ((Γ a b : ℝ) : ℂ) * star (α a) * α b *
            inner ℂ (ψ a) (ψ b)‖ := RCLike.abs_re_le_norm _
      _ = ‖x‖ ^ 2 * ‖∑ a, ∑ b, ((Γ a b : ℝ) : ℂ) * star (β a) * β b *
            inner ℂ (ψ a) (ψ b)‖ := by
          rw [hQscale, norm_mul,
            Complex.norm_of_nonneg (sq_nonneg _)]
      _ ≤ ‖x‖ ^ 2 * (2 * Real.sqrt (ε * (1 - ε)) *
            ‖Γ.map (fun r : ℝ => (r : ℂ))‖) :=
          mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
      _ = (2 * Real.sqrt (ε * (1 - ε)) *
            ‖Γ.map (fun r : ℝ => (r : ℂ))‖) * ‖x‖ ^ 2 := by ring

end Cslib.AdversaryOutputCondition
