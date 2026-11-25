/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MetaMathlibExt

/-! # Exponential growth bound for C-recursive sequences -/

/-- **Exponential growth bound for solutions of linear recurrences.** Let $k$ be a natural
number, let $c_0, \dots, c_{k-1}$ be complex numbers, and let $t : \mathbb{N} \to \mathbb{C}$
satisfy $t(n+k) = \sum_{i=0}^{k-1} c_i \, t(n+i)$ for all $n \in \mathbb{N}$. Then there is an
integer $g \ge 1$ such that $|t(n)| < g^{n+1}$ for all $n \in \mathbb{N}$. -/
theorem exists_norm_lt_pow_of_isSolution (E : LinearRecurrence ℂ) (t : ℕ → ℂ)
    (h : E.IsSolution t) :
    ∃ g : ℤ, 1 ≤ g ∧ ∀ n : ℕ, ‖t n‖ < ((g : ℝ) ^ (n + 1)) := by
  obtain ⟨k, c⟩ := E
  have hrec : ∀ n : ℕ, t (n + k) = ∑ i : Fin k, c i * t (n + i.val) := h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, le_rfl, fun n => ?_⟩
    simp [show t n = 0 by simpa using hrec n]
  have hA0 : 0 ≤ ∑ i : Fin k, ‖c i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hS0 : 0 ≤ ∑ j ∈ Finset.range k, ‖t j‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  set M : ℝ := (∑ i : Fin k, ‖c i‖) + (∑ j ∈ Finset.range k, ‖t j‖) + 2 with hM
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨g, hg⟩ := exists_int_gt M
  have hg1 : 1 ≤ g := by
    have hlt : (1 : ℝ) < (g : ℝ) := by linarith
    have hlt' : (1 : ℤ) < g := by exact_mod_cast hlt
    omega
  have hG1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
  have hGpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hAG : (∑ i : Fin k, ‖c i‖) < (g : ℝ) := by linarith
  have hinit : ∀ j : ℕ, j < k → ‖t j‖ < (g : ℝ) := by
    intro j hj
    have h1 : ‖t j‖ ≤ ∑ j ∈ Finset.range k, ‖t j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_range.mpr hj)
    linarith
  have key : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → ‖t m‖ < (g : ℝ) ^ (m + 1) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0
      have h0k : 0 < k := by omega
      exact lt_of_lt_of_le (hinit 0 h0k) (le_self_pow₀ hG1 (by omega))
    | succ n ih =>
      intro m hm
      rcases eq_or_lt_of_le hm with rfl | hlt
      · by_cases hmk : n + 1 < k
        · exact lt_of_lt_of_le (hinit _ hmk) (le_self_pow₀ hG1 (by omega))
        · have hmk' : k ≤ n + 1 := le_of_not_gt hmk
          have htm : t (n + 1) = ∑ i : Fin k, c i * t (n + 1 - k + ↑i.val) := by
            have h1 : n + 1 = (n + 1 - k) + k := (Nat.sub_add_cancel hmk').symm
            conv_lhs => rw [h1]
            exact hrec _
          have hpre : ∀ i : Fin k,
              ‖t (n + 1 - k + ↑i.val)‖ ≤ (g : ℝ) ^ (n + 1) := by
            intro i
            have hi : i.val < k := i.isLt
            have hle : n + 1 - k + i.val ≤ n := by omega
            have h2 : (n + 1 - k + ↑i.val) + 1 ≤ n + 1 := by omega
            exact le_trans (le_of_lt (ih _ hle)) (pow_le_pow_right₀ hG1 h2)
          have hsum : ‖∑ i : Fin k, c i * t (n + 1 - k + ↑i.val)‖
              ≤ ∑ i : Fin k, ‖c i‖ * (g : ℝ) ^ (n + 1) := by
            refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hpre i) (norm_nonneg _)
          have hAmul : (∑ i : Fin k, ‖c i‖) * (g : ℝ) ^ (n + 1)
              < (g : ℝ) ^ ((n + 1) + 1) := by
            have hpos : (0 : ℝ) < (g : ℝ) ^ (n + 1) := pow_pos hGpos _
            have hlt2 : (∑ i : Fin k, ‖c i‖) * (g : ℝ) ^ (n + 1)
                < (g : ℝ) * (g : ℝ) ^ (n + 1) :=
              mul_lt_mul_of_pos_right hAG hpos
            have heq : (g : ℝ) * (g : ℝ) ^ (n + 1) = (g : ℝ) ^ ((n + 1) + 1) :=
              (pow_succ' _ _).symm
            rwa [heq] at hlt2
          calc ‖t (n + 1)‖ = ‖∑ i : Fin k, c i * t (n + 1 - k + ↑i.val)‖ := by
                rw [htm]
            _ ≤ ∑ i : Fin k, ‖c i‖ * (g : ℝ) ^ (n + 1) := hsum
            _ = (∑ i : Fin k, ‖c i‖) * (g : ℝ) ^ (n + 1) := by
                rw [Finset.sum_mul]
            _ < (g : ℝ) ^ ((n + 1) + 1) := hAmul
      · exact ih _ (Nat.le_of_lt_succ hlt)
  exact ⟨g, hg1, fun n => key n n le_rfl⟩

/--
**Exponential growth bound for C-recursive sequences.** Let $t : \mathbb{N} \to \mathbb{C}$ be
C-recursive: there are an order $k \ge 1$ and complex numbers $c_0, \dots, c_{k-1}$ with
$t(n+k) = \sum_{i=0}^{k-1} c_i \, t(n+i)$ for all $n \in \mathbb{N}$. Then there is an integer
$g \ge 1$ such that $|t(n)| < g^{n+1}$ for all $n \in \mathbb{N}$.

Proves `Wanted` entry `c_recursive_exponential_growth_bound`.

Source: M. Prunescu and J. M. Shunia, "On Modular Representations of
C-Recursive Integer Sequences," Journal of Integer Sequences 28 (2025),
Article 25.5.3, Lemma (label LemmaGeneralInequality, quoting Prunescu and
Sauras-Altuzarra, Lemma 4), lines 166–167,
https://cs.uwaterloo.ca/journals/JIS/VOL28/Prunescu/prunescu3.tex
-/
theorem c_recursive_exponential_growth_bound
    (t : ℕ → ℂ)
    (h : ∃ k : ℕ, 1 ≤ k ∧ ∃ c : Fin k → ℂ,
      ∀ n : ℕ, t (n + k) = ∑ i : Fin k, c i * t (n + i.val)) :
    ∃ g : ℤ, 1 ≤ g ∧ ∀ n : ℕ, ‖t n‖ < ((g : ℝ) ^ (n + 1)) := by
  obtain ⟨k, -, c, hrec⟩ := h
  exact exists_norm_lt_pow_of_isSolution ⟨k, c⟩ t hrec

end MetaMathlibExt
