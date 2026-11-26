/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.NicomacheanTranslations
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-valued Nicomachean sequences with a large normalized gap

The gap between the two values can exceed any prescribed fraction less than one of the
length of the sequence.
-/

namespace MetaMathlibExt

/-- **Two-valued Nicomachean sequences with a large gap.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every real $\varepsilon > 0$ there are integers $0 < a < b$ and a finite
sequence $\sigma$ whose entries all equal $a$ or $b$, in which both $a$ and $b$ occur, such that
$\nu(\sigma) = 0$ and $(b - a)/L > 1 - \varepsilon$, where $L$ is the length of $\sigma$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 4
(`jis-2024-24.6.3-prop-4`). -/
public theorem exists_two_valued_nicomachean_large_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ ∃ σ : List ℤ, (∀ x ∈ σ, x = a ∨ x = b) ∧ a ∈ σ ∧ b ∈ σ ∧
      nicomacheanNu σ = 0 ∧ 1 - ε < ((b - a : ℤ) : ℝ) / σ.length := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (2 / ε))
  have hnR : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnN : 1 < n := by exact_mod_cast hnR
  have hnZ : (1 : ℤ) < n := by exact_mod_cast hnN
  have hnSq : 2 < n ^ 2 := by
    calc
      2 < 2 * 2 := by decide
      _ ≤ n ^ 2 := by simpa [pow_two] using Nat.mul_le_mul (show 2 ≤ n from hnN) hnN
  let σ := List.replicate n (n : ℤ) ++ List.replicate (n ^ 2 - 2) ((n : ℤ) ^ 2)
  have hab : (n : ℤ) < (n : ℤ) ^ 2 := by
    simpa [pow_two] using mul_lt_mul_of_pos_right hnZ (zero_lt_one.trans hnZ)
  refine ⟨n, (n : ℤ) ^ 2, zero_lt_one.trans hnZ, hab, σ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (List.eq_of_mem_replicate hx)
    · exact Or.inr (List.eq_of_mem_replicate hx)
  · exact List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  · exact List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  · simp only [σ, nicomacheanNu, List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate, nsmul_eq_mul]
    push_cast [Nat.cast_sub hnSq.le]
    ring
  · have hLengthNat : 0 < σ.length := by
      simp only [σ, List.length_append, List.length_replicate]
      omega
    have hLength : 0 < (σ.length : ℝ) := by exact_mod_cast hLengthNat
    apply (lt_div_iff₀ hLength).2
    simp only [σ, List.length_append, List.length_replicate]
    push_cast [Nat.cast_sub hnSq.le]
    have hεn : (2 : ℝ) < (n : ℝ) * ε :=
      (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    -- The length is (n + 2)(n - 1) and the gap is n(n - 1).
    have hbound : (1 - ε) * ((n : ℝ) + 2) < (n : ℝ) := by
      nlinarith only [hεn, hε]
    calc
      _ = ((1 - ε) * ((n : ℝ) + 2)) * ((n : ℝ) - 1) := by ring
      _ < (n : ℝ) * ((n : ℝ) - 1) := mul_lt_mul_of_pos_right hbound (sub_pos.mpr hnR)
      _ = _ := by ring

end MetaMathlibExt
