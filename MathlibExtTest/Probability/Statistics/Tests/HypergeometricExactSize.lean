/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Tests.HypergeometricExactSize

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Tests.HypergeometricExactSize

open ProbabilityTheory

/-- Fixture A (use): the single-free-cell 2×2 table has closed-form masses `1/2, 1/2`. -/
example : hypergeometricReal 2 1 1 0 = 1 / 2 ∧ hypergeometricReal 2 1 1 1 = 1 / 2 := by
  have h1 : (2 : ℕ) - 1 = 1 := rfl
  have h3 : (1 : ℕ) - 1 = 0 := rfl
  have c10 : Nat.choose 1 0 = 1 := rfl
  have c11 : Nat.choose 1 1 = 1 := rfl
  have c21 : Nat.choose 2 1 = 2 := rfl
  unfold hypergeometricReal
  simp only [ite_eq_left (show (0 : ℕ) ≤ 1 from by decide),
    ite_eq_left (show (1 : ℕ) ≤ 1 from by decide), h1, h3, c10, c11, c21]
  norm_num

/-- Fixture B (use, through the normalization API): the hypergeometric masses normalize
over the support. -/
example (N K m : ℕ) (hK : K ≤ N) (hm : m ≤ N) :
    ∑ j : Fin (m + 1), hypergeometricReal N K m (j.val : ℕ) = 1 := by
  have h := sum_hypergeometricReal (N := N) (K := K) (n := m) hK hm
  rw [Fin.sum_univ_eq_sum_range]
  exact h

/-- Fixture C (degenerate): zero free cells give a trivial test — on a one-point space the
exact-size construction yields a constant test through the copied theorem. -/
example (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ φstar : Unit → Set.Icc (0 : ℝ) 1,
      ∑ _ : Unit, (φstar ()).val * (1 : ℝ) = α ∧
      ∀ φ : Unit → Set.Icc (0 : ℝ) 1,
        ∑ _ : Unit, (φ ()).val * (1 : ℝ) ≤ α →
          ∑ _ : Unit, (φ ()).val * (1 : ℝ) ≤
            ∑ _ : Unit, (φstar ()).val * (1 : ℝ) := by
  obtain ⟨_k, _hk, _γ, _hγ, φstar, _hgt, _hlt, _heq, hsize, hdom⟩ :=
    MathlibExt.Probability.Statistics.NeymanPearson.exists_exact_size_most_powerful_finite
      (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (1 : ℝ))
      (fun _ => zero_le_one) (fun _ => zero_le_one)
      (show ∑ _ : Unit, (1 : ℝ) = 1 from by simp)
      (show ∑ _ : Unit, (1 : ℝ) = 1 from by simp)
      α hα0 hα1
  exact ⟨φstar, hsize, hdom⟩

end MathlibExtTest.Probability.Statistics.Tests.HypergeometricExactSize
