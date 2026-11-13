/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Tests.BinomialExactSize

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Tests.BinomialExactSize

/-- Fixture A (through the main theorem): at `α = 1/2` on the symmetric pair the exact-size
most powerful test exists and takes a strictly fractional value somewhere. -/
example (h : (0 : ℝ) < (1 / 4 : ℝ)) :
    ∃ φstar : Fin 2 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φstar j).val *
        (ProbabilityTheory.binomial 1 ⟨(1 / 4 : ℝ), by norm_num⟩).real {(j.val : ℕ)} = 1 / 2 ∧
      (∀ φ : Fin 2 → Set.Icc (0 : ℝ) 1,
        ∑ j, (φ j).val *
          (ProbabilityTheory.binomial 1 ⟨(1 / 4 : ℝ), by norm_num⟩).real {(j.val : ℕ)} ≤ 1 / 2 →
        ∑ j, (φ j).val *
          (ProbabilityTheory.binomial 1 ⟨(3 / 4 : ℝ), by norm_num⟩).real {(j.val : ℕ)} ≤
          ∑ j, (φstar j).val *
            (ProbabilityTheory.binomial 1 ⟨(3 / 4 : ℝ), by norm_num⟩).real {(j.val : ℕ)}) ∧
      ∃ j, 0 < (φstar j).val ∧ (φstar j).val < 1 := by
  obtain ⟨_, _, _, _, φstar, _, _, _, hsize, hopt⟩ :=
    MathlibExt.Probability.Statistics.Tests.binomial_exact_size_most_powerful 1 (le_refl 1)
      (p₀ := (⟨(1 / 4 : ℝ), by norm_num⟩ : ↥unitInterval))
      (p₁ := (⟨(3 / 4 : ℝ), by norm_num⟩ : ↥unitInterval))
      h (by show (1 / 4 : ℝ) < 3 / 4; norm_num) (by show (3 / 4 : ℝ) < 1; norm_num)
      (1 / 2) (by norm_num) (by norm_num)
  refine ⟨φstar, hsize, hopt, ?_⟩
  have v0 : ((⟨(1 / 4 : ℝ), by norm_num⟩ : ↥unitInterval).val) = 1 / 4 := rfl
  have m0 : (ProbabilityTheory.binomial 1
      (⟨(1 / 4 : ℝ), by norm_num⟩ : ↥unitInterval)).real {(0 : ℕ)} = 3 / 4 := by
    rw [ProbabilityTheory.binomial_real_zero, v0]
    norm_num
  have m1 : (ProbabilityTheory.binomial 1
      (⟨(1 / 4 : ℝ), by norm_num⟩ : ↥unitInterval)).real {(1 : ℕ)} = 1 / 4 := by
    rw [ProbabilityTheory.binomial_real_self, v0]
    norm_num
  have hsize2 : ∑ j : Fin 2, (φstar j).val *
      (ProbabilityTheory.binomial 1
        (⟨(1 / 4 : ℝ), by norm_num⟩ : ↥unitInterval)).real {(j.val : ℕ)} = 1 / 2 := hsize
  rw [Fin.sum_univ_two] at hsize2
  have e0 : ((0 : Fin 2).val : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 2).val : ℕ) = 1 := rfl
  rw [e0, e1, m0, m1] at hsize2
  by_contra hcon
  have hdet : ∀ j : Fin 2, (φstar j).val = 0 ∨ (φstar j).val = 1 := by
    intro j
    have hlo := (φstar j).property.1
    have hhi := (φstar j).property.2
    by_contra hc
    have hc1 : (φstar j).val ≠ 0 := fun h0 => hc (Or.inl h0)
    have hc2 : (φstar j).val ≠ 1 := fun h1 => hc (Or.inr h1)
    have hpos : 0 < (φstar j).val := lt_of_le_of_ne hlo (Ne.symm hc1)
    have hlt : (φstar j).val < 1 := lt_of_le_of_ne hhi hc2
    exact hcon ⟨j, hpos, hlt⟩
  rcases hdet 0 with h00 | h00 <;> rcases hdet 1 with h11 | h11 <;>
    rw [h00, h11] at hsize2 <;> norm_num at hsize2

/-- Fixture B (boundary): at `α = 1/4` below every atom mass, the exact-size test rejects
nowhere fully. -/
example :
    ∃ φstar : Fin 2 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φstar j).val *
        (ProbabilityTheory.binomial 1 ⟨(1 / 2 : ℝ), by norm_num⟩).real {(j.val : ℕ)} = 1 / 4 ∧
      ∀ j, (φstar j).val < 1 := by
  have v : ((⟨(1 / 2 : ℝ), by norm_num⟩ : ↥unitInterval).val) = 1 / 2 := rfl
  have m0 : (ProbabilityTheory.binomial 1
      (⟨(1 / 2 : ℝ), by norm_num⟩ : ↥unitInterval)).real {(0 : ℕ)} = 1 / 2 := by
    rw [ProbabilityTheory.binomial_real_zero, v]
    norm_num
  have m1 : (ProbabilityTheory.binomial 1
      (⟨(1 / 2 : ℝ), by norm_num⟩ : ↥unitInterval)).real {(1 : ℕ)} = 1 / 2 := by
    rw [ProbabilityTheory.binomial_real_self, v]
    norm_num
  have e0 : ((0 : Fin 2).val : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 2).val : ℕ) = 1 := rfl
  refine ⟨![⟨(0 : ℝ), Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩,
    ⟨(1 / 2 : ℝ), Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩], ?_, ?_⟩
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    show (0 : ℝ) * (ProbabilityTheory.binomial 1
        (⟨(1 / 2 : ℝ), by norm_num⟩ : ↥unitInterval)).real {((0 : Fin 2).val : ℕ)} +
        (1 / 2) * (ProbabilityTheory.binomial 1
        (⟨(1 / 2 : ℝ), by norm_num⟩ : ↥unitInterval)).real {((1 : Fin 2).val : ℕ)} = 1 / 4
    rw [e0, e1, m0, m1]
    norm_num
  · intro j
    fin_cases j
    · show (0 : ℝ) < 1
      norm_num
    · show (1 / 2 : ℝ) < 1
      norm_num

/-- Fixture C (counter-case): no deterministic test attains the straddling size `1/4` —
randomization is necessary. -/
example : ∀ φ : Fin 2 → Set.Icc (0 : ℝ) 1,
    (∀ j, (φ j).val = 0 ∨ (φ j).val = 1) →
    ∑ j, (φ j).val * (1 / 2 : ℝ) ≠ 1 / 4 := by
  intro φ hdet hcon
  rw [Fin.sum_univ_two] at hcon
  rcases hdet 0 with h00 | h00 <;> rcases hdet 1 with h11 | h11 <;>
    rw [h00, h11] at hcon <;> norm_num at hcon

end MathlibExtTest.Probability.Statistics.Tests.BinomialExactSize
