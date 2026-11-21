/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.MellinHermiteSumNonvanishing

@[expose] public section

open Complex

/-- `exactSource` consumer with the original binders. -/
example     (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ : ZMod 2) (e : ℤ)
    (hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ
      Finset.range (m + 1))).filter
            (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2)
              = (e : ZMod 2) + a₃))).Nonempty)
    (H : ℕ → ZMod 2 → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (b : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin (H j b)
        (x : ℂ)‖ ≤ ε * x * ‖mellin (H j b) (x : ℂ)‖)
    (hB : ∀ (j : ℕ) (b b' : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 1) b') ((x : ℂ) - 1)‖ ≤ ε * ‖mellin (H j b) (x : ℂ)‖) :
    ∀ σ₀ : ℝ, ∃ s : ℝ, σ₀ < s ∧
      ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ
        Finset.range (m + 1))).filter
            (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2)
              = (e : ZMod 2) + a₃)),
          ((-1 : ℂ) ^ (T.2.1 + T.2.2) *
            ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
              ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) *
                (T.2.2.factorial : ℂ) *
                (4 * (Real.pi : ℂ)) ^ T.1.1))) *
            Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1 ((e : ZMod 2) + (T.2.2 :
              ZMod 2))) ((s : ℂ) + (T.2.2 : ℂ) - 1) ≠ 0  :=
  LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real
    m a ha u₃ a₃ e hne H hA hB

/-- Boundary consumer at `σ₀ = 0`: there is a shift `s > 0` with the same
nonvanishing sum. -/
example (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ : ZMod 2) (e : ℤ)
    (hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ
      (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
        (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
          ((T.1.2 : ZMod 2) = (e : ZMod 2) + a₃))).Nonempty)
    (H : ℕ → ZMod 2 → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (b : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) *
        mellin (H j b) (x : ℂ)‖ ≤ ε * x * ‖mellin (H j b) (x : ℂ)‖)
    (hB : ∀ (j : ℕ) (b b' : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 1) b') ((x : ℂ) - 1)‖ ≤ ε * ‖mellin (H j b) (x : ℂ)‖) :
    ∃ s : ℝ, 0 < s ∧ True := by
  obtain ⟨s, hs, -⟩ :=
    LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real
      m a ha u₃ a₃ e hne H hA hB 0
  exact ⟨s, hs, trivial⟩
