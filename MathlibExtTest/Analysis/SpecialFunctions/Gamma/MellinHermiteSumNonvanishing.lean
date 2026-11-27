/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_
ne_zero_of_shift_ratio_real.lean`
(https://github.com/anthropics/fermats-last-theorem), at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`: the statement that the `exactSource`
consumer repeats. The other tests are original.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.MellinHermiteSumNonvanishing

@[expose] public section

open Complex LanglandsTunnell

/-- `exactSource` consumer with the original binders and the index set and sum written out. -/
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

/-- At `m = 0` only the index `((0, 0), (0, 0))` is in range, and it is admissible when
`e + a₃` is even. -/
example : hermiteAdmissible 0 0 0 = {((0, 0), (0, 0))} := by decide

/-- When `e + a₃` is odd (here `e = 1`) the parity condition removes that index, so `hne` can
fail. -/
example : hermiteAdmissible 0 0 1 = ∅ := by decide

/-- At `m = 2` with `e + a₃` even, the admissible indices are `((1, 0), (0, 0))`,
`((0, 2), (0, 0))` and the three `((0, 0), (j, k))` with `j + k = 2`. -/
example : hermiteAdmissible 2 0 0 =
    {((1, 0), (0, 0)), ((0, 2), (0, 0)), ((0, 0), (2, 0)), ((0, 0), (1, 1)), ((0, 0), (0, 2))} := by
  decide

/-- At `m = 2` with `e + a₃` odd (here `a₃ = 1`), only the indices with `l = 1` remain. -/
example : hermiteAdmissible 2 1 0 = {((0, 1), (1, 0)), ((0, 1), (0, 1))} := by decide

/-- A coefficient with `i = 1`: `c_{((1, 0), (0, 0))} = -2! / (4π)`. -/
example (a : ℚ) : hermiteCoeff 2 a ((1, 0), (0, 0)) = -2 / (4 * (Real.pi : ℂ)) := by
  simp [hermiteCoeff, Nat.factorial]

/-- A coefficient with `k = 1`: `c_{((0, 0), (0, 1))} = (-1) ^ 1 * 1! * a = -a`. -/
example (a : ℚ) : hermiteCoeff 1 a ((0, 0), (0, 1)) = -(a : ℂ) := by
  simp [hermiteCoeff]

/-- At `m = 0` (with `e = a₃ = 0`) the sum is the single term
`Γℝ (s + u₃) * mellin (H 0 0) (s - 1)`. -/
example (a : ℚ) (u₃ : ℂ) (H : ℕ → ZMod 2 → ℝ → ℂ) (s : ℝ) :
    hermiteGammaMellinSum 0 a u₃ 0 0 H s =
      Complex.Gammaℝ ((s : ℂ) + u₃) * mellin (H 0 0) ((s : ℂ) - 1) := by
  rw [hermiteGammaMellinSum, show hermiteAdmissible 0 0 0 = {((0, 0), (0, 0))} by decide,
    Finset.sum_singleton]
  simp [hermiteCoeff]

/-- At `m = 1` (with `e = a₃ = 0`) the admissible indices are `((0, 0), (1, 0))` and
`((0, 0), (0, 1))`, with coefficients `-1` and `-a`; the second term reads `H 0 1` at `s`. -/
example (a : ℚ) (u₃ : ℂ) (H : ℕ → ZMod 2 → ℝ → ℂ) (s : ℝ) :
    hermiteGammaMellinSum 1 a u₃ 0 0 H s =
      -(Complex.Gammaℝ ((s : ℂ) + u₃) * mellin (H 1 0) ((s : ℂ) - 1)) -
        (a : ℂ) * (Complex.Gammaℝ ((s : ℂ) + u₃) * mellin (H 0 1) (s : ℂ)) := by
  rw [hermiteGammaMellinSum,
    show hermiteAdmissible 1 0 0 = {((0, 0), (1, 0)), ((0, 0), (0, 1))} by decide,
    Finset.sum_pair (by decide)]
  simp [hermiteCoeff]
  ring

/-- Boundary consumer at `σ₀ = 0`: there is a shift `s > 0` with the same
nonvanishing sum. -/
example (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ : ZMod 2) (e : ℤ)
    (hne : (hermiteAdmissible m a₃ e).Nonempty)
    (H : ℕ → ZMod 2 → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (b : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j b) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j b) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) *
        mellin (H j b) (x : ℂ)‖ ≤ ε * x * ‖mellin (H j b) (x : ℂ)‖)
    (hB : ∀ (j : ℕ) (b b' : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 1) b') ((x : ℂ) - 1)‖ ≤ ε * ‖mellin (H j b) (x : ℂ)‖) :
    ∃ s : ℝ, 0 < s ∧ hermiteGammaMellinSum m a u₃ a₃ e H s ≠ 0 := by
  obtain ⟨s, hs, hsum⟩ :=
    exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real
      m a ha u₃ a₃ e hne H hA hB 0
  exact ⟨s, hs, hsum⟩

/-- `hA` cannot be dropped. Take `m = 0`, `a = 1`, `u₃ = 0`, `a₃ = 0`, `e = 0` and `H = 0`:
`ha`, `hne` and `hB` hold (each is proved in its slot below), and only `hA` fails, since
`mellin 0 = 0`. Every summand then has the factor `mellin 0 _ = 0`, so no shift makes the
sum nonzero. -/
example : ¬ ∀ (m : ℕ) (a : ℚ) (_ha : a ≠ 0) (u₃ : ℂ) (a₃ : ZMod 2) (e : ℤ)
    (_hne : (hermiteAdmissible m a₃ e).Nonempty) (H : ℕ → ZMod 2 → ℝ → ℂ)
    (_hB : ∀ (j : ℕ) (b b' : ZMod 2) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 1) b') ((x : ℂ) - 1)‖ ≤ ε * ‖mellin (H j b) (x : ℂ)‖),
    ∀ σ₀ : ℝ, ∃ s : ℝ, σ₀ < s ∧ hermiteGammaMellinSum m a u₃ a₃ e H s ≠ 0 := by
  intro h
  obtain ⟨s, -, hs⟩ := h 0 1 one_ne_zero 0 0 0
    -- `hne`: the index `((0, 0), (0, 0))` is admissible
    ⟨((0, 0), (0, 0)), by decide⟩
    (fun _ _ _ => 0)
    -- `hB`: both sides are `0`
    (fun _ _ _ _ _ => ⟨0, fun _ _ => by simp [mellin]⟩) 0
  exact hs (Finset.sum_eq_zero fun _ _ => by simp [mellin])
