/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.MichaelisMenten.Trajectories

/-! Tests for global Michaelis–Menten trajectories: the field on concrete states, the boundary
cases of an unprepared initial complex and of zero substrate (checked from the definitions, not
through the theorems under test), non-vacuity of the existence hypotheses, and a negative initial
enzyme showing the sign hypotheses are needed. -/

open Real

namespace MathlibExtTest.Biology.Dynamics.MichaelisMenten.Trajectories

open MathlibExt.Biology.Dynamics.MichaelisMenten

/-! ### Smoke test: the field on concrete states -/

example : mmField 1 1 1 ![2, 0, 1, 0] = ![-2, 2, -2, 0] := by
  ext i; fin_cases i <;> norm_num [mmField, substrateRate, complexRate]

example : mmCurve (fun _ ↦ 2) (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ 0) 5 = ![2, 0, 1, 0] := rfl

/-! ### Boundary case: unprepared initial complex

With `k₁ = k₋₁ = k₂ = 1`, total enzyme `1`, substrate `2` and no complex, the quasi-steady-state
complex is `1/2`, so `c(0) = 0` is unprepared, and the complex rate at the initial state is
positive, so the complex leaves `0` at once. Both facts are computed from the definitions. -/

example : qssComplex 1 1 1 (1 + 0) 2 = 1 / 2 := by norm_num [qssComplex, michaelisConstant]

example : (0 : ℝ) ≠ qssComplex 1 1 1 (1 + 0) 2 := by norm_num [qssComplex, michaelisConstant]

example : 0 < complexRate 1 1 1 2 0 1 := by norm_num [complexRate]

/-- The existence theorem applies to the unprepared start, and the resulting complex is positive
at positive times. -/
example : ∃ s c e p : ℝ → ℝ, IsSolution 1 1 1 s c e p ∧ c 0 = 0 ∧
    (∀ t, 0 < t → 0 < c t) ∧ ∀ t, 0 ≤ t → e t + c t = 1 := by
  obtain ⟨s, c, e, p, h, hs, hc, he, hp, -, hE, -, -⟩ :=
    exists_isSolution_nonneg (k₁ := 1) (kb := 1) (k₂ := 1) zero_le_one zero_le_one zero_le_one
      (s₀ := 2) (c₀ := 0) (e₀ := 1) (p₀ := 0) zero_le_two le_rfl zero_le_one le_rfl
  refine ⟨s, c, e, p, h, hc, fun t ht ↦ ?_, fun t ht ↦ by rw [hE t ht]; norm_num⟩
  exact h.complex_pos_of_pos one_pos zero_le_one zero_le_one (by rw [hs]; norm_num) hc.ge
    (by rw [he]; norm_num) hp.ge ht

/-! ### Boundary case: zero substrate

With no substrate and no complex the constant state is an equilibrium: the field vanishes there
and the constant curve satisfies the equations. Both are checked from the definitions. -/

example (k₁ kb k₂ e₀ p₀ : ℝ) : mmField k₁ kb k₂ ![0, 0, e₀, p₀] = 0 := by
  ext i; fin_cases i <;> simp [mmField, substrateRate, complexRate]

/-- The zero-substrate equilibrium with `e ≡ 3`, `p ≡ 1`, verified directly from the definition
of `IsSolution`. -/
theorem zeroSubstrate : IsSolution 2 1 1 (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 3) (fun _ ↦ 1) where
  hasDerivAt_substrate t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp [substrateRate]
  hasDerivAt_complex t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp [complexRate]
  hasDerivAt_enzyme t _ := by
    convert hasDerivAt_const t (3 : ℝ) using 1; simp [complexRate]
  hasDerivAt_product t _ := by
    convert hasDerivAt_const t (1 : ℝ) using 1; simp

/-- Uniqueness identifies the constructed zero-substrate solution with the equilibrium. -/
example {s c e p : ℝ → ℝ} (h : IsSolution 2 1 1 s c e p) (hs : s 0 = 0) (hc : c 0 = 0)
    (he : e 0 = 3) (hp : p 0 = 1) : s 7 = 0 ∧ c 7 = 0 ∧ e 7 = 3 ∧ p 7 = 1 :=
  h.eq_of_initial zeroSubstrate hs hc he hp (by norm_num)

/-! ### Non-vacuity -/

/-- The hypotheses of the invariance theorems are satisfiable: the equilibrium above has
nonnegative data and positive enzyme. -/
example : (0 : ℝ) < 3 :=
  zeroSubstrate.enzyme_pos (t := 4) (by norm_num) zero_le_one zero_le_one le_rfl le_rfl
    (by norm_num) zero_le_one (by norm_num)

/-- With all rate constants and initial data positive, every coordinate of `s`, `c`, `e`
stays positive. -/
example : ∃ s c e p : ℝ → ℝ, IsSolution 1 2 3 s c e p ∧
    ∀ t, 0 ≤ t → 0 < s t ∧ 0 < c t ∧ 0 < e t := by
  obtain ⟨s, c, e, p, h, -, -, -, -, -, -, -, hpos⟩ :=
    exists_isSolution_nonneg (k₁ := 1) (kb := 2) (k₂ := 3) (by norm_num) (by norm_num)
      (by norm_num) (s₀ := 1) (c₀ := 1) (e₀ := 1) (p₀ := 0) zero_le_one zero_le_one zero_le_one
      le_rfl
  exact ⟨s, c, e, p, h, fun t ht ↦ ⟨(hpos t ht).1 one_pos, (hpos t ht).2.1 one_pos,
    (hpos t ht).2.2 one_pos⟩⟩

/-! ### The sign hypotheses are needed

With a negative initial enzyme the constant zero-substrate curve is still a solution (checked
from the definitions) but its enzyme is negative. -/

theorem negEnzyme : IsSolution 1 1 1 (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ -1) (fun _ ↦ 0) where
  hasDerivAt_substrate t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp [substrateRate]
  hasDerivAt_complex t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp [complexRate]
  hasDerivAt_enzyme t _ := by
    convert hasDerivAt_const t (-1 : ℝ) using 1; simp [complexRate]
  hasDerivAt_product t _ := by
    convert hasDerivAt_const t (0 : ℝ) using 1; simp

example : ¬ 0 ≤ (fun _ ↦ (-1 : ℝ)) 1 := by norm_num

end MathlibExtTest.Biology.Dynamics.MichaelisMenten.Trajectories
