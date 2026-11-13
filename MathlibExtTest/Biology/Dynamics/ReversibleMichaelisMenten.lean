/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten

/-! Tests for reversible Michaelis–Menten kinetics: the field on concrete states, the
`k₋₂ = 0` reduction and a concrete detailed-balanced equilibrium (computed from the definitions,
not through the theorems under test), non-vacuity of the existence and equilibrium hypotheses,
and boundary cases showing why `E_T > 0`, `k₋₂ > 0` and nonnegative rates are assumed. -/

namespace MathlibExtTest.Biology.Dynamics.ReversibleMichaelisMenten

open MathlibExt.Biology.Dynamics.MichaelisMenten (substrateRate complexRate mmField)
open MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten

/-! ### Smoke test: the field on concrete states -/

example : revField 1 1 1 1 ![2, 0, 1, 0] = ![-2, 2, -2, 0] := by
  ext i; fin_cases i <;> norm_num [revField, substrateRate, revComplexRate, complexRate,
    revProductRate]

/-- The reverse product step feeds the complex from product and free enzyme. -/
example : revField 1 1 1 1 ![0, 0, 1, 3] = ![0, 3, -3, -3] := by
  ext i; fin_cases i <;> norm_num [revField, substrateRate, revComplexRate, complexRate,
    revProductRate]

example : revCurve (fun _ ↦ 2) (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ 0) 5 = ![2, 0, 1, 0] := rfl

/-- The two conservation laws, read off the field at a concrete state: the `e + c` and
`s + c + p` components of the field sum to zero. -/
example : let v := revField 2 3 5 7 ![1, 2, 3, 4]; v 2 + v 1 = 0 ∧ v 0 + v 1 + v 3 = 0 := by
  norm_num [revField, substrateRate, revComplexRate, complexRate, revProductRate]

/-! ### `k₋₂ = 0` is the irreversible system (computed, not via `revField_zero`) -/

example : revField 2 3 5 0 ![1, 2, 3, 4] = mmField 2 3 5 ![1, 2, 3, 4] := by
  ext i; fin_cases i <;> norm_num [revField, mmField, substrateRate, revComplexRate, complexRate,
    revProductRate]

example : revField 2 3 5 0 = mmField 2 3 5 := revField_zero

/-! ### A concrete detailed-balanced equilibrium

All rate constants `1`, state `(s, c, e, p) = (1, 1/2, 1/2, 1)`: `k₁ e s = 1/2 = k₋₁ c` and
`k₂ c = 1/2 = k₋₂ e p`. Totals `E_T = 1`, `S_T = 5/2`; `p / s = 1 = k₁ k₂ / (k₋₁ k₋₂)`. -/

/-- The field vanishes there, computed coordinate by coordinate. -/
theorem eqState_zero : revField 1 1 1 1 ![1, 1 / 2, 1 / 2, 1] = 0 := by
  ext i; fin_cases i <;> norm_num [revField, substrateRate, revComplexRate, complexRate,
    revProductRate]

example : (1 : ℝ) * (1 / 2) * 1 = 1 * (1 / 2) ∧ (1 : ℝ) * (1 / 2) = 1 * (1 / 2) * 1 := by
  norm_num

/-- The Haldane ratio at the concrete equilibrium, by arithmetic. -/
example : (1 : ℝ) / 1 = 1 * 1 / (1 * 1) := by norm_num

/-- Consumer use of `haldane_div` on the concrete equilibrium. -/
example : (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 3 / (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 0 =
    1 * 1 / (1 * 1) :=
  haldane_div eqState_zero (by norm_num) (by norm_num) one_ne_zero one_ne_zero

/-- The constant curve at the concrete equilibrium is a solution, checked from the definition
of `IsSolution` (not via `isSolution_const_iff`). -/
theorem isSolution_eqState :
    IsSolution 1 1 1 1 (fun _ ↦ 1) (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2) (fun _ ↦ 1) where
  hasDerivAt_substrate t _ := by
    convert hasDerivAt_const t (1 : ℝ) using 1; norm_num [substrateRate]
  hasDerivAt_complex t _ := by
    convert hasDerivAt_const t (1 / 2 : ℝ) using 1
    norm_num [revComplexRate, complexRate]
  hasDerivAt_enzyme t _ := by
    convert hasDerivAt_const t (1 / 2 : ℝ) using 1
    norm_num [revComplexRate, complexRate]
  hasDerivAt_product t _ := by
    convert hasDerivAt_const t (1 : ℝ) using 1; norm_num [revProductRate]

/-! ### Non-vacuity -/

/-- `existsUnique_equilibrium` applies (positive rates and totals), and its unique equilibrium in
the class `E_T = 1`, `S_T = 5/2` is the concrete state above. -/
example : ∀ y : Fin 4 → ℝ, (∀ i, 0 ≤ y i) → y 2 + y 1 = 1 → y 0 + y 1 + y 3 = 5 / 2 →
    revField 1 1 1 1 y = 0 → y = ![1, 1 / 2, 1 / 2, 1] := by
  intro y hy hE hS h0
  obtain ⟨x, -, hx⟩ := existsUnique_equilibrium (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1)
    one_pos one_pos one_pos one_pos (eT := 1) (sT := 5 / 2) one_pos (by norm_num)
  have hstate : (∀ i, 0 ≤ (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) i) ∧
      (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 2 + (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 1 = 1 ∧
      (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 0 + (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 1 +
        (![1, 1 / 2, 1 / 2, 1] : Fin 4 → ℝ) 3 = 5 / 2 ∧
      revField 1 1 1 1 ![1, 1 / 2, 1 / 2, 1] = 0 := by
    refine ⟨fun i ↦ ?_, by norm_num, by norm_num, eqState_zero⟩
    fin_cases i <;> norm_num
  rw [hx y ⟨hy, hE, hS, h0⟩, hx _ hstate]

/-- Global existence applies to a nonnegative, unprepared start (no complex, no product) and
yields both conservation laws. -/
example : ∃ s c e p : ℝ → ℝ, IsSolution 1 1 1 1 s c e p ∧ c 0 = 0 ∧ p 0 = 0 ∧
    ∀ t, 0 ≤ t → e t + c t = 1 ∧ s t + c t + p t = 2 ∧ 0 ≤ p t := by
  obtain ⟨s, c, e, p, h, -, hc, -, hp, hnn, hE, hS⟩ :=
    exists_isSolution_nonneg (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1) zero_le_one zero_le_one
      zero_le_one zero_le_one (s₀ := 2) (c₀ := 0) (e₀ := 1) (p₀ := 0) zero_le_two le_rfl
      zero_le_one le_rfl
  refine ⟨s, c, e, p, h, hc, hp, fun t ht ↦ ⟨?_, ?_, (hnn t ht).2.2.2⟩⟩
  · rw [hE t ht]; norm_num
  · rw [hS t ht]; norm_num

/-- A solution started at the concrete equilibrium stays there. -/
example {t : ℝ} (ht : 0 ≤ t) : (fun _ : ℝ ↦ (1 / 2 : ℝ)) t = 1 / 2 :=
  (isSolution_eqState.eq_of_equilibrium (by simpa using eqState_zero) ht).2.1

/-! ### Boundary cases -/

/-- **`E_T = 0`: uniqueness fails.** With no enzyme, `(S_T, 0, 0, 0)` and `(0, 0, 0, S_T)` are
two distinct nonnegative equilibria in the same class `E_T = 0`, `S_T = 1`, so the hypothesis
`0 < eT` of `existsUnique_equilibrium` is needed. Computed from the definitions. -/
example : revField 1 1 1 1 ![1, 0, 0, 0] = 0 ∧ revField 1 1 1 1 ![0, 0, 0, 1] = 0 ∧
    (![1, 0, 0, 0] : Fin 4 → ℝ) ≠ ![0, 0, 0, 1] := by
  refine ⟨?_, ?_, fun h ↦ by simpa using congrFun h 0⟩ <;>
  · ext i; fin_cases i <;> norm_num [revField, substrateRate, revComplexRate, complexRate,
      revProductRate]

/-- **`k₋₂ = 0`: no positive equilibrium.** In the irreversible limit the concrete
detailed-balanced state is not an equilibrium (product keeps forming), so the hypothesis
`0 < kb₂` of `existsUnique_equilibrium` / `pos_of_equilibrium` is needed. -/
example : revField 1 1 1 0 ![1, 1 / 2, 1 / 2, 1] ≠ 0 := by
  intro h
  have := congrFun h 3
  norm_num [revField, revProductRate] at this

/-- In the irreversible limit the equilibrium of the class `E_T = 1`, `S_T = 1` has all
substrate converted: `(0, 0, 1, 1)`. -/
example : revField 1 1 1 0 ![0, 0, 1, 1] = 0 := by
  ext i; fin_cases i <;> norm_num [revField, substrateRate, revComplexRate, complexRate,
    revProductRate]

/-- **A negative rate breaks orthant invariance.** With `k₋₁ = -1`, at the nonnegative state
`(0, 1, 0, 0)` the substrate rate is `-1 < 0`, so the field leaves the orthant through the face
`s = 0`; the sign hypotheses of `exists_isSolution_nonneg` are needed. -/
example : revField 1 (-1) 1 1 ![0, 1, 0, 0] 0 < 0 := by
  norm_num [revField, substrateRate]

end MathlibExtTest.Biology.Dynamics.ReversibleMichaelisMenten
