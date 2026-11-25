/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.AdelicLiftExists

@[expose] public section

open NumberField
open scoped ModularForm

/-- Consumer with the original binders. -/
private theorem exactSource {M : ℕ} (hM : M ≠ 0) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ φ : NumberField.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ, g.IsAdelicLiftOf φ :=
  CuspForm.exists_isAdelicLiftOf hM g

/-- The lift is not vacuous: at the identity it takes the value of the cusp form at `i`. -/
example {M : ℕ} (hM : M ≠ 0) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ, g.IsAdelicLiftOf φ ∧
      φ 1 = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 1) UpperHalfPlane.I := by
  obtain ⟨φ, hφ⟩ := CuspForm.exists_isAdelicLiftOf hM g
  refine ⟨φ, hφ, hφ.apply_eq 1 (map_one _) ?_⟩
  unfold LanglandsTunnell.ratArchGL2
  rw [map_one, map_one, map_one]
  exact one_mem _
