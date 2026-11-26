/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.NormalizedEigenform

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N]
    (h : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g ≠ 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform :=
  CuspForm.exists_isNormalizedEigenform h

/-- exactSource consumer: finite-dimensionality of `S_k(Γ₀(N))`. -/
example (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  CuspForm.finiteDimensional_Gamma0 N k

/-- Finite-dimensionality of `S_k(Γ₀(N))` is found by instance search. -/
example (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  inferInstance

/-- The source statement that `T p` preserves `S_k(Γ₀(N))` for a prime `p ∤ N` is met by
`CuspForm.heckeTLin`. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f :=
  ⟨CuspForm.heckeTLin k hp hpN f, CuspForm.coe_heckeTLin_apply k hp hpN f⟩

/-- The source statement that `U p` preserves `S_k(Γ₀(N))` for `p ∣ N` is met by
`CuspForm.heckeULin`. -/
example {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ}
    (hpN : p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  ⟨CuspForm.heckeULin k hpN f, CuspForm.coe_heckeULin_apply k hpN f⟩

/-- exactSource consumer: the coefficient characterization of normalized eigenforms. -/
example {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
      ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧
        (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n))) :=
  CuspForm.isNormalizedEigenform_iff_coeffHecke f

/-- Boundary: the witness cannot be the zero form, whose first coefficient is `0`.
This is why the theorem needs a nonzero cusp form. -/
example {N : ℕ} : ¬ (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2).IsNormalizedEigenform := by
  intro h
  have h1 := h.qCoeff_one
  have h0 := CuspForm.qCoeff_smul (N := N) (k := 2) 0 0 1
  rw [zero_smul, zero_mul] at h0
  rw [h0] at h1
  exact zero_ne_one h1
