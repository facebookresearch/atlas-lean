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

/-- exactSource consumer: the constant coefficient of a cusp form on `Γ₀(N)` vanishes. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularFormClass.qCoeff f 0 = 0 :=
  CuspForm.qCoeff_zero f

/-- exactSource consumer: vanishing of an eigen-sequence with vanishing first coefficient. -/
example (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 :=
  ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero k N a c hT hU h1

/-- exactSource consumer: the eigenvalues of a normalized eigen-sequence. -/
example (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p :=
  ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one k N a c hT hU h1

/-- The indicator `δ₀` of `0`: `T p` scales it by `1 + p ^ (k - 1)` and `U p` by `1`. -/
private theorem coeffHecke_indicator_zero (k : ℤ) (N : ℕ) :
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeT k p (fun m => if m = 0 then 1 else 0) n =
        (if p ∣ N then 1 else 1 + (p : ℂ) ^ (k - 1)) * (if n = 0 then 1 else 0)) ∧
    (∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeU p (fun m => if m = 0 then 1 else 0) n =
        (if p ∣ N then 1 else 1 + (p : ℂ) ^ (k - 1)) * (if n = 0 then 1 else 0)) := by
  refine ⟨fun p hp hpN n => ?_, fun p hp hpN n => ?_⟩
  · rw [ModularForm.coeffHeckeT_apply, ite_eq_right hpN]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnp : n * p ≠ 0 := mul_ne_zero hn hp.ne_zero
      by_cases hpn : p ∣ n
      · have hq : n / p ≠ 0 :=
          (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos).ne'
        simp [hnp, hn, hpn, hq]
      · simp [hnp, hn, hpn]
  · rw [ModularForm.coeffHeckeU_apply, ite_eq_left hpN, one_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [mul_ne_zero hn hp.ne_zero, hn]

/-- Concrete instance and boundary: `δ₀` is an eigenvector of every coefficient operator with
`δ₀ 1 = 0`, so its coefficients of positive index vanish; `δ₀ 0 = 1` shows that the index `0`
must be excluded. -/
example (k : ℤ) (N : ℕ) :
    (∀ n : ℕ, n ≠ 0 → (fun m : ℕ => if m = 0 then (1 : ℂ) else 0) n = 0) ∧
      (fun m : ℕ => if m = 0 then (1 : ℂ) else 0) 0 ≠ 0 :=
  ⟨ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero k N _ _
    (coeffHecke_indicator_zero k N).1 (coeffHecke_indicator_zero k N).2 (by simp), by simp⟩

/-- Concrete instance: at level `0` every prime divides the level, and the sequence `n ↦ n` is an
eigenvector of every `U p`, with eigenvalue `p`, equal to its `p`-th coefficient. -/
example (k : ℤ) : ∀ p : ℕ, p.Prime → (fun q : ℕ => (q : ℂ)) p = (fun n : ℕ => (n : ℂ)) p :=
  ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one k 0 (fun n => (n : ℂ))
    (fun q => (q : ℂ)) (fun _ _ h => (h (dvd_zero _)).elim)
    (fun p _ _ n => by rw [ModularForm.coeffHeckeU_apply]; push_cast; ring) (by simp)
