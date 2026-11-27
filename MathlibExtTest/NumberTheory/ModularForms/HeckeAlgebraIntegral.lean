/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
The source statements restated in this file are copied from
`Theorems/Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean`,
`Theorems/Thm_CuspForm_exists_coe_eq_heckeT.lean`,
`Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean`,
`Theorems/Thm_CuspForm_linearIndependent_of_mem_intLattice.lean`,
`Theorems/Thm_IsIntegral_of_mem_span_of_apply_eq_smul.lean`,
`Theorems/Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom.lean`, and
`Theorems/Thm_exists_integralClosure_coe_eq_of_isIntegral.lean`
in https://github.com/anthropics/fermats-last-theorem, compared with the source files at
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebraIntegral

@[expose] public section

/-- exactSource restatement, from `CuspForm.heckeTLin` and `CuspForm.coe_heckeTLin_apply`. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f :=
  ⟨CuspForm.heckeTLin k hp hpN f, CuspForm.coe_heckeTLin_apply k hp hpN f⟩

/-- exactSource restatement, from `CuspForm.heckeULin` and `CuspForm.coe_heckeULin_apply`. -/
example {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ}
    (hpN : p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  ⟨CuspForm.heckeULin k hpN f, CuspForm.coe_heckeULin_apply k hpN f⟩

/-- exactSource consumer: the original binders apply verbatim. -/
example {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Submodule ℤ V) (hfg : L.FG)
    (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) {v : V} (hv : v ∈ Submodule.span ℂ (L : Set V))
    (hv0 : v ≠ 0) {c : ℂ} (hTv : T v = c • v) : IsIntegral ℤ c :=
  IsIntegral.of_mem_span_of_apply_eq_smul L hfg T hTL hv hv0 hTv

/-- exactSource restatement, from Mathlib's `mem_integralClosure_iff`. -/
example {z : ℂ} (hz : IsIntegral ℤ z) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = z :=
  ⟨⟨z, (mem_integralClosure_iff ℤ ℂ).mpr hz⟩, rfl⟩

/-- exactSource restatement, from Mathlib's `LinearMap.ext_on`. -/
example {N : ℕ} {k : ℤ} (hN : CuspForm.HasIntegralStructure N k)
    (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k))
    (h : ∀ f ∈ CuspForm.intLattice N k, t f = 0) : t = 0 :=
  LinearMap.ext_on hN fun f hf => by rw [LinearMap.zero_apply]; exact h f hf

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (f : Fin n → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : ∀ i, f i ∈ CuspForm.intLattice N k) (h : LinearIndependent ℤ f) :
    LinearIndependent ℂ f :=
  CuspForm.linearIndependent_of_mem_intLattice n f hf h

/-- exactSource consumer: the original binders apply verbatim. -/
example {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [CommRing T]
    (ρ : T →+* Module.End K V) (L : Submodule ℤ V) (hL : L.FG)
    (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L) (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0)
    (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y →
      LinearIndependent K y)
    (χ : T →+* K) : ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v :=
  Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom ρ L hL hstab hfaith hfree χ

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k)
    {S : Set ℕ} (χ : CuspForm.heckeAlgebra N k S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧
      ∀ t : CuspForm.heckeAlgebra N k S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f :=
  CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul hN hk χ

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k)
    (S : Set ℕ) : Module.Finite ℤ (CuspForm.heckeAlgebra N k S) :=
  CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN hk S

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k)
    (S : Set ℕ) : Module.Free ℤ (CuspForm.heckeAlgebra N k S) :=
  CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra hN hk S

/-- Boundary case: the weight-two Hecke algebra away from the level, as used downstream. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
  hN.moduleFinite_heckeAlgebra one_le_two _

/-- Boundary case: the identity on `ℂ` stabilizes the lattice `ℤ ⊆ ℂ`, so its eigenvalue `1`
is integral. -/
example : IsIntegral ℤ (1 : ℂ) := by
  have hv : (1 : ℂ) ∈ Submodule.span ℂ ((Submodule.span ℤ {(1 : ℂ)} : Submodule ℤ ℂ) : Set ℂ) :=
    Submodule.subset_span (Submodule.subset_span rfl)
  exact IsIntegral.of_mem_span_of_apply_eq_smul (Submodule.span ℤ {(1 : ℂ)})
    (Submodule.fg_span_singleton _) LinearMap.id (fun _ hx => hx) hv one_ne_zero (by simp)
