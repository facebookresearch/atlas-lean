/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one.lean`
and
`P2M/Sol/S_Module_Invertible_of_projective_of_forall_finrank_eq_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.Invertible.RankOneAux

variable {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]

private lemma mul_comm_of_equiv {B : Type*} [CommRing B] {L : Type*} [AddCommGroup L]
    [Module B L] (e : B ≃ₗ[B] L) (f g : Module.Dual B L) (l l' : L) :
    f l * g l' = f l' * g l := by
  obtain ⟨a, rfl⟩ := e.surjective l
  obtain ⟨b, rfl⟩ := e.surjective l'
  have ha : e a = a • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  have hb : e b = b • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  rw [ha, hb]
  simp only [map_smul, smul_eq_mul]
  ring

variable [Module.Finite A P] [Module.Projective A P]
  (h : ∀ (K : Type u) [Field K] [Algebra A K],
    Module.finrank K (TensorProduct A K P) = 1)

include h in
private lemma finrank_localization_eq_one (m : Ideal A) [m.IsMaximal] :
    Module.finrank (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] P) = 1 := by
  have _ : Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] P) :=
    Module.free_of_flat_of_isLocalRing
  have h1 := h (IsLocalRing.ResidueField (Localization.AtPrime m))
  have h2 := Module.finrank_baseChange
    (R := IsLocalRing.ResidueField (Localization.AtPrime m))
    (S := Localization.AtPrime m) (M' := Localization.AtPrime m ⊗[A] P)
  rw [← h2, (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime m)
    (IsLocalRing.ResidueField (Localization.AtPrime m))
    (IsLocalRing.ResidueField (Localization.AtPrime m)) P).finrank_eq]
  exact h1

include h in
private lemma apply_mul_apply_comm (φ ψ : Module.Dual A P) (p q : P) :
    φ p * ψ q = φ q * ψ p := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro m hm
  have _ : m.IsMaximal := hm
  set B := Localization.AtPrime m
  have _ : Module.Free B (B ⊗[A] P) := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one
    (finrank_localization_eq_one h m)
  have hΦ : ∀ x : P, φ.baseChange B (1 ⊗ₜ x) = algebraMap A B (φ x) := fun x ↦ by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  have hΨ : ∀ x : P, ψ.baseChange B (1 ⊗ₜ x) = algebraMap A B (ψ x) := fun x ↦ by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  have key := mul_comm_of_equiv e (φ.baseChange B) (ψ.baseChange B) (1 ⊗ₜ p) (1 ⊗ₜ q)
  rw [hΦ, hΦ, hΨ, hΨ] at key
  rw [map_sub, map_mul, map_mul, key, sub_self]

omit h in
private lemma exists_dualBasis :
    ∃ (n : ℕ) (x : Fin n → P) (φ : Fin n → Module.Dual A P),
      ∀ p : P, ∑ i, φ i p • x i = p := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A P
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun i ↦ f (Pi.single i 1), fun i ↦ (LinearMap.proj i).comp g, fun p ↦ ?_⟩
  have hfg : f (g p) = p := congrArg (fun φ => φ p) hg
  have hgp : ∑ i, (g p i) • (Pi.single i (1 : A) : Fin n → A) = g p := by
    simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
    exact Finset.univ_sum_single (g p)
  conv_rhs => rw [← hfg, ← hgp]
  simp [map_sum, map_smul]

include h in
private lemma surjective_contractLeft :
    Function.Surjective (contractLeft A P) := by
  obtain ⟨n, x, φ, hx⟩ := exists_dualBasis (A := A) (P := P)
  rw [← LinearMap.range_eq_top]
  by_contra hT
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal _ hT
  let _ := Ideal.Quotient.field m
  have hP : (⊤ : Submodule A P) ≤ m • ⊤ := by
    rintro p -
    rw [← hx p]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem_smul
        (hTm ⟨φ i ⊗ₜ p, contractLeft_apply (φ i) p⟩) Submodule.mem_top
  have hs : Subsingleton ((A ⧸ m) ⊗[A] P) := by
    refine (TensorProduct.quotTensorEquivQuotSMul P m).toEquiv.subsingleton_congr.mpr ?_
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    exact hP
  have h1 := h (A ⧸ m)
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

include h in
private lemma injective_contractLeft :
    Function.Injective (contractLeft A P) := by
  obtain ⟨n, x, φ, hx⟩ := exists_dualBasis (A := A) (P := P)
  let u : Module.Dual A P ⊗[A] P := ∑ i, φ i ⊗ₜ x i
  have hu : (contractLeft A P).smulRight u = LinearMap.id := by
    refine TensorProduct.ext' fun ψ p ↦ ?_
    simp only [LinearMap.smulRight_apply, contractLeft_apply,
      LinearMap.id_apply]
    have hφ : ∀ i, ψ p • φ i = φ i p • ψ := fun i ↦ by
      ext q
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [mul_comm (φ i p), apply_mul_apply_comm h ψ (φ i) p q]
    calc ψ p • u = ∑ i, (ψ p • φ i) ⊗ₜ[A] x i := by
            simp only [u, Finset.smul_sum, TensorProduct.smul_tmul']
      _ = ∑ i, ψ ⊗ₜ[A] (φ i p • x i) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [hφ i, TensorProduct.smul_tmul]
      _ = ψ ⊗ₜ[A] ∑ i, φ i p • x i := by rw [TensorProduct.tmul_sum]
      _ = ψ ⊗ₜ[A] p := by rw [hx]
  intro t₁ t₂ ht
  have h₁ : contractLeft A P t₁ • u = t₁ := congrArg (fun φ => φ t₁) hu
  have h₂ : contractLeft A P t₂ • u = t₂ := congrArg (fun φ => φ t₂) hu
  rw [← h₁, ← h₂, ht]

end Module.Invertible.RankOneAux

namespace Module

/-- A finite projective module whose base change to every field has rank
one is invertible.

This is the standard criterion for a module to define a line bundle: it
is used to show that projective modules of constant rank one are
invertible, to construct Picard group elements, and to recognize
invertible sheaves from their fibers. -/
theorem Invertible.of_projective_of_forall_finrank_eq_one {A : Type u} [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K],
      Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P :=
  ⟨⟨Module.Invertible.RankOneAux.injective_contractLeft h,
    Module.Invertible.RankOneAux.surjective_contractLeft h⟩⟩

end Module
