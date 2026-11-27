/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_IsGalois_exists_basis_baseChange_forall_apply_eq_self.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.FieldTheory.Galois.SemilinearDescent
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

open scoped TensorProduct

-- Consumer with the original binders.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i :=
  IsGalois.exists_basis_baseChange_forall_apply_eq_self ρ f hf

-- Higher-universe consumer.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] {U : Type 1} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i :=
  IsGalois.exists_basis_baseChange_forall_apply_eq_self ρ f hf

/-! ### Boundary: the semilinear hypothesis `hf` cannot be dropped

Model: `K = ℝ`, `L = ℂ`, `U = ℝ`, where `σ` acts on `U` by the determinant of
`σ` as a real linear map (`signChar`, with `signChar conj = -1`). The untwisted
action `untwisted σ = id ⊗ signChar σ` meets every hypothesis of
`IsGalois.exists_basis_baseChange_forall_apply_eq_self` except `hf`, and no
basis is invariant under it. The twisted action `σ ⊗ signChar σ` of the same
character satisfies `hf`, and no vector of its invariant basis lies on the real
line `ℝ ⊗ U`. -/

/-- `ℂ / ℝ` is Galois: separable since `ℝ` is perfect, and normal since every
complex polynomial splits. -/
private instance isGalois_real_complex : IsGalois ℝ ℂ := by
  rw [isGalois_iff]
  refine ⟨inferInstance, ?_⟩
  rw [normal_iff]
  intro x
  exact ⟨IsIntegral.of_finite ℝ x, IsAlgClosed.splits _⟩

/-- `σ` acts on `U = ℝ` by the determinant of `σ` as a real linear map. -/
private noncomputable def signChar : (ℂ ≃ₐ[ℝ] ℂ) →* (ℝ →ₗ[ℝ] ℝ) :=
  (algebraMap ℝ (Module.End ℝ ℝ)).toMonoidHom.comp
    (LinearMap.det.comp (AlgEquiv.toLinearMapHom ℝ ℂ))

private theorem signChar_conj : signChar Complex.conjAe = -1 := by
  have hdet : LinearMap.det (AlgEquiv.toLinearMapHom ℝ ℂ Complex.conjAe) = -1 :=
    Complex.det_conjAe
  change algebraMap ℝ (Module.End ℝ ℝ)
    (LinearMap.det (AlgEquiv.toLinearMapHom ℝ ℂ Complex.conjAe)) = -1
  rw [hdet, map_neg, map_one]

/-- The untwisted action: `σ` acts on the factor `U` only. -/
private noncomputable def untwisted (σ : ℂ ≃ₐ[ℝ] ℂ) : ℂ ⊗[ℝ] ℝ →+ ℂ ⊗[ℝ] ℝ :=
  (TensorProduct.map LinearMap.id (signChar σ)).toAddMonoidHom

/-- The twisted action: `σ` acts on both factors, as `hf` requires. -/
private noncomputable def twisted (σ : ℂ ≃ₐ[ℝ] ℂ) : ℂ ⊗[ℝ] ℝ →+ ℂ ⊗[ℝ] ℝ :=
  (TensorProduct.map σ.toLinearMap (signChar σ)).toAddMonoidHom

private theorem twisted_tmul (σ : ℂ ≃ₐ[ℝ] ℂ) (l : ℂ) (u : ℝ) :
    twisted σ (l ⊗ₜ[ℝ] u) = σ l ⊗ₜ[ℝ] signChar σ u :=
  TensorProduct.map_tmul _ _ _ _

private theorem eq_zero_of_neg_eq_self {x : ℂ ⊗[ℝ] ℝ} (h : -x = x) : x = 0 := by
  have h' := congrArg (TensorProduct.rid ℝ ℂ) h
  rw [map_neg, CharZero.neg_eq_self_iff] at h'
  exact (TensorProduct.rid ℝ ℂ).map_eq_zero_iff.mp h'

/-- Complex conjugation acts by `-1` under the untwisted action. -/
private theorem untwisted_conj (x : ℂ ⊗[ℝ] ℝ) : untwisted Complex.conjAe x = -x := by
  induction x using TensorProduct.inductionOn with
  | tmul l u =>
      change TensorProduct.map LinearMap.id (signChar Complex.conjAe) (l ⊗ₜ[ℝ] u) = _
      rw [TensorProduct.map_tmul, signChar_conj, LinearMap.id_apply, LinearMap.neg_apply,
        one_apply_eq_self, TensorProduct.tmul_neg]
  | add x y hx hy => rw [map_add, hx, hy, neg_add]

/-- The untwisted action fails `hf` at `σ = conj`, `l = i`, `u = 1`. -/
private theorem untwisted_not_hf :
    ¬ ∀ (σ : ℂ ≃ₐ[ℝ] ℂ) (l : ℂ) (u : ℝ),
      untwisted σ (l ⊗ₜ[ℝ] u) = σ l ⊗ₜ[ℝ] signChar σ u := by
  intro h
  have h' := h Complex.conjAe Complex.I 1
  rw [untwisted_conj, Complex.conjAe_coe, Complex.conj_I, signChar_conj, LinearMap.neg_apply,
    one_apply_eq_self, TensorProduct.tmul_neg, TensorProduct.neg_tmul, neg_neg] at h'
  have h1 := congrArg (TensorProduct.rid ℝ ℂ) (eq_zero_of_neg_eq_self h')
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h1
  exact Complex.I_ne_zero h1

/-- No basis of `ℂ ⊗[ℝ] ℝ` is invariant under the untwisted action. -/
private theorem untwisted_no_invariant_basis :
    ¬ ∃ b : Module.Basis (Fin (Module.finrank ℝ ℝ)) ℂ (ℂ ⊗[ℝ] ℝ),
      ∀ (σ : ℂ ≃ₐ[ℝ] ℂ) (i : Fin (Module.finrank ℝ ℝ)), untwisted σ (b i) = b i := by
  rintro ⟨b, hb⟩
  obtain ⟨i⟩ : Nonempty (Fin (Module.finrank ℝ ℝ)) := ⟨⟨0, by simp⟩⟩
  have h := hb Complex.conjAe i
  rw [untwisted_conj] at h
  exact b.ne_zero i (eq_zero_of_neg_eq_self h)

/-- Boundary: the theorem with `hf` removed is false; the untwisted action
refutes it. -/
example : ¬ ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (_ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U)) (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U),
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i :=
  fun h => untwisted_no_invariant_basis (h ℝ ℂ ℝ signChar untwisted)

/-- With `hf` restored (the twisted action), the theorem gives an invariant
basis, and none of its vectors lies on the real line `ℝ ⊗ U`. -/
example : ∃ b : Module.Basis (Fin (Module.finrank ℝ ℝ)) ℂ (ℂ ⊗[ℝ] ℝ),
    (∀ (σ : ℂ ≃ₐ[ℝ] ℂ) (i : Fin (Module.finrank ℝ ℝ)), twisted σ (b i) = b i) ∧
      ∀ (i : Fin (Module.finrank ℝ ℝ)) (r : ℝ), b i ≠ (r : ℂ) ⊗ₜ[ℝ] (1 : ℝ) := by
  obtain ⟨b, hb⟩ :=
    IsGalois.exists_basis_baseChange_forall_apply_eq_self signChar twisted twisted_tmul
  refine ⟨b, hb, fun i r hr => b.ne_zero i (eq_zero_of_neg_eq_self ?_)⟩
  have h := hb Complex.conjAe i
  rw [hr, twisted_tmul, Complex.conjAe_coe, Complex.conj_ofReal, signChar_conj,
    LinearMap.neg_apply, one_apply_eq_self, TensorProduct.tmul_neg] at h
  rw [hr]
  exact h
