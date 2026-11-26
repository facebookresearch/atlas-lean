/-
Portions of this file are adapted from:

`Theorems/Thm_IsGalois_exists_basis_baseChange_forall_apply_eq_self.lean`
and
`P2M/Sol/S_IsGalois_exists_basis_baseChange_forall_apply_eq_self.lean`
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

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
the proof-extraction machinery is removed, the names are restated in Mathlib
style, and the proofs are adapted to Lean and Mathlib v4.36.0.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct
open Module

section Descent

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {U : Type*} [AddCommGroup U] [Module K U]

local notation "Gal" => (L ≃ₐ[K] L)

variable (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
  (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
  (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u)
include hf

omit [FiniteDimensional K L] in
private theorem f_smul (σ : Gal) (l : L) (x : L ⊗[K] U) :
    f σ (l • x) = σ l • f σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul l' u =>
      rw [TensorProduct.smul_tmul', hf, hf, TensorProduct.smul_tmul', smul_eq_mul,
        smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [FiniteDimensional K L] in
private theorem f_mul (τ σ : Gal) (x : L ⊗[K] U) : f (τ * σ) x = f τ (f σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l u => rw [hf, hf, hf, map_mul, AlgEquiv.mul_apply, mul_apply_eq_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [FiniteDimensional K L] in
private theorem f_one (x : L ⊗[K] U) : f 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul l u => rw [hf, map_one, AlgEquiv.one_apply, one_apply_eq_self]
  | add x y hx hy => simp only [map_add, hx, hy]

private def inv : AddSubgroup (L ⊗[K] U) where
  carrier := {x | ∀ σ : Gal, f σ x = x}
  add_mem' := fun {x y} hx hy σ => by rw [map_add, hx σ, hy σ]
  zero_mem' := fun σ => by rw [map_zero]
  neg_mem' := fun {x} hx σ => by rw [map_neg, hx σ]

omit [FiniteDimensional K L] hf in
private theorem mem_inv {x : L ⊗[K] U} : x ∈ inv f ↔ ∀ σ : Gal, f σ x = x := Iff.rfl

omit [FiniteDimensional K L] in
private theorem sum_mem_inv [Fintype Gal] (x : L ⊗[K] U) :
    ∑ σ : Gal, f σ x ∈ inv f := by
  intro τ
  rw [map_sum]
  simp_rw [← f_mul ρ f hf]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

private theorem one_tmul_mem_span [IsGalois K L] (u : U) :
    (1 : L) ⊗ₜ[K] u ∈ Submodule.span L (inv f : Set (L ⊗[K] U)) := by
  classical
  have : Fintype Gal := Fintype.ofFinite _
  set n := Module.finrank K L with hn
  have hcard : Fintype.card Gal = n := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  set e : Gal ≃ Fin n := Fintype.equivFinOfCardEq hcard with he
  set lam : Fin n → L := fun j => Module.finBasis K L j with hlam
  set A : Matrix (Fin n) (Fin n) L := fun k j => (e.symm k) (lam j) with hA
  have hrows : LinearIndependent L A.row := by
    have hind : LinearIndependent L (fun σ : Gal => (σ : L → L)) :=
      LinearIndependent.comp (ι' := Gal) (linearIndependent_monoidHom L L)
        (fun σ => (σ : L →* L))
        (fun σ τ h => by
          apply AlgEquiv.ext
          intro y
          exact DFunLike.congr_fun h y)
    rw [Fintype.linearIndependent_iff]
    intro d hd k
    have hfun : ∑ k', d k' • ((e.symm k' : Gal) : L → L) = 0 := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hy := (Module.finBasis K L).sum_repr y
      rw [← hy]
      simp only [map_sum, map_smul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : ∑ k', d k' * (e.symm k') (lam j) = 0 := by
        have := congrFun hd j
        simpa [Matrix.row, hA, Finset.sum_apply] using this
      have hthis : ∑ k', d k' * ((Module.finBasis K L).repr y j •
            (e.symm k') ((Module.finBasis K L) j)) =
          (Module.finBasis K L).repr y j • ∑ k', d k' * (e.symm k') (lam j) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]
      rw [hthis, hj, smul_zero]
    have hind' : LinearIndependent L (fun k' : Fin n => ((e.symm k' : Gal) : L → L)) :=
      hind.comp e.symm e.symm.injective
    exact Fintype.linearIndependent_iff.mp hind' d hfun k
  have hunit : IsUnit A := Matrix.linearIndependent_row_iff_isUnit.mp hrows
  set c : Fin n → L := A⁻¹.mulVec (Pi.single (e 1) 1) with hc
  have hAc : A.mulVec c = Pi.single (e 1) 1 := by
    rw [hc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hunit),
      Matrix.one_mulVec]
  have hAc' : ∀ σ : Gal, ∑ j, (σ (lam j)) * c j = if σ = 1 then 1 else 0 := by
    intro σ
    have h := congrFun hAc (e σ)
    simp only [Matrix.mulVec, dotProduct, hA, Equiv.symm_apply_apply] at h
    rw [h, Pi.single_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  have hmem : ∀ j, ∑ σ : Gal, f σ (lam j ⊗ₜ[K] u) ∈ inv f :=
    fun j => sum_mem_inv ρ f hf _
  have hcomb : ∑ j, c j • ∑ σ : Gal, f σ (lam j ⊗ₜ[K] u) = (1 : L) ⊗ₜ[K] u := by
    simp only [hf, Finset.smul_sum]
    rw [Finset.sum_comm]
    have hthis : ∀ σ : Gal, ∑ j, c j • (σ (lam j) ⊗ₜ[K] ρ σ u) =
        (∑ j, σ (lam j) * c j) • ((1 : L) ⊗ₜ[K] ρ σ u) := by
      intro σ
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
        mul_one, mul_comm]
    simp_rw [hthis, hAc']
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      map_one, one_apply_eq_self]
  rw [← hcomb]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span (hmem j))

private theorem span_inv_eq_top [IsGalois K L] :
    Submodule.span L (inv f : Set (L ⊗[K] U)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | tmul l u =>
      have hthis : l ⊗ₜ[K] u = l • ((1 : L) ⊗ₜ[K] u) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hthis]
      exact Submodule.smul_mem _ _ (one_tmul_mem_span ρ f hf u)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Descent

/-- Galois semilinear descent for an induced action: let `L / K` be a finite
Galois extension, `U` a finite-dimensional `K`-vector space, and `ρ` a
`K`-linear representation of `Gal(L/K)` on `U`. If each `f σ` is the additive
map on `L ⊗[K] U` with `f σ (l ⊗ₜ u) = σ l ⊗ₜ ρ σ u`, then `L ⊗[K] U` has an
`L`-basis of `f`-invariant vectors, indexed by `Fin (finrank K U)`. -/
public theorem IsGalois.exists_basis_baseChange_forall_apply_eq_self
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i := by
  classical
  obtain ⟨B, hBsub, hBspan, hBind⟩ :=
    exists_linearIndependent L (inv f : Set (L ⊗[K] U))
  have htop : ⊤ ≤ Submodule.span L (Set.range ((↑) : B → L ⊗[K] U)) := by
    rw [Subtype.range_coe, hBspan, span_inv_eq_top ρ f hf]
  let b₀ : Module.Basis B L (L ⊗[K] U) := Module.Basis.mk hBind htop
  have : Finite B := Module.Basis.finite_index_of_rank_lt_aleph0 (b := b₀)
    (Module.rank_lt_aleph0 L (L ⊗[K] U))
  have : Fintype B := Fintype.ofFinite B
  have hcardB : Fintype.card B = Module.finrank K U := by
    rw [← Module.finrank_eq_card_basis b₀, Module.finrank_baseChange]
  refine ⟨b₀.reindex (Fintype.equivFinOfCardEq hcardB), fun σ i => ?_⟩
  rw [Module.Basis.reindex_apply]
  have hmem : (b₀ ((Fintype.equivFinOfCardEq hcardB).symm i)) ∈
      (inv f : Set (L ⊗[K] U)) := by
    rw [Module.Basis.mk_apply]
    exact hBsub ((Fintype.equivFinOfCardEq hcardB).symm i).2
  exact hmem σ
