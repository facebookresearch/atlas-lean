/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.GroupTheory.Perm.Sign
public import MathlibExt.LinearAlgebra.TensorPower.Quotient

/-!
# Actual weighted place-permutation operators

Every operator is a finite sum of the original tensor-factor permutations.
The coefficient tensor factor is fixed. Uniform maps of the tail module,
arbitrary coefficient maps, and factorwise quotient projections commute
with the operator. No algebra structure on a quotient tail is required.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w v' w'

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {W : Type v'} [AddCommGroup W] [Module k W]
  {M : Type w} [AddCommGroup M] [Module k M]
  {N : Type w'} [AddCommGroup N] [Module k N]

/-- A finite linear combination of actual place permutations, using the inverse-word convention. -/
def permutationOperator (n : ℕ) (c : Equiv.Perm (Fin n) → k) :
    TensorPower k n V →ₗ[k] TensorPower k n V := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n),
    c σ • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap

/-- The original coefficient is fixed by the finite place-permutation sum. -/
def coefficientPermutationOperator (n : ℕ) (c : Equiv.Perm (Fin n) → k) :
    M ⊗[k] TensorPower k n V →ₗ[k] M ⊗[k] TensorPower k n V :=
  TensorProduct.map LinearMap.id (permutationOperator (V := V) n c)

/-- The pure tail word is the actual finite inverse-permutation sum. -/
theorem permutationOperator_tprod (n : ℕ) (c : Equiv.Perm (Fin n) → k)
    (a : Fin n → V) :
    permutationOperator (V := V) n c (PiTensorProduct.tprod k a) =
      ∑ σ : Equiv.Perm (Fin n),
        c σ • PiTensorProduct.tprod k (fun i => a (σ.symm i)) := by
  classical
  simp only [permutationOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod]

/-- Every pure coefficient word has the literal inverse-permutation formula. -/
theorem coefficientPermutationOperator_tprod (n : ℕ) (c : Equiv.Perm (Fin n) → k)
    (m : M) (a : Fin n → V) :
    coefficientPermutationOperator (M := M) (V := V) n c
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ∑ σ : Equiv.Perm (Fin n),
        c σ • (m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => a (σ.symm i))) := by
  classical
  simp only [coefficientPermutationOperator, TensorProduct.map_tmul, LinearMap.id_apply,
    permutationOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul]

/-- Uniform tail maps commute with the actual finite permutation sum. -/
theorem permutationOperator_naturality (n : ℕ) (c : Equiv.Perm (Fin n) → k)
    (g : V →ₗ[k] W) :
    (PiTensorProduct.map (fun _ : Fin n => g)).comp
        (permutationOperator (V := V) n c) =
      (permutationOperator (V := W) n c).comp
        (PiTensorProduct.map (fun _ : Fin n => g)) := by
  classical
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    permutationOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod,
    PiTensorProduct.map_tprod, map_sum, map_smul]

/-- Independent coefficient and uniform tail maps commute with the actual coefficient-fixed operator. -/
theorem coefficientPermutationOperator_naturality (n : ℕ)
    (c : Equiv.Perm (Fin n) → k) (g : V →ₗ[k] W) (f : M →ₗ[k] N) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
        (coefficientPermutationOperator (M := M) (V := V) n c) =
      (coefficientPermutationOperator (M := N) (V := W) n c).comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  unfold coefficientPermutationOperator
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp only [LinearMap.comp_id, LinearMap.id_comp]
  rw [permutationOperator_naturality]

/-- The finite operator commutes with the actual factorwise tensor quotient projection. -/
theorem coefficientQuotientMap_permutationOperator (S : Submodule k V) (n : ℕ)
    (c : Equiv.Perm (Fin n) → k) :
    (coefficientQuotientMap S M n).comp
        (coefficientPermutationOperator (M := M) (V := V) n c) =
      (coefficientPermutationOperator (M := M) (V := V ⧸ S) n c).comp
        (coefficientQuotientMap S M n) :=
  coefficientPermutationOperator_naturality n c S.mkQ LinearMap.id

end TensorPower
