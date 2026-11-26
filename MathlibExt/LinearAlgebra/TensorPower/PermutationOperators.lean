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
# Weighted place-permutation operators

For a commutative ring k, a k-module V and c : Sₙ → k, the operator O_c on V⊗n is ∑σ c(σ)ρₙ(σ),
where ρₙ(σ)tprod(a) = tprod(a ∘ σ⁻¹). On M ⊗ V⊗n the analogous sum fixes the coefficient in a
k-module M. These operators commute with coefficient maps, uniform maps of tensor factors and
quotient maps V → V/S for submodules S.

For the permutation functoriality of tensor powers, see N. Bourbaki, Algebra I, Chapter III.
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

/-- A weighted sum of place permutations.

For a commutative ring k, a k-module V and c : Sₙ → k, O_c : V⊗n → V⊗n is ∑σ c(σ)ρₙ(σ). The
permutation action sends a tensor word a to a ∘ σ⁻¹. -/
def permutationOperator (n : ℕ) (c : Equiv.Perm (Fin n) → k) :
    TensorPower k n V →ₗ[k] TensorPower k n V := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n),
    c σ • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap

/-- A weighted permutation sum with a fixed coefficient.

For a commutative ring k, k-modules M,V and c : Sₙ → k, this endomorphism of M ⊗ V⊗n is ∑σ
c(σ)(id_M ⊗ ρₙ(σ)), so each summand retains the coefficient in M. -/
def coefficientPermutationOperator (n : ℕ) (c : Equiv.Perm (Fin n) → k) :
    M ⊗[k] TensorPower k n V →ₗ[k] M ⊗[k] TensorPower k n V :=
  TensorProduct.map LinearMap.id (permutationOperator (V := V) n c)

/-- The inverse-permutation formula on a pure tensor.

For a commutative ring k, a k-module V, c : Sₙ → k and a : Fin n → V, O_c(tprod(a)) = ∑σ
c(σ) · tprod(a ∘ σ⁻¹). -/
theorem permutationOperator_tprod (n : ℕ) (c : Equiv.Perm (Fin n) → k)
    (a : Fin n → V) :
    permutationOperator (V := V) n c (PiTensorProduct.tprod k a) =
      ∑ σ : Equiv.Perm (Fin n),
        c σ • PiTensorProduct.tprod k (fun i => a (σ.symm i)) := by
  classical
  simp only [permutationOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod]

/-- The weighted formula on a coefficient tensor word.

For a commutative ring k, k-modules M,V, c : Sₙ → k, m ∈ M and a : Fin n → V, O_c(m ⊗
tprod(a)) = ∑σ c(σ) · (m ⊗ tprod(a ∘ σ⁻¹)). -/
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

/-- Naturality of a weighted permutation sum.

For a commutative ring k, a k-linear map g : V → W and c : Sₙ → k, g⊗n ∘ O_c,V = O_c,W ∘
g⊗n. -/
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

/-- Naturality in a coefficient and uniform tensor factors.

For a commutative ring k, k-linear maps f : M → N and g : V → W, and c : Sₙ → k, T = f ⊗ g⊗n
satisfies T ∘ O_c,M,V = O_c,N,W ∘ T. The modules may have independent universes. -/
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

/-- Weighted permutations descend through a factorwise quotient.

For a commutative ring k, k-modules M,V and a submodule S ≤ V, let q : V → V/S and T = id_M
⊗ q⊗n. For every c : Sₙ → k, T ∘ O_c,M,V = O_c,M,V/S ∘ T. -/
theorem coefficientQuotientMap_permutationOperator (S : Submodule k V) (n : ℕ)
    (c : Equiv.Perm (Fin n) → k) :
    (coefficientQuotientMap S M n).comp
        (coefficientPermutationOperator (M := M) (V := V) n c) =
      (coefficientPermutationOperator (M := M) (V := V ⧸ S) n c).comp
        (coefficientQuotientMap S M n) :=
  coefficientPermutationOperator_naturality n c S.mkQ LinearMap.id

end TensorPower
