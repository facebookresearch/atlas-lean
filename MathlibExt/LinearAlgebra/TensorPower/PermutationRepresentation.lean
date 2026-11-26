/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.PermutationOperators
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Permutation representations on coefficient tensors

Let k be a commutative ring and M,V k-modules. A permutation σ ∈ Sₙ acts on V⊗n by tprod(a) ↦
tprod(a ∘ σ⁻¹). Tensoring this representation with id_M fixes the coefficient in M. Its
k[Sₙ]-linear extension is an algebra homomorphism to End_k(M ⊗ V⊗n), so multiplication is
composition and the group-algebra unit acts as the identity. If k is a ℚ-algebra, rational
coefficients act through ℚ → k.

For tensor permutation representations, see N. Bourbaki, Algebra I, Chapter III.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- The place-permutation representation of a tensor power.

For a commutative ring k and a k-module V, ρₙ : Sₙ → End_k(V⊗n) sends σ to the reindexing
map a ↦ a ∘ σ⁻¹ on pure tensor words. It preserves the identity and permutation
multiplication. -/
def permutationRepresentation (n : ℕ) :
    Equiv.Perm (Fin n) →* Module.End k (TensorPower k n V) where
  toFun σ := (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap
  map_one' := by
    change (PiTensorProduct.reindex k (fun _ : Fin n => V) (Equiv.refl (Fin n))).toLinearMap =
      LinearMap.id
    rw [PiTensorProduct.reindex_refl]
    rfl
  map_mul' σ τ := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    change PiTensorProduct.reindex k (fun _ : Fin n => V) (σ * τ) (PiTensorProduct.tprod k a) =
      PiTensorProduct.reindex k (fun _ : Fin n => V) σ
        (PiTensorProduct.reindex k (fun _ : Fin n => V) τ (PiTensorProduct.tprod k a))
    simp only [PiTensorProduct.reindex_tprod]
    rfl

/-- The tensor-word formula for a place permutation.

For a commutative ring k, a k-module V, σ ∈ Sₙ and a : Fin n → V, ρₙ(σ)(tprod(a)) = tprod(a
∘ σ⁻¹). -/
theorem permutationRepresentation_tprod (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : Fin n → V) :
    permutationRepresentation (k := k) (V := V) n σ (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun i => a (σ.symm i)) := by
  change PiTensorProduct.reindex k (fun _ : Fin n => V) σ (PiTensorProduct.tprod k a) = _
  simp only [PiTensorProduct.reindex_tprod]

/-- The permutation representation with a fixed coefficient factor.

For a commutative ring k and k-modules M,V, ρₙ,M : Sₙ → End_k(M ⊗ V⊗n) is σ ↦ id_M ⊗ ρₙ(σ).
It is a monoid homomorphism and fixes the coefficient in M. -/
def coefficientPermutationRepresentation (n : ℕ) :
    Equiv.Perm (Fin n) →* Module.End k (M ⊗[k] TensorPower k n V) where
  toFun σ := TensorProduct.map LinearMap.id (permutationRepresentation (V := V) n σ)
  map_one' := by
    rw [map_one]
    exact TensorProduct.map_id
  map_mul' σ τ := by
    change TensorProduct.map LinearMap.id
        (permutationRepresentation (V := V) n (σ * τ)) =
      (TensorProduct.map LinearMap.id (permutationRepresentation (V := V) n σ)).comp
        (TensorProduct.map LinearMap.id (permutationRepresentation (V := V) n τ))
    rw [map_mul, ← TensorProduct.map_comp]
    rfl

/-- The coefficient tensor formula for a permutation.

For a commutative ring k, k-modules M,V, σ ∈ Sₙ, m ∈ M and a : Fin n → V, ρₙ,M(σ)(m ⊗
tprod(a)) = m ⊗ tprod(a ∘ σ⁻¹). -/
theorem coefficientPermutationRepresentation_tprod (n : ℕ) (σ : Equiv.Perm (Fin n))
    (m : M) (a : Fin n → V) :
    coefficientPermutationRepresentation (M := M) (V := V) n σ
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => a (σ.symm i)) := by
  change TensorProduct.map (LinearMap.id : M →ₗ[k] M)
    (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
    PiTensorProduct.reindex_tprod]

/-- The group-algebra representation on coefficient tensors.

For a commutative ring k and k-modules M,V, this k-algebra homomorphism k[Sₙ] → End_k(M ⊗
V⊗n) sends c[σ] to c · (id_M ⊗ ρₙ(σ)). Thus the coefficient-weighted permutation action
preserves products and units. -/
def coefficientPermutationGroupAlgebraAction (n : ℕ) :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] Module.End k (M ⊗[k] TensorPower k n V) :=
  MonoidAlgebra.lift k (Module.End k (M ⊗[k] TensorPower k n V)) (Equiv.Perm (Fin n))
    (coefficientPermutationRepresentation (M := M) (V := V) n)

/-- The action of a group-algebra monomial.

For a commutative ring k, k-modules M,V, c ∈ k and σ ∈ Sₙ, the action of c[σ] on M ⊗ V⊗n is
c · ρₙ,M(σ), where ρₙ,M fixes M. -/
theorem coefficientPermutationGroupAlgebraAction_single (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (c : k) :
    coefficientPermutationGroupAlgebraAction (M := M) (V := V) n
        (MonoidAlgebra.single σ c) =
      c • coefficientPermutationRepresentation (M := M) (V := V) n σ :=
  MonoidAlgebra.lift_single _ _ _

/-- A finite group-algebra sum acts as its weighted permutation operator.

For a commutative ring k, k-modules M,V and c : Sₙ → k, the action of ∑σ c(σ)[σ] is ∑σ
c(σ)ρₙ,M(σ), namely coefficientPermutationOperator. -/
theorem coefficientPermutationGroupAlgebraAction_sum (n : ℕ)
    (c : Equiv.Perm (Fin n) → k) :
    coefficientPermutationGroupAlgebraAction (M := M) (V := V) n
        (∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.single σ (c σ)) =
      coefficientPermutationOperator (M := M) (V := V) n c := by
  classical
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change coefficientPermutationGroupAlgebraAction (M := M) (V := V) n
      (∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.single σ (c σ))
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
    coefficientPermutationOperator (M := M) (V := V) n c (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [coefficientPermutationOperator_tprod, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [coefficientPermutationGroupAlgebraAction_single]
  simp only [LinearMap.smul_apply, coefficientPermutationRepresentation_tprod,
    TensorProduct.smul_tmul']

variable [Algebra ℚ k]

/-- The rational group-ring action on coefficient tensors.

For a commutative ℚ-algebra k and k-modules M,V, this ring homomorphism ℚ[Sₙ] → End_k(M ⊗
V⊗n) first maps each rational coefficient along ℚ → k, then applies the coefficient
permutation representation. -/
def coefficientRationalPermutationAction (n : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+* Module.End k (M ⊗[k] TensorPower k n V) :=
  (coefficientPermutationGroupAlgebraAction (M := M) (V := V) n).toRingHom.comp
    (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))

/-- Rational scalar compatibility of the coefficient action.

For a commutative ℚ-algebra k, k-modules M,V, c ∈ ℚ and x ∈ ℚ[Sₙ], the action satisfies
ρₙ,M(c x) = algebraMap(c) · ρₙ,M(x). -/
theorem coefficientRationalPermutationAction_smul (n : ℕ) (c : ℚ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n (c • x) =
      (algebraMap ℚ k c) • coefficientRationalPermutationAction (k := k) (M := M) (V := V) n x := by
  let ρ : MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+*
      Module.End k (M ⊗[k] TensorPower k n V) :=
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
  change ρ (c • x) = (algebraMap ℚ k c) • ρ x
  rw [Algebra.smul_def, map_mul]
  have hscalar : ρ (algebraMap ℚ (MonoidAlgebra ℚ (Equiv.Perm (Fin n))) c) =
      (algebraMap ℚ k c) • (1 : Module.End k (M ⊗[k] TensorPower k n V)) := by
    change coefficientPermutationGroupAlgebraAction (M := M) (V := V) n
      ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))
        (MonoidAlgebra.single (1 : Equiv.Perm (Fin n)) c)) = _
    rw [MonoidAlgebra.mapRingHom_single, coefficientPermutationGroupAlgebraAction_single, map_one]
  rw [hscalar, smul_mul_assoc, _root_.one_mul]

/-- The weighted tensor operator of a rational group-ring sum.

For a commutative ℚ-algebra k, k-modules M,V and c : Sₙ → ℚ, the action of ∑σ c(σ)[σ] equals
coefficientPermutationOperator with weights σ ↦ algebraMap(c(σ)). -/
theorem coefficientRationalPermutationAction_sum (n : ℕ)
    (c : Equiv.Perm (Fin n) → ℚ) :
    coefficientRationalPermutationAction (k := k) (M := M) (V := V) n
        (∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.single σ (c σ)) =
      coefficientPermutationOperator (M := M) (V := V) n
        (fun σ => algebraMap ℚ k (c σ)) := by
  classical
  unfold coefficientRationalPermutationAction
  change coefficientPermutationGroupAlgebraAction (M := M) (V := V) n
    ((MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))
      (∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.single σ (c σ))) = _
  rw [map_sum]
  simp only [MonoidAlgebra.mapRingHom_single]
  exact coefficientPermutationGroupAlgebraAction_sum n _

end TensorPower
