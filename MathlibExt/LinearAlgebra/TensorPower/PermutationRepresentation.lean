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
# The actual group-algebra representation on coefficient tensor words

A permutation sends the old entry at j to sigma(j); the new word uses
sigma inverse. The coefficient is fixed. The monoid representation and its
native group-algebra lift prove that the finite operator is multiplicative
and unital. Rational coefficients are mapped through the original ground
algebra. No projector laws or representation certificate is an input.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- The actual inverse-word place-permutation monoid representation. -/
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

/-- The native tail permutation representation retains its actual inverse-place tensor-word value. -/
theorem permutationRepresentation_tprod (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : Fin n → V) :
    permutationRepresentation (k := k) (V := V) n σ (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun i => a (σ.symm i)) := by
  change PiTensorProduct.reindex k (fun _ : Fin n => V) σ (PiTensorProduct.tprod k a) = _
  simp only [PiTensorProduct.reindex_tprod]

/-- The coefficient-fixed actual permutation representation. -/
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

/-- The coefficient remains fixed while the tail uses the original inverse-permutation word. -/
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

/-- Native monoid-algebra lifting gives the actual coefficient-word algebra representation. -/
def coefficientPermutationGroupAlgebraAction (n : ℕ) :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] Module.End k (M ⊗[k] TensorPower k n V) :=
  MonoidAlgebra.lift k (Module.End k (M ⊗[k] TensorPower k n V)) (Equiv.Perm (Fin n))
    (coefficientPermutationRepresentation (M := M) (V := V) n)

/-- A group-algebra generator acts by its scalar and original coefficient-fixed permutation. -/
theorem coefficientPermutationGroupAlgebraAction_single (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (c : k) :
    coefficientPermutationGroupAlgebraAction (M := M) (V := V) n
        (MonoidAlgebra.single σ c) =
      c • coefficientPermutationRepresentation (M := M) (V := V) n σ :=
  MonoidAlgebra.lift_single _ _ _

/-- The native group-algebra representation is exactly the actual finite permutation operator. -/
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

/-- The original rational group-ring coefficients act through the actual ground algebra map. -/
def coefficientRationalPermutationAction (n : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+* Module.End k (M ⊗[k] TensorPower k n V) :=
  (coefficientPermutationGroupAlgebraAction (M := M) (V := V) n).toRingHom.comp
    (MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ k))

/-- Rational scalar multiplication acts through the actual ground-algebra scalar image. -/
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

/-- The actual rational finite sum is the coefficient operator with the original scalar images. -/
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
