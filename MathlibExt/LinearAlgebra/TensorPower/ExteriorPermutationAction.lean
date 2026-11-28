/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.LinearAlgebra.TensorPower.Antisymmetrization
public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation

/-!
# Permutation signs on exterior tensor images

For a commutative ring k and k-modules V,M, let Aₙ : ⋀ⁿV → V⊗n be antisymmetrization. The place-
permutation action ρₙ(σ) sends a tensor word a to a ∘ σ⁻¹. It satisfies ρₙ(σ)Aₙ = sign(σ)Aₙ, and
the same formula holds after tensoring with id_M. All signs are mapped from ℤ to k.

This is the alternating representation in multilinear algebra; see N. Bourbaki, Algebra I,
Chapter III.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

variable (k : Type u) [CommRing k]
  (V : Type v) [AddCommGroup V] [Module k V]

/-- The sign action on the exterior image in a tensor power.

For a commutative ring k, a k-module V and σ ∈ Sₙ, ρₙ(σ) ∘ Aₙ = sign(σ) · Aₙ as maps ⋀ⁿV →
V⊗n. The representation uses the inverse-word convention and the sign acts through ℤ → k. -/
theorem permutationRepresentation_comp_exteriorAntisymmetrization
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation (k := k) (V := V) n σ).comp (exteriorAntisymmetrization k V n) =
      (((σ.sign : ℤ) : k)) • exteriorAntisymmetrization k V n := by
  classical
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change PiTensorProduct.reindex k (fun _ : Fin n => V) σ
      (exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a)) =
    (((σ.sign : ℤ) : k)) • exteriorAntisymmetrization k V n (exteriorPower.ιMulti k n a)
  simp only [exteriorAntisymmetrization_ιMulti, Units.smul_def, map_sum, map_zsmul,
    PiTensorProduct.reindex_tprod]
  change (∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
      PiTensorProduct.tprod k ((a ∘ π) ∘ σ.symm)) =
    (((σ.sign : ℤ) : k)) • ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) • PiTensorProduct.tprod k (a ∘ π)
  let e := Equiv.mulRight σ
  rw [← Equiv.sum_comp e (fun π : Equiv.Perm (Fin n) => (π.sign : ℤ) •
    PiTensorProduct.tprod k ((a ∘ π) ∘ σ.symm)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hword : (a ∘ (π * σ)) ∘ σ.symm = a ∘ π := by
    funext i
    simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  change ((π * σ).sign : ℤ) • PiTensorProduct.tprod k ((a ∘ (π * σ)) ∘ σ.symm) = _
  rw [hword, Equiv.Perm.sign_mul]
  simp only [Units.val_mul, ← Int.cast_smul_eq_zsmul k, Int.cast_mul, smul_smul, mul_comm]

variable (M : Type w) [AddCommGroup M] [Module k M]

/-- The sign action with a fixed coefficient module.

For a commutative ring k, k-modules M,V and σ ∈ Sₙ, the action on M ⊗ V⊗n fixes M and
satisfies ρₙ,M(σ) ∘ (id_M ⊗ Aₙ) = sign(σ) · (id_M ⊗ Aₙ). -/
theorem coefficientPermutationRepresentation_comp_exteriorAntisymmetrization
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (coefficientPermutationRepresentation (k := k) (M := M) (V := V) n σ).comp
      (TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n)) =
        (((σ.sign : ℤ) : k)) • TensorProduct.map LinearMap.id (exteriorAntisymmetrization k V n) :=
          by
  change (TensorProduct.map (LinearMap.id : M →ₗ[k] M)
    (permutationRepresentation (k := k) (V := V) n σ)).comp
      (TensorProduct.map (LinearMap.id : M →ₗ[k] M) (exteriorAntisymmetrization k V n)) = _
  rw [← TensorProduct.map_comp,
    LinearMap.id_comp, permutationRepresentation_comp_exteriorAntisymmetrization,
    TensorProduct.map_smul_right]

end TensorPower
