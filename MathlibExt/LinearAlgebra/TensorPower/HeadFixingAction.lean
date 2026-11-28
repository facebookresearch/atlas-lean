/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicHeadFixing
public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import MathlibExt.LinearAlgebra.TensorPower.PermutationRepresentation

/-!
# Place permutations that fix the first tensor factor

For a commutative ring k and a k-module V, the embedding h : Sₙ → Sₙ₊₁ fixes position zero and
permutes the following n positions. Under consEquiv : V ⊗ V⊗n ≃ V⊗(n+1), the inverse-word action
of h(σ) is id_V ⊗ ρₙ(σ).

For tensor powers and their permutation functoriality, see N. Bourbaki, Algebra I, Chapter III.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]

/-- The first-factor coordinate formula for a head-fixed permutation.

For a commutative ring k, a k-module V and σ ∈ Sₙ, ρₙ₊₁(h(σ)) ∘ consEquiv = consEquiv ∘
(id_V ⊗ ρₙ(σ)). Here h fixes position zero and ρ uses a ∘ σ⁻¹ on tensor words. -/
theorem permutationRepresentation_headFixing_cons (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationRepresentation (V := V) (n + 1) (Equiv.Perm.headFixingHom n σ)).comp
        (consEquiv k V n).toLinearMap =
      (consEquiv k V n).toLinearMap.comp
        (TensorProduct.map LinearMap.id (permutationRepresentation (V := V) n σ)) := by
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  have hinv : (Equiv.Perm.headFixingHom n σ).symm = Equiv.Perm.headFixingHom n σ.symm :=
    (map_inv (Equiv.Perm.headFixingHom n) σ).symm
  change PiTensorProduct.reindex k (fun _ : Fin (n + 1) => V) (Equiv.Perm.headFixingHom n σ)
      (consEquiv k V n (v ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    consEquiv k V n
      (TensorProduct.map LinearMap.id (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap
        (v ⊗ₜ[k] PiTensorProduct.tprod k a))
  simp only [consEquiv_tmul,
    LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [hinv]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  cases i using Fin.cases with
  | zero =>
    change @Fin.cons n (fun _ => V) v a (Equiv.Perm.headFixingPermutation n σ.symm 0) = v
    rw [Equiv.Perm.headFixingPermutation_zero, Fin.cons_zero]
  | succ i =>
    change @Fin.cons n (fun _ => V) v a (Equiv.Perm.headFixingPermutation n σ.symm i.succ) = a
      (σ.symm i)
    rw [Equiv.Perm.headFixingPermutation_succ, Fin.cons_succ]

end TensorPower
