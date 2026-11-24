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
# The original neutral tensor action of the head-fixing permutation

The actual head-fixing monoid embedding fixes the original first factor
and has its original tail representation through the native cons tensor
coordinates. This sign-independent original word law holds over every
commutative ground ring and does not import the rational Eulerian engine.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v

namespace TensorPower

variable {k : Type u} [CommRing k]
  {V : Type v} [AddCommGroup V] [Module k V]

/-- The actual head-fixing place representation retains the original head and original tail coordinates. -/
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
    change @Fin.cons n (fun _ => V) v a (Equiv.Perm.headFixingPermutation n σ.symm i.succ) = a (σ.symm i)
    rw [Equiv.Perm.headFixingPermutation_succ, Fin.cons_succ]

end TensorPower
