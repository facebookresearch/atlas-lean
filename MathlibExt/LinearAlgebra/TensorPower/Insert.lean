/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Inserting a fixed tensor factor

Let k be a commutative semiring and B a k-module with an additive commutative monoid structure.
For i ∈ Fin(n+1) and c ∈ B, insertion defines a k-linear map Iᵢ(c) : B⊗n → B⊗(n+1). It sends
tprod(a) to tprod(Fin.insertNth i c a), so the existing factors retain their order.

The construction uses the multilinear universal property of tensor products; see N. Bourbaki,
Algebra I, Chapter III.
-/

@[expose] public section

namespace TensorPower

universe u v

variable (k : Type u) [CommSemiring k]
  {B : Type v} [AddCommMonoid B] [Module k B]

/-- Insertion of a fixed vector into a tensor power.

For a commutative semiring k, an additive commutative k-module B, i ∈ Fin(n+1) and c ∈ B,
this k-linear map B⊗n → B⊗(n+1) inserts c at position i and shifts later factors one
position to the right. -/
noncomputable def insert {n : ℕ} (i : Fin (n + 1)) (c : B) :
    TensorPower k n B →ₗ[k] TensorPower k (n + 1) B :=
  PiTensorProduct.lift
    (MultilinearMap.mk'
      (fun a : Fin n → B =>
        PiTensorProduct.tprod k (Fin.insertNth (α := fun _ : Fin (n + 1) => B) i c a))
      (by
        intro a j x y
        simp only [Fin.insertNth_update]
        exact (show MultilinearMap (RingHom.id k) (fun _ : Fin (n + 1) => B)
          (TensorPower k (n + 1) B) from PiTensorProduct.tprod k).map_update_add
            (Fin.insertNth (α := fun _ : Fin (n + 1) => B) i c a) (i.succAbove j) x y)
      (by
        intro a j r x
        simp only [Fin.insertNth_update]
        exact (show MultilinearMap (RingHom.id k) (fun _ : Fin (n + 1) => B)
          (TensorPower k (n + 1) B) from PiTensorProduct.tprod k).map_update_smul
            (Fin.insertNth (α := fun _ : Fin (n + 1) => B) i c a) (i.succAbove j) r x))

/-- The pure-tensor formula for insertion.

For a commutative semiring k, an additive commutative k-module B, i ∈ Fin(n+1), c ∈ B and a
: Fin n → B, insert(k,i,c)(tprod(a)) = tprod(Fin.insertNth i c a). -/
@[simp]
theorem insert_tprod {n : ℕ} (i : Fin (n + 1)) (c : B) (a : Fin n → B) :
    insert k i c (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (Fin.insertNth i c a) := by
  rw [insert, PiTensorProduct.lift.tprod]
  rfl

end TensorPower
