/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Insertion of one fixed tensor factor

This is the native multilinear universal-property construction, with no new
tensor carrier. The construction was used privately in the source-owned
matrix Morita operators; this neutral owner permits the actual conjugation
and general unit-frame consumers to reuse it. Only semiring/module structure
is needed.
-/

@[expose] public section

namespace TensorPower

universe u v

variable (k : Type u) [CommSemiring k]
  {B : Type v} [AddCommMonoid B] [Module k B]

/-- Insert one fixed factor into the actual tensor power. -/
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

@[simp]
theorem insert_tprod {n : ℕ} (i : Fin (n + 1)) (c : B) (a : Fin n → B) :
    insert k i c (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (Fin.insertNth i c a) := by
  rw [insert, PiTensorProduct.lift.tprod]
  rfl

end TensorPower
