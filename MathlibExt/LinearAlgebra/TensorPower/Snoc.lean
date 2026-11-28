/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # The last coordinate of the existing tensor power -/
@[expose] public section
noncomputable section

open scoped TensorProduct

namespace TensorPower
universe u v

variable (k : Type u) [CommSemiring k] (M : Type v) [AddCommMonoid M] [Module k M]

/-- Place an actual last vector after the original tensor-power word. -/
def snocEquiv (n : ℕ) :
    TensorPower k n M ⊗[k] M ≃ₗ[k] TensorPower k (n + 1) M :=
  (TensorProduct.comm k (TensorPower k n M) M).trans
    ((consEquiv k M n).trans
      (PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (finRotate (n + 1)).symm))

/-- Cons followed by the native rotation preserves the original order before the last vector. -/
theorem snocEquiv_tmul (n : ℕ) (a : Fin n → M) (m : M) :
    snocEquiv k M n (PiTensorProduct.tprod k a ⊗ₜ[k] m) =
      PiTensorProduct.tprod k (Fin.snoc a m) := by
  simp only [snocEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    consEquiv_tmul, PiTensorProduct.reindex_tprod, Equiv.symm_symm]
  exact congrArg (PiTensorProduct.tprod k) (Fin.snoc_eq_cons_rotate a m).symm

/-- Splitting a pure word recovers its unchanged initial word and its actual last coordinate. -/
theorem snocEquiv_symm_tprod (n : ℕ) (a : Fin (n + 1) → M) :
    (snocEquiv k M n).symm (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (Fin.init a) ⊗ₜ[k] a (Fin.last n) := by
  apply (snocEquiv k M n).injective
  rw [LinearEquiv.apply_symm_apply, snocEquiv_tmul, Fin.snoc_init_self]

end TensorPower
