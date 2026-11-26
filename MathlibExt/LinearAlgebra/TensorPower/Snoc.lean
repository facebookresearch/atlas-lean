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

/-!
# Appending and splitting the last tensor factor

Let k be a commutative semiring and M an additive commutative k-module. The linear equivalence
M⊗n ⊗ M ≃ M⊗(n+1) appends the last factor. On a pure word it sends tprod(a) ⊗ m to
tprod(Fin.snoc a m). Its inverse separates the initial n factors and the factor at Fin.last n.

For tensor associativity and its universal property, see N. Bourbaki, Algebra I, Chapter III.
-/
@[expose] public section
noncomputable section

open scoped TensorProduct

namespace TensorPower
universe u v

variable (k : Type u) [CommSemiring k] (M : Type v) [AddCommMonoid M] [Module k M]

/-- Appending a last tensor factor.

For a commutative semiring k and an additive commutative k-module M, snocEquiv is the
k-linear equivalence M⊗n ⊗ M ≃ M⊗(n+1) that retains the order of the initial factors and
appends the last one. -/
def snocEquiv (n : ℕ) :
    TensorPower k n M ⊗[k] M ≃ₗ[k] TensorPower k (n + 1) M :=
  (TensorProduct.comm k (TensorPower k n M) M).trans
    ((consEquiv k M n).trans
      (PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (finRotate (n + 1)).symm))

/-- The pure-tensor formula for appending a factor.

For a commutative semiring k, an additive commutative k-module M, a : Fin n → M and m ∈ M,
snocEquiv(tprod(a) ⊗ m) = tprod(Fin.snoc a m). -/
theorem snocEquiv_tmul (n : ℕ) (a : Fin n → M) (m : M) :
    snocEquiv k M n (PiTensorProduct.tprod k a ⊗ₜ[k] m) =
      PiTensorProduct.tprod k (Fin.snoc a m) := by
  simp only [snocEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    consEquiv_tmul, PiTensorProduct.reindex_tprod, Equiv.symm_symm]
  exact congrArg (PiTensorProduct.tprod k) (Fin.snoc_eq_cons_rotate a m).symm

/-- Separating the last factor of a tensor word.

For a commutative semiring k, an additive commutative k-module M and a : Fin(n+1) → M,
snocEquiv⁻¹(tprod(a)) = tprod(Fin.init a) ⊗ a(Fin.last n). -/
theorem snocEquiv_symm_tprod (n : ℕ) (a : Fin (n + 1) → M) :
    (snocEquiv k M n).symm (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (Fin.init a) ⊗ₜ[k] a (Fin.last n) := by
  apply (snocEquiv k M n).injective
  rw [LinearEquiv.apply_symm_apply, snocEquiv_tmul, Fin.snoc_init_self]

end TensorPower
