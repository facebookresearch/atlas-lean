/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.TensorPower.Snoc
public import MathlibExt.Algebra.Module.AlgHomAction
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The native enveloping action on the two outer tensor-power factors

The original A tensor TensorPower(n+1,A) carrier is identified with the
native induced left (A tensor A-opposite)-module, retaining the middle word.
Only the existing cons, rotation, associator, tensor swap and op coordinate
are used. No bar complex, resolution or comparison map is reconstructed.
-/
@[expose] public section
noncomputable section

open scoped TensorProduct
open MulOpposite

namespace TensorPower
universe u v w

variable (k : Type u) [CommSemiring k]

section Coordinates
variable (A : Type v) [AddCommMonoid A] [Module k A]

/-- Reassociate and move the two original outer module factors into their opposite-marked coordinate. -/
def outerTensorCoordinate (V : Type w) [AddCommMonoid V] [Module k V] :
    A ⊗[k] (V ⊗[k] A) ≃ₗ[k] (A ⊗[k] Aᵐᵒᵖ) ⊗[k] V :=
  (TensorProduct.assoc k A V A).symm.trans
    ((TensorProduct.congr (TensorProduct.comm k A V) (MulOpposite.opLinearEquiv k (M := A))).trans
      ((TensorProduct.assoc k V A Aᵐᵒᵖ).trans
        (TensorProduct.comm k V (A ⊗[k] Aᵐᵒᵖ))))

/-- This coordinate retains the original middle vector and each outer vector. -/
theorem outerTensorCoordinate_tmul (V : Type w) [AddCommMonoid V] [Module k V]
    (a b : A) (x : V) :
    outerTensorCoordinate k A V (a ⊗ₜ[k] (x ⊗ₜ[k] b)) =
      (a ⊗ₜ[k] op b) ⊗ₜ[k] x := by
  simp only [outerTensorCoordinate, LinearEquiv.trans_apply, TensorProduct.assoc_symm_tmul,
    TensorProduct.congr_tmul, TensorProduct.comm_tmul, TensorProduct.assoc_tmul,
    MulOpposite.coe_opLinearEquiv]

/-- The literal first/last factors become the enveloping coordinate, with the middle word unchanged. -/
def outerCoordinate (n : ℕ) :
    A ⊗[k] TensorPower k (n + 1) A ≃ₗ[k]
      (A ⊗[k] Aᵐᵒᵖ) ⊗[k] TensorPower k n A :=
  (TensorProduct.congr (LinearEquiv.refl k A) (snocEquiv k A n).symm).trans
    (outerTensorCoordinate k A (TensorPower k n A))

/-- These are the actual first, unchanged middle, and last coordinates of the input word. -/
theorem outerCoordinate_tprod (n : ℕ) (a₀ : A) (a : Fin (n + 1) → A) :
    outerCoordinate k A n (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (a₀ ⊗ₜ[k] op (a (Fin.last n))) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.init a) := by
  simp only [outerCoordinate, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    snocEquiv_symm_tprod, LinearEquiv.refl_apply, outerTensorCoordinate_tmul]

end Coordinates

variable (A : Type v) [Semiring A] [Algebra k A]

/-- Conjugate the native left tensor-module representation through the earned literal-word coordinate. -/
def outerRepresentation (n : ℕ) :
    (A ⊗[k] Aᵐᵒᵖ) →ₐ[k] Module.End k (A ⊗[k] TensorPower k (n + 1) A) :=
  ((outerCoordinate k A n).symm.conjAlgEquiv k).toAlgHom.comp
    (Algebra.lsmul (A := A ⊗[k] Aᵐᵒᵖ) k k
      ((A ⊗[k] Aᵐᵒᵖ) ⊗[k] TensorPower k n A))

/-- The representation acts by actual native left multiplication in the earned coordinate. -/
theorem outerRepresentation_apply (n : ℕ) (z : A ⊗[k] Aᵐᵒᵖ)
    (x : A ⊗[k] TensorPower k (n + 1) A) :
    outerRepresentation k A n z x =
      (outerCoordinate k A n).symm (z • outerCoordinate k A n x) := rfl

/-- The existing native pullback module is the enveloping module on the original word carrier. -/
@[instance_reducible]
def outerModule (n : ℕ) : Module (A ⊗[k] Aᵐᵒᵖ) (A ⊗[k] TensorPower k (n + 1) A) :=
  Module.compHom _ (outerRepresentation k A n).toRingHom

/-- The earned representation preserves the original ground scalar module. -/
theorem outerScalarTower (n : ℕ) :
    letI := outerModule k A n
    IsScalarTower k (A ⊗[k] Aᵐᵒᵖ) (A ⊗[k] TensorPower k (n + 1) A) :=
  AlgHom.moduleEnd_compHom_isScalarTower (outerRepresentation k A n)

/-- An enveloping pure tensor multiplies only the literal outer first/last factors. -/
theorem outerModule_tprod (n : ℕ) (l r a₀ : A) (a : Fin (n + 1) → A) :
    letI := outerModule k A n
    (l ⊗ₜ[k] op r) • (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (l * a₀) ⊗ₜ[k]
        PiTensorProduct.tprod k (Fin.snoc (Fin.init a) (a (Fin.last n) * r)) := by
  let := outerModule k A n
  apply (outerCoordinate k A n).injective
  change outerCoordinate k A n
    (outerRepresentation k A n (l ⊗ₜ[k] op r) (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [outerRepresentation_apply, LinearEquiv.apply_symm_apply]
  rw [outerCoordinate_tprod, outerCoordinate_tprod]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    MulOpposite.op_mul, Fin.snoc_last, Fin.init_snoc]

end TensorPower
