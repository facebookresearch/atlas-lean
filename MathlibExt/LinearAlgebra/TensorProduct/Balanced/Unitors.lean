/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Algebra.Tower
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced

/-!
# Actual unitors for the noncommutative balanced quotient

The regular factor is contracted by the given module action. The maps use
the existing balanced quotient, its lift/balance, and free-action cancellation.
The acting ring need not be commutative. Ground compatibility refers to the
original module actions; no unitor, comparison or flatness is supplied as data.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe u v w

namespace TensorProduct.Balanced

variable (k : Type u) (R : Type v) [CommRing k] [Ring R] [Algebra k R]

section Left

variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]
  [IsScalarTower k R N]

/-- Contract the original regular left factor through the actual balanced relation. -/
def leftUnitor : Balanced k R R N ≃ₗ[k] N := by
  refine LinearEquiv.ofLinearMap
    (lift (Algebra.lsmul k k N : R →ₐ[k] Module.End k N).toLinearMap
      (by
        intro s r n
        change (r * s) • n = r • (s • n)
        exact mul_smul r s n))
    (mk k R R N 1) ?_ ?_
  · apply LinearMap.ext
    intro n
    change (1 : R) • n = n
    exact one_smul R n
  · apply hom_ext
    intro r n
    change mk k R R N 1 (r • n) = mk k R R N r n
    calc
      _ = mk k R R N (op r • (1 : R)) n :=
        (balance k R R N r 1 n).symm
      _ = _ := by
        apply congrArg (fun a : R => mk k R R N a n)
        change (1 : R) * r = r
        exact one_mul r

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem leftUnitor_mk (r : R) (n : N) :
    leftUnitor k R N (mk k R R N r n) = r • n :=
  rfl

@[simp]
theorem leftUnitor_symm (n : N) :
    (leftUnitor k R N).symm n = mk k R R N 1 n :=
  rfl

end Left

section Right

variable (Q : Type w) [AddCommGroup Q] [Module k Q] [Module Rᵐᵒᵖ Q]
  [IsScalarTower k Rᵐᵒᵖ Q]

/-- Contract the regular right factor using the existing free-action cancellation. -/
def rightUnitor : Balanced k R Q R ≃ₗ[k] Q := by
  refine (congr (LinearEquiv.refl k Q) (TensorProduct.rid k R).symm
    (fun _ _ => rfl) ?_).trans
      ((cancelEquiv k R Q k).trans (TensorProduct.rid k Q))
  intro r s
  change (r * s) ⊗ₜ[k] (1 : k) = r • (s ⊗ₜ[k] (1 : k))
  simp only [TensorProduct.smul_tmul', smul_eq_mul]

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem rightUnitor_mk (q : Q) (r : R) :
    rightUnitor k R Q (mk k R Q R q r) = op r • q := by
  let h : ∀ r s : R, (TensorProduct.rid k R).symm (r • s) =
      r • (TensorProduct.rid k R).symm s := by
    intro r s
    change (r * s) ⊗ₜ[k] (1 : k) = r • (s ⊗ₜ[k] (1 : k))
    simp only [TensorProduct.smul_tmul', smul_eq_mul]
  change (TensorProduct.rid k Q)
      ((cancelEquiv k R Q k)
        ((congr (LinearEquiv.refl k Q) (TensorProduct.rid k R).symm
          (fun _ _ => rfl) h) (mk k R Q R q r))) = op r • q
  rw [congr_mk (LinearEquiv.refl k Q) (TensorProduct.rid k R).symm
    (fun _ _ => rfl) h q r]
  simp only [LinearEquiv.refl_apply, TensorProduct.rid_symm_apply]
  rw [cancelEquiv_mk_tmul, TensorProduct.rid_tmul, one_smul]

@[simp]
theorem rightUnitor_symm (q : Q) :
    (rightUnitor k R Q).symm q = mk k R Q R q 1 := by
  apply (rightUnitor k R Q).injective
  rw [LinearEquiv.apply_symm_apply, rightUnitor_mk, op_one, one_smul]

end Right

end TensorProduct.Balanced
