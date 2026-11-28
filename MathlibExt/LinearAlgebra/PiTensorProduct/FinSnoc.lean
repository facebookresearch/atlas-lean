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

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Last-factor splitting of a finite dependent tensor family

Over a commutative semiring, the tensor family indexed by `Fin (n + 1)` splits into the
ordered prefix indexed by `Fin n` and its last factor. Independent coefficient carrier
universes and arbitrary semimodules are retained.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
universe r v w

namespace PiTensorProduct

variable (R : Type r) [CommSemiring R]

/-- For a commutative semiring R and a dependent family of R-modules
V_j indexed by Fin(n + 1), each with additive commutative monoid structure,
this R-linear equivalence splits off the last factor:
⨂_(j:Fin(n+1)) V_j ≅ (⨂_(j:Fin n) V_(j.castSucc)) ⊗[R] V_(Fin.last n).
The prefix keeps its original order. -/
def finSnocEquiv (n : ℕ) (V : Fin (n + 1) → Type v)
    [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)] :
    (⨂[R] j : Fin (n + 1), V j) ≃ₗ[R]
      (⨂[R] j : Fin n, V j.castSucc) ⊗[R] V (Fin.last n) :=
  (reindex R V (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm).trans
    ((tmulEquivDep R
        (fun j : Fin n ⊕ Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) j))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R (⨂[R] j : Fin n, V j.castSucc))
        (subsingletonEquiv (R := R)
          (s := fun j : Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j))) 0)))

/-- For a commutative semiring R, R-modules V_j indexed by Fin(n + 1),
and a family x_j ∈ V_j, the last-factor splitting sends
tprod(x) to tprod(j ↦ x_(j.castSucc)) ⊗ x_(Fin.last n).
The first tensor factor contains the ordered prefix. -/
@[simp]
theorem finSnocEquiv_tprod (n : ℕ) (V : Fin (n + 1) → Type v)
    [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)] (x : ∀ j, V j) :
    finSnocEquiv R n V (tprod R x) =
      tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R] x (Fin.last n) := by
  rw [finSnocEquiv, LinearEquiv.trans_apply, reindex_tprod]
  change TensorProduct.congr (LinearEquiv.refl R (⨂[R] j : Fin n, V j.castSucc))
      (subsingletonEquiv (R := R)
        (s := fun j : Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j))) 0)
      ((tmulEquivDep R
        (fun j : Fin n ⊕ Fin 1 => V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) j))).symm
        (tprod R (fun j => x ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) j)))) = _
  rw [tmulEquivDep_symm_apply]
  change TensorProduct.congr (LinearEquiv.refl R (⨂[R] j : Fin n, V j.castSucc))
      (subsingletonEquiv (R := R)
        (s := fun j : Fin 1 =>
          V ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j))) 0)
      (tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R]
        tprod R (fun j : Fin 1 =>
          x ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr j)))) =
    tprod R (fun j : Fin n => x j.castSucc) ⊗ₜ[R] x (Fin.last n)
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    subsingletonEquiv_apply_tprod]
  rfl

end PiTensorProduct
