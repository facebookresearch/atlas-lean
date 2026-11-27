/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement

/-! # Tests for finite-free complements in `FGProjectiveCat` -/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace FGProjectiveCatFiniteFreeComplementTests

variable {R : Type u} [Ring R]

example (P Q : FGProjectiveCat.{u} R) :
    ((P ⊞ Q : FGProjectiveCat.{u} R) : Type u) ≃ₗ[R] (P × Q) :=
  FGProjectiveCat.biprodCarrierLinearEquiv P Q

example {P Q : FGProjectiveCat.{u} R} (e : P ≃ₗ[R] Q) : P ≅ Q :=
  FGProjectiveCat.isoOfLinearEquiv e

example (P : FGProjectiveCat.{u} R) :
    Aut P ≃* (P ≃ₗ[R] P) :=
  FGProjectiveCat.autCarrierLinearEquiv P

example (P : FGProjectiveCat.{u} R) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.{u} R),
      Nonempty (P ⊞ Q ≅ FGProjectiveCat.of (R := R) (Fin n → R)) :=
  FGProjectiveCat.exists_biprod_iso_fin_free P

example {A : Type u} [CommRing A] (n : ℕ) :
    Aut (FGProjectiveCat.of (R := A) (Fin n → A)) ≃*
      Matrix.GeneralLinearGroup (Fin n) A :=
  FGProjectiveCat.freeAutMulEquivGL A n

end FGProjectiveCatFiniteFreeComplementTests
