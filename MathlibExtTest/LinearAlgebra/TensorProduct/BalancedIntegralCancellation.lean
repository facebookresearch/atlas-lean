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

import MathlibExt.LinearAlgebra.TensorProduct.BalancedIntegralCancellation

/-! Actual noncommutative right-action, integral inverse and independent-world map consumers. -/

noncomputable section

open scoped TensorProduct
open MulOpposite

universe u v w z w' z'

variable (k : Type u) (R : Type v) (M : Type w) (V : Type z)
  [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup V] [Module k V]

example (m : M) (r : R) (v : V) :
    TensorProduct.Balanced.integralCancelEquiv k R M V
        (TensorProduct.Balanced.mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      (op r • m) ⊗ₜ[k] v :=
  TensorProduct.Balanced.integralCancelEquiv_mk_tmul k R M V m r v

example (m : M) (r s : R) (v : V) :
    TensorProduct.Balanced.integralCancelEquiv k R M V
        (TensorProduct.Balanced.mk ℤ R M (R ⊗[k] V) (op r • m) (s ⊗ₜ[k] v)) =
      TensorProduct.Balanced.integralCancelEquiv k R M V
        (TensorProduct.Balanced.mk ℤ R M (R ⊗[k] V) m ((r * s) ⊗ₜ[k] v)) := by
  rw [TensorProduct.Balanced.integralCancelEquiv_mk_tmul,
    TensorProduct.Balanced.integralCancelEquiv_mk_tmul, ← mul_smul, ← op_mul]

example (m : M) (v : V) :
    (TensorProduct.Balanced.integralCancelEquiv k R M V).symm (m ⊗ₜ[k] v) =
      TensorProduct.Balanced.mk ℤ R M (R ⊗[k] V) m ((1 : R) ⊗ₜ[k] v) :=
  TensorProduct.Balanced.integralCancelEquiv_symm_tmul k R M V m v

example (x : M ⊗[k] V) :
    TensorProduct.Balanced.integralCancel k R M V
        (TensorProduct.Balanced.integralInsert k R M V x) = x :=
  TensorProduct.Balanced.integralCancel_insert k R M V x

example (q : TensorProduct.Balanced ℤ R M (R ⊗[k] V)) :
    TensorProduct.Balanced.integralInsert k R M V
        (TensorProduct.Balanced.integralCancel k R M V q) = q :=
  TensorProduct.Balanced.integralInsert_cancel k R M V q

variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Rᵐᵒᵖ M']
  [SMulCommClass k Rᵐᵒᵖ M'] [IsScalarTower k Rᵐᵒᵖ M']
  {V' : Type z'} [AddCommGroup V'] [Module k V']

example (f : M →ₗ[k] M') (g : V →ₗ[k] V')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (m : M) (r : R) (v : V) :
    TensorProduct.Balanced.integralMap k R M V f g hf
        (TensorProduct.Balanced.mk ℤ R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      TensorProduct.Balanced.mk ℤ R M' (R ⊗[k] V') (f m) (r ⊗ₜ[k] g v) :=
  TensorProduct.Balanced.integralMap_mk_tmul k R M V f g hf m r v

example (f : M →ₗ[k] M') (g : V →ₗ[k] V')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (q : TensorProduct.Balanced ℤ R M (R ⊗[k] V)) :
    TensorProduct.Balanced.integralCancelEquiv k R M' V'
        (TensorProduct.Balanced.integralMap k R M V f g hf q) =
      TensorProduct.map f g (TensorProduct.Balanced.integralCancelEquiv k R M V q) :=
  TensorProduct.Balanced.integralCancelEquiv_naturality k R M V f g hf q
