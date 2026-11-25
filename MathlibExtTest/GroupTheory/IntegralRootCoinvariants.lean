/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GroupTheory.IntegralRootCoinvariants
import Mathlib.Data.ZMod.Basic

/-! The adjoint A1 coroot relation is two in the coweight lattice Z.
The actual integral quotient retains its nonzero order-two class. -/

open MathlibExt.GroupTheory.IntegralRootCoinvariants

private def coroots : Submodule ℤ ℤ := Submodule.span ℤ {(2 : ℤ)}
private def action : Representation ℤ Unit ℤ := Representation.trivial _ _ _

private def reduction : ℤ →ₗ[ℤ] ZMod 2 where
  toFun a := a
  map_add' a b := Int.cast_add a b
  map_smul' a b := by simp [zsmul_eq_mul]

private theorem reduction_coroots : coroots ≤ LinearMap.ker reduction := by
  apply Submodule.span_le.mpr
  rintro x (rfl : x = 2)
  change (2 : ZMod 2) = 0
  decide

private theorem reduction_inertia : ∀ g x, reduction (action g x) = reduction x := by
  intro g x
  rfl

private theorem reduction_one : reduction (1 : ℤ) = (1 : ZMod 2) := by
  change ((1 : ℤ) : ZMod 2) = 1
  exact Int.cast_one

example : quotientMap coroots action (2 : ℤ) = 0 :=
  quotientMap_coroot _ _ (Submodule.subset_span (Set.mem_singleton _))

example : quotientMap coroots action (1 : ℤ) ≠ 0 := by
  intro h
  have h' := congrArg (descend coroots action reduction reduction_coroots reduction_inertia) h
  have h'' : (1 : ZMod 2) = 0 := by
    simpa only [descend_quotientMap, map_zero, reduction_one] using h'
  exact one_ne_zero h''
