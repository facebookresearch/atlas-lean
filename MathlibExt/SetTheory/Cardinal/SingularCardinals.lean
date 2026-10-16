/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Regular
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 358
-- Proposed path (advisory metadata only, not a review instruction).

open Set Cardinal Ordinal

-- Logic 358: Singular Cardinal Hypothesis
def SingularCardinalsHypothesis.{u} : Prop :=
  ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → κ.ord.cof < κ →
    (2 : Cardinal.{u}) ^ κ.ord.cof < κ → κ ^ κ.ord.cof = Order.succ κ

theorem succ_le_power_cof.{u} {κ : Cardinal.{u}} (h : ℵ₀ ≤ κ) :
    Order.succ κ ≤ κ ^ κ.ord.cof :=
  Order.succ_le_of_lt (Cardinal.lt_power_cof_ord h)

theorem two_power_cof_le_power_cof.{u} {κ : Cardinal.{u}} (h : 2 ≤ κ) :
    (2 : Cardinal.{u}) ^ κ.ord.cof ≤ κ ^ κ.ord.cof :=
  Cardinal.power_le_power_right h

theorem not_cof_lt_aleph0.{u} : ¬ (ℵ₀ : Cardinal.{u}).ord.cof < ℵ₀ :=
  not_lt.mpr Cardinal.isRegular_aleph0.2

theorem not_cof_lt_of_isRegular.{u} {κ : Cardinal.{u}} (h : κ.IsRegular) : ¬ κ.ord.cof < κ :=
  not_lt.mpr h.2

end
