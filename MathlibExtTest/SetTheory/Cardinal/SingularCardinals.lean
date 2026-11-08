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

public import MathlibExt.SetTheory.Cardinal.SingularCardinals
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

open Set Cardinal Ordinal

namespace MathlibExtTest.SetTheory.Cardinal.SingularCardinals

open MetaMathlibExt

-- Logic 358: Singular Cardinal Hypothesis

/-- König: `κ⁺ ≤ κ ^ cf κ` for infinite `κ`.  So SCH's conclusion is the *least* value the
exponential can take, and only the `≤` direction of `κ ^ cf κ = κ⁺` has content. -/

theorem succ_le_power_cof.{u} {κ : Cardinal.{u}} (h : ℵ₀ ≤ κ) :
    Order.succ κ ≤ κ ^ κ.ord.cof :=
  Order.succ_le_of_lt (Cardinal.lt_power_cof_ord h)

/-- The `2 ^ cf κ < κ` clause is load-bearing: `2 ^ cf κ` is a lower bound for `κ ^ cf κ`,
so a continuum function large enough to push `2 ^ cf κ` past `κ⁺` refutes the conclusion. -/

theorem two_power_cof_le_power_cof.{u} {κ : Cardinal.{u}} (h : 2 ≤ κ) :
    (2 : Cardinal.{u}) ^ κ.ord.cof ≤ κ ^ κ.ord.cof :=
  Cardinal.power_le_power_right h

/-- `ℵ₀` is regular, so the singularity clause excludes it — SCH says nothing at `ℵ₀`. -/

theorem not_cof_lt_aleph0.{u} : ¬ (ℵ₀ : Cardinal.{u}).ord.cof < ℵ₀ :=
  not_lt.mpr Cardinal.isRegular_aleph0.2

/-- Regular cardinals are out of scope generally, not just `ℵ₀`. -/

theorem not_cof_lt_of_isRegular.{u} {κ : Cardinal.{u}} (h : κ.IsRegular) : ¬ κ.ord.cof < κ :=
  not_lt.mpr h.2

end MathlibExtTest.SetTheory.Cardinal.SingularCardinals

end
