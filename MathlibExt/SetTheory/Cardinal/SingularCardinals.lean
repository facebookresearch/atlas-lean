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
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 358

/-!
# Singular Cardinal Hypothesis

## References

* Jech (for `SingularCardinalsHypothesis`)
-/

open Set Cardinal Ordinal

namespace MetaMathlibExt

-- Logic 358: Singular Cardinal Hypothesis

/-- For all singular cardinal $\kappa$, if $2^{cof(\kappa)}<\kappa, then $\kappa^{cof(\kappa)} =
\kappa^+$.
-/
def SingularCardinalsHypothesis.{u} : Prop :=
  ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → κ.ord.cof < κ →
    (2 : Cardinal.{u}) ^ κ.ord.cof < κ → κ ^ κ.ord.cof = Order.succ κ

end MetaMathlibExt

end
