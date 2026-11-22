/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import MathlibExt.SetTheory.Cardinal.Cofinality.Stationary
public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Inaccessible

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 28, Logic 30

/-!
# Mahlo cardinal; Weakly Mahlo cardinal

## References

* Jech (for `IsMahlo`, `IsWeaklyMahlo`)
-/

namespace MetaMathlibExt

-- Logic 28: Mahlo cardinal

/-- A cardinal κ is *Mahlo* if κ is inaccessible and the set {  λ < κ : λ  is inaccessible  } of
inaccessibles below κ is stationary in κ.
-/
def IsMahlo.{u} (κ : Cardinal.{u}) : Prop :=
  Cardinal.IsInaccessible κ ∧ IsStationary (inaccessibleBelow κ)

-- Logic 30: Weakly Mahlo cardinal

/-- A cardinal κ is *weakly Mahlo* if κ is weakly inaccessible and {  λ < κ : λ  is a regular
cardinal  } is stationary in κ.
-/
def IsWeaklyMahlo.{u} (κ : Cardinal.{u}) : Prop :=
  IsWeaklyInaccessible κ ∧
  IsStationary {α : Set.Iio κ.ord | (α.val.card).IsRegular ∧ α.val.card.ord = α.val}

end MetaMathlibExt

end
