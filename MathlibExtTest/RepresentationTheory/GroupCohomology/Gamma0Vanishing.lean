/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.Gamma0Vanishing

@[expose] public section

open CongruenceSubgroup


/-- Consumer with the original binders (`Type 0`). -/
private theorem exactSource {k : Type} [CommRing k] (M : ℕ) (h6 : IsUnit (6 : k))
    (A : Rep k ↥(Gamma0 M)) : Subsingleton (groupCohomology A 2) :=
  CongruenceSubgroup.subsingleton_H2_gamma0 M h6 A

/-- Boundary: the unit hypothesis matters already for the index `48`:
`48` is not a unit in `ℤ`, so the corestriction argument cannot kill
classes over `ℤ` by this route. -/
example : ¬ IsUnit (48 : ℤ) := by decide
