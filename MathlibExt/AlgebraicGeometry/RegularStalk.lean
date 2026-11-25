/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff.lean`
and
`P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.IsOpenImmersion

/-- Regularity of a stalk is invariant under an open immersion, since
the stalk map of an open immersion is an isomorphism. -/
public theorem isRegularLocalRing_stalk_iff {U X : Scheme.{u}}
    (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔
      IsRegularLocalRing (U.presheaf.stalk u) := by
  let e : X.presheaf.stalk (i.base u) ≃+* U.presheaf.stalk u :=
    (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e,
    fun _ => IsRegularLocalRing.of_ringEquiv e.symm⟩

end AlgebraicGeometry.IsOpenImmersion
