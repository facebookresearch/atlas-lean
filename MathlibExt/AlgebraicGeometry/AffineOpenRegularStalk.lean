/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing.lean`
and
`P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing.lean`
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
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The stalk at a point of an affine open whose ring of sections is regular
is a regular local ring. -/
public theorem IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (hreg : IsRegularRing Γ(X, U))
    (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv

end AlgebraicGeometry
