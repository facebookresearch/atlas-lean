/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean`
and
`P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.AlgebraicGeometry.Curve.Place

/-!
# The valuation of a place is trivial on constants

This file proves that the normalized valuation of a place of `F` over `K` is trivial on `K`.

## Main statement

* `AlgebraicCurve.Place.adicValuation_isTrivialOn`
-/

namespace CurveGenus.AdicValuationTrivialOn

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

private theorem _root_.AlgebraicCurve.Place.mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

private theorem rowMain : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.CurveGenus.AdicValuationTrivialOn.AlgebraicCurve in
/-- The normalized valuation of a place of `F` over `K` is trivial on the constants `K`. -/
public theorem _root_.AlgebraicCurve.Place.adicValuation_isTrivialOn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsTrivialOn K :=
  AlgebraicCurve.Place.rowMain v

end AdicValuationTrivialOn

end CurveGenus
