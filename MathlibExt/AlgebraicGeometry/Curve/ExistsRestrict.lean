/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Place_exists_restrict_eq.lean`
and
`P2M/Sol/S_AlgebraicCurve_Place_exists_restrict_eq.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.FundamentalIdentityFiber

/-!
# Every place of a subfield lies under a place

This file proves that every place of `F'` lies under a place of a finite separable extension `M` of
`F'`.

## Main statement

* `AlgebraicCurve.Place.exists_restrict_eq`
-/

namespace CurveGenus.ExistsRestrict

noncomputable section
open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.CurveGenus.ExistsRestrict.AlgebraicCurve.Place in
/-- Every place of `F'` is the restriction of a place of a finite separable extension `M`. -/
public theorem _root_.AlgebraicCurve.Place.exists_restrict_eq {K F' M : Type*} [Field K]
    [Field F'] [Field M] [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [Algebra.IsSeparable F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w := by
  by_contra hne
  push Not at hne
  have hempty : w.fiberOver M = ∅ :=
    Finset.eq_empty_of_forall_notMem fun W hW => hne W (restrict_eq_of_mem_fiberOver w hW)
  have hsum := sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := M) w
  rw [hempty, Finset.sum_empty] at hsum
  have hpos : 0 < Module.finrank F' M := Module.finrank_pos
  omega

end

end ExistsRestrict

end CurveGenus
