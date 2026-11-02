/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian.lean`
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

public import MathlibExt.AlgebraicGeometry.SmoothReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Smooth morphisms preserve reducedness

A smooth morphism with reduced locally Noetherian target has reduced
source: smooth morphisms are geometrically reduced, and a flat morphism
with geometrically reduced fibers over a reduced locally Noetherian base
has reduced source.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SmoothReducedAux

private theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact AlgebraicGeometry.isReduced_of_smooth_over_field (g := snd) inferInstance

end SmoothReducedAux

namespace AlgebraicGeometry.Smooth

/-- A smooth morphism with reduced locally Noetherian target has reduced source. -/
theorem isReduced_of_isReduced_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by
  haveI := SmoothReducedAux.geometricallyReduced_of_smooth f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end AlgebraicGeometry.Smooth
