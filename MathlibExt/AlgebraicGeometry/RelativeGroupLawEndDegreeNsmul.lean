/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean` and
`Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow.lean`
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

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace RelativeGroupLaw

section CommRing

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- On a commutative relative group law, multiplication by one is the
identity endomorphism. -/
theorem nsmulEnd_one (G : RelativeGroupLaw R f) (hc : G.IsCommutative) :
    G.nsmulEnd hc 1 = G.idEnd :=
  End.ext (G.nsmul_one f idPoint)

end CommRing

section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

/-- On a commutative relative group law over a field, multiplication by one
has degree `1`. -/
theorem endDegree_nsmulEnd_one (G : RelativeGroupLaw K f) (hc : G.IsCommutative) :
    G.endDegree (G.nsmulEnd hc 1) = 1 := by
  rw [G.nsmulEnd_one hc, G.endDegree_idEnd]

end Field

end RelativeGroupLaw

end AlgebraicGeometry
