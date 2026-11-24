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

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

/-- The one-fold sum of the identity point is the identity point. -/
theorem nsmul_one_idPoint (G : RelativeGroupLaw K f) :
    G.nsmul f 1 idPoint = idPoint :=
  G.nsmul_one f idPoint

/-- Exemplar of the end-degree formula at multiplication by one: the
degree is `1 ^ (2 * g)` for every `g`. -/
theorem endDegree_nsmul_one_idPoint_eq_pow (G : RelativeGroupLaw K f)
    (g : ℕ) :
    G.endDegree (G.nsmul f 1 idPoint) = 1 ^ (2 * g) := by
  rw [G.nsmul_one_idPoint]
  show G.endDegree (idEnd (f := f)) = 1 ^ (2 * g)
  rw [G.endDegree_idEnd, one_pow]

end RelativeGroupLaw

end AlgebraicGeometry
