/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # Vertices of the coherent-isomorphism interval

Small neutral companion to upstream
`Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso`: a simplex of
`SSet.coherentIso` is determined by its sequence of vertices in
`CategoryTheory.WalkingIso`, recorded as `Bool`s by
`SSet.coherentIso.vertexBool` (through
`CategoryTheory.WalkingIso.equivBool`), and two simplices with the
same vertex pattern are equal by thinness
(`SSet.coherentIso.eq_of_forall_vertexBool_eq`). Both the
quasicategory extension theory
(`MathlibExt.AlgebraicTopology.Quasicategory.CoherentIsoExtension`)
and the Joyal endpoint theory (which needs only this vocabulary, not
`InvStruct` maps) use this identification.
-/

@[expose] public section

open CategoryTheory Opposite SimplexCategory.Truncated

open scoped Simplicial SimplicialObject.Truncated

universe u

namespace SSet

namespace coherentIso

/-- The `i`-th vertex of a simplex of `SSet.coherentIso`, recorded
as a `Bool`: `false` for `CategoryTheory.WalkingIso.zero` and
`true` for `CategoryTheory.WalkingIso.one`, via
`CategoryTheory.WalkingIso.equivBool`. -/
def vertexBool {n : ℕ} (s : coherentIso.{u} _⦋n⦌) (i : Fin (n + 1)) :
    Bool :=
  CategoryTheory.WalkingIso.equivBool (s.obj i)

/-- Two simplices of `SSet.coherentIso` with the same vertices are
equal, because `CategoryTheory.WalkingIso` is a thin category:
this is `CategoryTheory.nerve.ext_of_isThin` read through
`coherentIso.vertexBool`. -/
lemma eq_of_forall_vertexBool_eq {n : ℕ} {s t : coherentIso.{u} _⦋n⦌}
    (h : ∀ i : Fin (n + 1), vertexBool s i = vertexBool t i) : s = t := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  exact CategoryTheory.WalkingIso.equivBool.injective (h i)

end coherentIso

end SSet
