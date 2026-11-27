/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-! # Internal-hom vertex dictionary tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices`: the
vertex dictionary `SSet.ihomVertexEquiv`, precomposition and
postcomposition on internal-hom vertices, the Yoneda name of a
vertex, and evaluation of curried names at the monoidal unit and at
`Δ[0]`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace IhomVerticesTest

section Signatures

#check @SSet.ihomVertexEquiv
#check @SSet.ihomVertexEquiv_eq
#check @SSet.curry'_comp_pre_app
#check @SSet.ihomVertexEquiv_pre_app
#check @SSet.ihomVertexEquiv_ihom_map
#check @SSet.yonedaEquiv_symm_ihomVertexEquiv
#check @SSet.curry'_unitIsoSelf_hom
#check @SSet.curry'_evalDeltaZeroIso_hom
#check @SSet.yonedaEquiv_eq_unitHomEquiv
#check @SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv

end Signatures

section VertexDictionary

variable {A B C X : SSet.{u}}

/-- The vertex dictionary recovers the classifying map. -/
example (g : X ⟶ C) :
    (SSet.ihomVertexEquiv X C).symm (SSet.ihomVertexEquiv X C g) = g :=
  Equiv.symm_apply_apply _ _

/-- Every vertex is the vertex classified by its recovered map. -/
example (v : ((ihom X).obj C) _⦋0⦌) :
    SSet.ihomVertexEquiv X C ((SSet.ihomVertexEquiv X C).symm v) = v :=
  Equiv.apply_symm_apply _ _

/-- The dictionary is currying followed by `unitHomEquiv`. -/
example (g : X ⟶ C) :
    SSet.ihomVertexEquiv X C g =
      SSet.unitHomEquiv _ (MonoidalClosed.curry' g) :=
  SSet.ihomVertexEquiv_eq X C g

/-- Currying commutes with precomposition in the internal hom. -/
example (f : B ⟶ A) (g : A ⟶ C) :
    MonoidalClosed.curry' g ≫ (MonoidalClosed.pre f).app C =
      MonoidalClosed.curry' (f ≫ g) :=
  SSet.curry'_comp_pre_app f g

/-- Precomposition acts on vertices by precomposing the
classifying maps. -/
example (f : B ⟶ A) (g : A ⟶ C) :
    ((MonoidalClosed.pre f).app C).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv A C g) =
      SSet.ihomVertexEquiv B C (f ≫ g) :=
  SSet.ihomVertexEquiv_pre_app f g

/-- Postcomposition acts on vertices by postcomposing the classifying
maps. -/
example (g : X ⟶ B) (r : B ⟶ C) :
    ((ihom X).map r).app (op ⦋0⦌) (SSet.ihomVertexEquiv X B g) =
      SSet.ihomVertexEquiv X C (g ≫ r) :=
  SSet.ihomVertexEquiv_ihom_map g r

/-- The Yoneda name of a vertex is its curried name transported along
`Δ0IsoUnit`. -/
example (g : X ⟶ C) :
    SSet.yonedaEquiv.symm (SSet.ihomVertexEquiv X C g) =
      SSet.Δ0IsoUnit.hom ≫ MonoidalClosed.curry' g :=
  SSet.yonedaEquiv_symm_ihomVertexEquiv X C g

end VertexDictionary

section Evaluation

variable {C : SSet.{u}}

/-- Evaluation at the unit recovers a map from its curried name. -/
example (h : 𝟙_ SSet.{u} ⟶ C) :
    MonoidalClosed.curry' h ≫ (MonoidalClosed.unitIsoSelf C).hom = h :=
  SSet.curry'_unitIsoSelf_hom h

/-- Evaluation at `Δ[0]` recovers a point from its curried
name, up to the unit identification `Δ0IsoUnit`. -/
example (q : (Δ[0] : SSet.{u}) ⟶ C) :
    MonoidalClosed.curry' q ≫ (SSet.evalDeltaZeroIso C).hom =
      SSet.Δ0IsoUnit.inv ≫ q :=
  SSet.curry'_evalDeltaZeroIso_hom q

/-- On vertices, evaluation at `Δ[0]` sends the vertex
classified by a point to the vertex of the point itself. -/
example (q : (Δ[0] : SSet.{u}) ⟶ C) :
    ((SSet.evalDeltaZeroIso C).hom).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv (Δ[0]) C q) =
      SSet.yonedaEquiv q :=
  SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv q

/-- Applying the vertex evaluation to the identity point of
`Δ[0]` gives its Yoneda vertex. -/
example :
    ((SSet.evalDeltaZeroIso (Δ[0] : SSet.{u})).hom).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv (Δ[0]) (Δ[0] : SSet.{u}) (𝟙 _)) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
  SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv (𝟙 _)

/-- A point read through Yoneda agrees with the same point read
through the unit after any choice of vertex of `Δ[0]`. -/
example (s : 𝟙_ SSet.{u} ⟶ (Δ[0] : SSet.{u}))
    (q : (Δ[0] : SSet.{u}) ⟶ C) :
    SSet.yonedaEquiv q = SSet.unitHomEquiv C (s ≫ q) :=
  SSet.yonedaEquiv_eq_unitHomEquiv s q

/-- Evaluation of the vertex classified by `m` at a vertex is the
value of `m` at that vertex, for a nerve target. -/
example {X : SSet.{u}} {D : Type u} [Category.{u} D]
    (m : X ⟶ CategoryTheory.nerve D) (z : X _⦋0⦌) :
    ((ihom.ev X).app (CategoryTheory.nerve D)).app (op ⦋0⦌)
        (z, SSet.ihomVertexEquiv X _ m) = m.app (op ⦋0⦌) z :=
  SSet.ihom_ev_app_zero_ihomVertexEquiv m z

end Evaluation

section Axioms

#print axioms SSet.ihomVertexEquiv_pre_app
#print axioms SSet.ihomVertexEquiv_ihom_map
#print axioms SSet.yonedaEquiv_symm_ihomVertexEquiv
#print axioms SSet.curry'_evalDeltaZeroIso_hom
#print axioms SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv

end Axioms

end IhomVerticesTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet
