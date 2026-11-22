/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterBifunctors

/-!
# Actual original target-isomorphism naturality on relative marked maps

The existing target isomorphism is precisely the original relative
postcomposition map, retaining both native pullback coordinates.
Consequently source restriction is conjugated by those same actual
target isomorphisms. This compares whole maps in the original slice;
no replacement or marked-model outcome is used.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original relative target-isomorphism map is the same full native target postcomposition map. -/
theorem relativeMappingTargetIso_hom_eq_post (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (e : Y ≅ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (he : e.hom ≫ p' = p) :
    (relativeMappingTargetIso k r e p p' he).hom = relativeMappingPost k r e.hom p p' he := by
  let F := (relativeMappingTargetIso k r e p p' he).hom
  let G := relativeMappingPost k r e.hom p p' he
  let a : relativeMappingComplex k r p' ⟶ mappingComplex k X Y' :=
    pullback.fst (mappingComplexPost k X p') (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  have hF : F ≫ a = b ≫ mappingComplexPost k X e.hom := relativeMappingTargetIso_hom_fst k r e p p' he
  have hG : G ≫ a = b ≫ mappingComplexPost k X e.hom := relativeMappingPost_fst k r e.hom p p' he
  apply (IsPullback.of_hasPullback (mappingComplexPost k X p') (mappingBasePoint k r)).hom_ext
  · change F ≫ a = G ≫ a
    exact hF.trans hG.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original marked target isomorphism conjugates the same whole relative source restriction. -/
def overMappingRestrictionTargetIso (k : ParameterMarking) {Z : Marked.{u}}
    {X X' Y Y' : Over Z} (f : X ⟶ X') (e : Y ≅ Y') :
    Arrow.mk ((overMappingFunctor k Z Y).map f.op) ≅
      Arrow.mk ((overMappingFunctor k Z Y').map f.op) := by
  let h : Y.left ≅ Y'.left := (Over.forget Z).mapIso e
  let a := relativeMappingTargetIso k X'.hom h Y.hom Y'.hom (Over.w e.hom)
  let b := relativeMappingTargetIso k X.hom h Y.hom Y'.hom (Over.w e.hom)
  let P : relativeMappingComplex k X'.hom Y.hom ⟶ relativeMappingComplex k X.hom Y.hom :=
    (overMappingFunctor k Z Y).map f.op
  let Q : relativeMappingComplex k X'.hom Y'.hom ⟶ relativeMappingComplex k X.hom Y'.hom :=
    (overMappingFunctor k Z Y').map f.op
  let A : relativeMappingComplex k X'.hom Y.hom ⟶ relativeMappingComplex k X'.hom Y'.hom :=
    relativeMappingPost k X'.hom e.hom.left Y.hom Y'.hom (Over.w e.hom)
  let B : relativeMappingComplex k X.hom Y.hom ⟶ relativeMappingComplex k X.hom Y'.hom :=
    relativeMappingPost k X.hom e.hom.left Y.hom Y'.hom (Over.w e.hom)
  have ha : a.hom = A := relativeMappingTargetIso_hom_eq_post k X'.hom h Y.hom Y'.hom (Over.w e.hom)
  have hb : b.hom = B := relativeMappingTargetIso_hom_eq_post k X.hom h Y.hom Y'.hom (Over.w e.hom)
  have hPQ : P ≫ B = A ≫ Q := relativeMappingPre_post k f e.hom
  have hs : a.hom ≫ Q = P ≫ b.hom := by rw [ha, hb]; exact hPQ.symm
  exact Arrow.isoMk a b hs

end SSet.Marked
