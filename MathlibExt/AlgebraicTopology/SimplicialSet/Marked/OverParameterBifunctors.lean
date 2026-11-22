/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterAdjunction

/-!
# Original marked slice parameter bifunctors

Original source and target maps act on the same complete relative prisms.
Their actions commute with both native pullback coordinates unchanged.
The original slice parameter tensor is natural in the marked source, and
its literal currying adjunction is a genuine parametrized adjunction.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Original source restriction and target postcomposition commute on the same full fixed-base prism. -/
theorem relativeMappingPre_post (k : ParameterMarking) {Z : Marked.{u}}
    {X X' Y Y' : Over Z} (f : X' ⟶ X) (g : Y ⟶ Y') :
    relativeMappingPre k f.left X.hom X'.hom Y.hom (Over.w f) ≫
        relativeMappingPost k X'.hom g.left Y.hom Y'.hom (Over.w g) =
      relativeMappingPost k X.hom g.left Y.hom Y'.hom (Over.w g) ≫
        relativeMappingPre k f.left X.hom X'.hom Y'.hom (Over.w f) := by
  let P := relativeMappingPre k f.left X.hom X'.hom Y.hom (Over.w f)
  let Q := relativeMappingPost k X'.hom g.left Y.hom Y'.hom (Over.w g)
  let R := relativeMappingPost k X.hom g.left Y.hom Y'.hom (Over.w g)
  let T := relativeMappingPre k f.left X.hom X'.hom Y'.hom (Over.w f)
  let a : relativeMappingComplex k X.hom Y.hom ⟶ mappingComplex k X.left Y.left :=
    pullback.fst (mappingComplexPost k X.left Y.hom) (mappingBasePoint k X.hom)
  let aP : relativeMappingComplex k X'.hom Y.hom ⟶ mappingComplex k X'.left Y.left :=
    pullback.fst (mappingComplexPost k X'.left Y.hom) (mappingBasePoint k X'.hom)
  let aR : relativeMappingComplex k X.hom Y'.hom ⟶ mappingComplex k X.left Y'.left :=
    pullback.fst (mappingComplexPost k X.left Y'.hom) (mappingBasePoint k X.hom)
  let a' : relativeMappingComplex k X'.hom Y'.hom ⟶ mappingComplex k X'.left Y'.left :=
    pullback.fst (mappingComplexPost k X'.left Y'.hom) (mappingBasePoint k X'.hom)
  have hP : P ≫ aP = a ≫ mappingComplexPre k f.left Y.left := relativeMappingPre_fst _ _ _ _ _ _
  have hQ : Q ≫ a' = aP ≫ mappingComplexPost k X'.left g.left := relativeMappingPost_fst _ _ _ _ _ _
  have hR : R ≫ aR = a ≫ mappingComplexPost k X.left g.left := relativeMappingPost_fst _ _ _ _ _ _
  have hT : T ≫ a' = aR ≫ mappingComplexPre k f.left Y'.left := relativeMappingPre_fst _ _ _ _ _ _
  apply (IsPullback.of_hasPullback (mappingComplexPost k X'.left Y'.hom)
    (mappingBasePoint k X'.hom)).hom_ext
  · change (P ≫ Q) ≫ a' = (R ≫ T) ≫ a'
    calc
      _ = P ≫ (aP ≫ mappingComplexPost k X'.left g.left) :=
        (Category.assoc _ _ _).trans (congrArg (fun t => P ≫ t) hQ)
      _ = (a ≫ mappingComplexPre k f.left Y.left) ≫ mappingComplexPost k X'.left g.left :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ _) hP)
      _ = a ≫ (mappingComplexPre k f.left Y.left ≫ mappingComplexPost k X'.left g.left) := Category.assoc _ _ _
      _ = a ≫ (mappingComplexPost k X.left g.left ≫ mappingComplexPre k f.left Y'.left) :=
        congrArg (fun t => a ≫ t) (mappingComplexPre_post k f.left g.left)
      _ = (a ≫ mappingComplexPost k X.left g.left) ≫ mappingComplexPre k f.left Y'.left := (Category.assoc _ _ _).symm
      _ = (R ≫ aR) ≫ mappingComplexPre k f.left Y'.left := congrArg (fun t => t ≫ _) hR.symm
      _ = R ≫ (aR ≫ mappingComplexPre k f.left Y'.left) := Category.assoc _ _ _
      _ = R ≫ (T ≫ a') := congrArg (fun t => R ≫ t) hT.symm
      _ = _ := (Category.assoc _ _ _).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original marked source acts by its actual product map over the same base. -/
def overParameterMap {Z : Marked.{u}} {X X' : Over Z} (f : X ⟶ X') :
    overParameterFunctor Z X ⟶ overParameterFunctor Z X' where
  app K := Over.homMk (prodMap (𝟙 (max K)) f.left) (by
    apply Hom.ext
    have h := congrArg Hom.hom (Over.w f)
    ext n a
    exact ConcreteCategory.congr_hom (congr_app h n) a.2)
  naturality K K' a := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl

/-- The genuine maximal-parameter tensor is covariant in original marked sources over the supplied base. -/
def overParameterBifunctor (Z : Marked.{u}) : Over Z ⥤ SSet.{u} ⥤ Over Z where
  obj X := overParameterFunctor Z X
  map f := overParameterMap f
  map_id X := by
    apply NatTrans.ext
    funext K
    apply Over.OverMorphism.ext
    exact prodMap_id (max K) X.left
  map_comp f g := by
    apply NatTrans.ext
    funext K
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl

/-- Relative maximal mapping spaces form the actual source-contravariant target-covariant slice bifunctor. -/
def overParameterMappingBifunctor (Z : Marked.{u}) : (Over Z)ᵒᵖ ⥤ Over Z ⥤ SSet.{u} where
  obj X := overTargetMappingFunctor .maximal Z X.unop
  map {X X'} f :=
    { app Y := relativeMappingPre .maximal f.unop.left X.unop.hom X'.unop.hom Y.hom (Over.w f.unop)
      naturality Y Y' g := (relativeMappingPre_post .maximal f.unop g).symm }
  map_id X := by
    apply NatTrans.ext
    funext Y
    exact relativeMappingPre_id .maximal X.unop.hom Y.hom
  map_comp {X X' X''} f g := by
    apply NatTrans.ext
    funext Y
    exact relativeMappingPre_comp .maximal f.unop.left g.unop.left _ _ _ Y.hom
      (Over.w f.unop) (Over.w g.unop)

/-- Currying retains the actual original marked source-product map and fixed-base prism restriction. -/
theorem overParameterHomEquiv_source {Z : Marked.{u}} {X X' : Over Z}
    (f : X ⟶ X') (K : SSet.{u}) (Y : Over Z) (g : overParameter Z X' K ⟶ Y) :
    overParameterHomEquiv Z X K Y ((overParameterMap f).app K ≫ g) =
      overParameterHomEquiv Z X' K Y g ≫
        relativeMappingPre .maximal f.left X'.hom X.hom Y.hom (Over.w f) := by
  let P := overParameterHomEquiv Z X K Y ((overParameterMap f).app K ≫ g)
  let Q := overParameterHomEquiv Z X' K Y g
  let T := relativeMappingPre .maximal f.left X'.hom X.hom Y.hom (Over.w f)
  let a : relativeMappingComplex .maximal X.hom Y.hom ⟶ mappingComplex .maximal X.left Y.left :=
    pullback.fst (mappingComplexPost .maximal X.left Y.hom) (mappingBasePoint .maximal X.hom)
  let a' : relativeMappingComplex .maximal X'.hom Y.hom ⟶ mappingComplex .maximal X'.left Y.left :=
    pullback.fst (mappingComplexPost .maximal X'.left Y.hom) (mappingBasePoint .maximal X'.hom)
  have hP : P ≫ a = maxCurry (prodMap (𝟙 (max K)) f.left ≫ g.left) := pullback.lift_fst _ _ _
  have hQ : Q ≫ a' = maxCurry g.left := pullback.lift_fst _ _ _
  have hT : T ≫ a = a' ≫ mappingComplexPre .maximal f.left Y.left := relativeMappingPre_fst _ _ _ _ _ _
  apply (IsPullback.of_hasPullback (mappingComplexPost .maximal X.left Y.hom)
    (mappingBasePoint .maximal X.hom)).hom_ext
  · change P ≫ a = (Q ≫ T) ≫ a
    calc
      _ = maxCurry (prodMap (𝟙 (max K)) f.left ≫ g.left) := hP
      _ = maxCurry g.left ≫ mappingComplexPre .maximal f.left Y.left := maxCurry_source f.left g.left
      _ = (Q ≫ a') ≫ mappingComplexPre .maximal f.left Y.left := congrArg (fun t => t ≫ _) hQ.symm
      _ = Q ≫ (a' ≫ mappingComplexPre .maximal f.left Y.left) := Category.assoc _ _ _
      _ = Q ≫ (T ≫ a) := congrArg (fun t => Q ≫ t) hT.symm
      _ = _ := (Category.assoc _ _ _).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Whole original slice currying is a genuine parametrized tensor/mapping adjunction. -/
def overParameterAdjunction₂ (Z : Marked.{u}) :
    overParameterBifunctor Z ⊣₂ overParameterMappingBifunctor Z :=
  ParametrizedAdjunction.mk' (overParameterAdjunction Z) (by
    intro X X' f K Y g
    let G : overParameter Z X' K ⟶ Y := g
    let A : overParameter Z X K ⟶ Y := (overParameterMap f).app K ≫ G
    let T : relativeMappingComplex .maximal X'.hom Y.hom ⟶
        relativeMappingComplex .maximal X.hom Y.hom :=
      relativeMappingPre .maximal f.left X'.hom X.hom Y.hom (Over.w f)
    change (overParameterAdjunction Z X).homEquiv K Y A =
      (overParameterAdjunction Z X').homEquiv K Y G ≫ T
    have hX : (overParameterAdjunction Z X).homEquiv =
        fun K Y => overParameterHomEquiv Z X K Y := Adjunction.mkOfHomEquiv_homEquiv _
    have hX' : (overParameterAdjunction Z X').homEquiv =
        fun K Y => overParameterHomEquiv Z X' K Y := Adjunction.mkOfHomEquiv_homEquiv _
    rw [hX, hX']
    exact overParameterHomEquiv_source f K Y G)

end SSet.Marked
