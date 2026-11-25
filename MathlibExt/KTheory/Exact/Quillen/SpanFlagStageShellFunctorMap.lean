/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Exact.Quillen.Functor
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellNormalized
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality

/-!
# Exact-functor naturality of Stage-shell Quillen simplices

An additive exact functor carries the cross vertices and normalized shell
classes extracted from an edgewise Stage to their images in the Quillen
Q-construction.  These comparisons assemble into an isomorphism between the
Quillen simplex of the mapped Stage and the mapped original simplex, natural
in pointwise weak Stage morphisms.

This file only compares the extracted finite Quillen simplices.  It constructs
no Stage-grid map, outer-reindex coherence, nerve or diagonal map, realization,
weak equivalence, endpoint inverse, group comparison, spectrum map, or Q/S
equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance spanFlagStageShellFunctorMapWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance spanFlagStageShellFunctorMapWaldhausenD :
    WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

/-- The cross vertex of a mapped Stage is canonically the image of the
original cross vertex. -/
noncomputable def edgewiseStageVertexMapIso
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    edgewiseStageVertex ((mapStageWeak C D F _).obj A).obj k ≅
      F.obj (edgewiseStageVertex A.obj k) :=
  F.mapIso (Iso.refl _)

@[simp]
theorem edgewiseStageVertexMapIso_hom
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageVertexMapIso F A k).hom = F.map (𝟙 _) :=
  rfl

/-- The cross-vertex comparison is natural in pointwise weak Stage
morphisms. -/
theorem edgewiseStageVertexMapIso_naturality
    {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageVertexIso ((mapStageWeak C D F _).map f) k).trans
        (edgewiseStageVertexMapIso F B k) =
      (edgewiseStageVertexMapIso F A k).trans
        (F.mapIso (edgewiseStageVertexIso f k)) := by
  apply Iso.ext
  change F.map _ ≫ F.map (𝟙 _) = F.map (𝟙 _) ≫ F.map _
  simp

private theorem edgewiseStageShellSourceEqVertex_map
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellSourceEqVertex
        ((mapStageWeak C D F _).obj A).obj k l hkl =
      congrArg F.obj (edgewiseStageShellSourceEqVertex A.obj k l hkl) := by
  apply Subsingleton.elim

private theorem edgewiseStageShellTargetEqVertex_map
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellTargetEqVertex
        ((mapStageWeak C D F _).obj A).obj k l hkl =
      congrArg F.obj (edgewiseStageShellTargetEqVertex A.obj k l hkl) := by
  apply Subsingleton.elim

private theorem edgewiseStageShellMap_map
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l)
    {I J : Ar 3} (f : I ⟶ J) :
    ((reindexStage (C := D) (edgewiseShell a k l hkl)).obj
        ((mapStageWeak C D F _).obj A).obj).obj.map f =
      F.map (((reindexStage (C := C) (edgewiseShell a k l hkl)).obj
        A.obj).obj.map f) :=
  rfl

private theorem edgewiseStageShellSpan_map_l
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket
      ((mapStageWeak C D F _).obj A).obj k l hkl).span.l =
      F.map ((edgewiseStageShellPacket A.obj k l hkl).span.l) := by
  exact edgewiseStageShellMap_map F A k l hkl _

private theorem edgewiseStageShellSpan_map_r
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket
      ((mapStageWeak C D F _).obj A).obj k l hkl).span.r =
      F.map ((edgewiseStageShellPacket A.obj k l hkl).span.r) := by
  exact edgewiseStageShellMap_map F A k l hkl _

set_option backward.isDefEq.respectTransparency false in
private theorem edgewiseStageShellSpanNormalized_map_l
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized
      ((mapStageWeak C D F _).obj A).obj k l hkl).l =
      (QuillenSpan.map F
        (edgewiseStageShellSpanNormalized A.obj k l hkl)).l := by
  rw [edgewiseStageShellSpanNormalized_l, QuillenSpan.map_l,
    edgewiseStageShellSpanNormalized_l]
  rw [edgewiseStageShellSpan_map_l F A k l hkl]
  simp only [edgewiseStageShellPacket, QuillenStageShellData.span]
  rw [F.map_comp]
  simp only [eqToIso.hom]
  rw [edgewiseStageShellSourceEqVertex_map F A k l hkl]
  rw [← eqToHom_map F
    (edgewiseStageShellSourceEqVertex A.obj k l hkl)]

set_option backward.isDefEq.respectTransparency false in
private theorem edgewiseStageShellSpanNormalized_map_r
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized
      ((mapStageWeak C D F _).obj A).obj k l hkl).r =
      (QuillenSpan.map F
        (edgewiseStageShellSpanNormalized A.obj k l hkl)).r := by
  rw [edgewiseStageShellSpanNormalized_r, QuillenSpan.map_r,
    edgewiseStageShellSpanNormalized_r]
  rw [edgewiseStageShellSpan_map_r F A k l hkl]
  simp only [edgewiseStageShellPacket, QuillenStageShellData.span]
  rw [F.map_comp]
  simp only [eqToIso.hom]
  rw [edgewiseStageShellTargetEqVertex_map F A k l hkl]
  rw [← eqToHom_map F
    (edgewiseStageShellTargetEqVertex A.obj k l hkl)]

set_option backward.isDefEq.respectTransparency false in
/-- Exact-functor naturality of every normalized Stage-shell class.  The
mapped-Stage shell is compared first, followed by the target vertex
comparison. -/
theorem edgewiseStageShellClassNormalized_map
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized
          ((mapStageWeak C D F _).obj A).obj k l hkl ≫
        (QuillenQ.underlyingIso
          (edgewiseStageVertexMapIso F A l)).hom =
      (QuillenQ.underlyingIso
          (edgewiseStageVertexMapIso F A k)).hom ≫
        (QuillenQ.map F).map
          (edgewiseStageShellClassNormalized A.obj k l hkl) := by
  let S := edgewiseStageShellSpanNormalized
    ((mapStageWeak C D F _).obj A).obj k l hkl
  let T := QuillenSpan.map F
    (edgewiseStageShellSpanNormalized A.obj k l hkl)
  let eX := edgewiseStageVertexMapIso F A k
  let eY := edgewiseStageVertexMapIso F A l
  let eA : S.apex ≅ T.apex := Iso.refl T.apex
  have h := QuillenQ.mkHom_naturality_of_span_iso S T eX eY eA
    (by
      rw [edgewiseStageShellSpanNormalized_map_l F A k l hkl]
      change (𝟙 T.apex) ≫ T.l = T.l ≫ F.map (𝟙 _)
      simp)
    (by
      rw [edgewiseStageShellSpanNormalized_map_r F A k l hkl]
      change (𝟙 T.apex) ≫ T.r = T.r ≫ F.map (𝟙 _)
      simp)
  have hSource : QuillenQ.mkHom S =
      edgewiseStageShellClassNormalized
        ((mapStageWeak C D F _).obj A).obj k l hkl :=
    edgewiseStageShellSpanNormalized_mkHom _ _ _ _
  have hTarget :
      (QuillenQ.map F).map
          (edgewiseStageShellClassNormalized A.obj k l hkl) =
        QuillenQ.mkHom T := by
    rw [← edgewiseStageShellSpanNormalized_mkHom A.obj k l hkl]
    exact QuillenQ.map_mk F _
  have hLeft := congrArg
    (fun q => q ≫ (QuillenQ.underlyingIso eY).hom) hSource.symm
  have hRight := congrArg
    (fun q => (QuillenQ.underlyingIso eX).hom ≫ q) hTarget.symm
  exact hLeft.trans (h.trans hRight)

/-- The Quillen simplex extracted from a mapped Stage is canonically
isomorphic to the image of the original extracted simplex. -/
noncomputable def edgewiseStageQuillenSimplexMapIso
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    edgewiseStageQuillenSimplex ((mapStageWeak C D F _).obj A).obj ≅
      ((QuillenQ.map F).mapComposableArrows a.len).obj
        (edgewiseStageQuillenSimplex A.obj) := by
  refine ComposableArrows.isoMk
    (fun k => QuillenQ.underlyingIso
      (edgewiseStageVertexMapIso F A k)) ?_
  intro i hi
  let k : Fin (a.len + 1) := ⟨i, Nat.lt_add_one_of_lt hi⟩
  let l : Fin (a.len + 1) := ⟨i + 1, Nat.add_lt_add_right hi 1⟩
  have hkl : k ≤ l := by
    change i ≤ i + 1
    omega
  change edgewiseStageShellClassNormalized
        ((mapStageWeak C D F _).obj A).obj k l _ ≫
      (QuillenQ.underlyingIso
        (edgewiseStageVertexMapIso F A l)).hom =
    (QuillenQ.underlyingIso
        (edgewiseStageVertexMapIso F A k)).hom ≫
      (QuillenQ.map F).map
        (edgewiseStageShellClassNormalized A.obj k l _)
  exact edgewiseStageShellClassNormalized_map F A k l hkl

@[simp]
theorem edgewiseStageQuillenSimplexMapIso_hom_app
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageQuillenSimplexMapIso F A).hom.app k =
      (QuillenQ.underlyingIso (edgewiseStageVertexMapIso F A k)).hom :=
  rfl

/-- Arbitrary-interval characteristic square for the simplex comparison. -/
theorem edgewiseStageQuillenSimplexMapIso_naturality_homOfLE
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageQuillenSimplex
        ((mapStageWeak C D F _).obj A).obj).map (homOfLE hkl) ≫
        (edgewiseStageQuillenSimplexMapIso F A).hom.app l =
      (edgewiseStageQuillenSimplexMapIso F A).hom.app k ≫
        (((QuillenQ.map F).mapComposableArrows a.len).obj
          (edgewiseStageQuillenSimplex A.obj)).map (homOfLE hkl) := by
  exact (edgewiseStageQuillenSimplexMapIso F A).hom.naturality
    (homOfLE hkl)

/-- Exact-functor naturality of the extracted Quillen-simplex functor. -/
noncomputable def edgewiseStageQuillenSimplexFunctor_mapIso
    (a : SimplexCategory) :
    mapStageWeak C D F (edgewiseQ.obj a).len ⋙
        edgewiseStageQuillenSimplexFunctor D a ≅
      edgewiseStageQuillenSimplexFunctor C a ⋙
        (QuillenQ.map F).mapComposableArrows a.len := by
  refine NatIso.ofComponents
    (fun A => edgewiseStageQuillenSimplexMapIso F A) ?_
  intro A B f
  apply NatTrans.ext
  funext k
  change
    (QuillenQ.underlyingIso
        (edgewiseStageVertexIso ((mapStageWeak C D F _).map f) k)).hom ≫
      (QuillenQ.underlyingIso
        (edgewiseStageVertexMapIso F B k)).hom =
    (QuillenQ.underlyingIso
        (edgewiseStageVertexMapIso F A k)).hom ≫
      (QuillenQ.map F).map
        (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom
  calc
    _ = (QuillenQ.underlyingIso
          ((edgewiseStageVertexIso
              ((mapStageWeak C D F _).map f) k).trans
            (edgewiseStageVertexMapIso F B k))).hom := by
          rw [QuillenQ.underlyingIso_trans, Iso.trans_hom]
    _ = (QuillenQ.underlyingIso
          ((edgewiseStageVertexMapIso F A k).trans
            (F.mapIso (edgewiseStageVertexIso f k)))).hom := by
          rw [edgewiseStageVertexMapIso_naturality]
    _ = (QuillenQ.underlyingIso
          (edgewiseStageVertexMapIso F A k)).hom ≫
        (QuillenQ.underlyingIso
          (F.mapIso (edgewiseStageVertexIso f k))).hom := by
          rw [QuillenQ.underlyingIso_trans, Iso.trans_hom]
    _ = _ := by
      rw [show (QuillenQ.underlyingIso
          (F.mapIso (edgewiseStageVertexIso f k))).hom =
          (QuillenQ.map F).map
            (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom by
        exact congrArg Iso.hom
          (QuillenQ.underlyingIso_map F
            (edgewiseStageVertexIso f k)).symm]
      rfl

@[simp]
theorem edgewiseStageQuillenSimplexFunctor_mapIso_hom_app
    (a : SimplexCategory)
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app A =
      (edgewiseStageQuillenSimplexMapIso F A).hom :=
  rfl

@[simp]
theorem edgewiseStageQuillenSimplexFunctor_mapIso_hom_app_app
    (a : SimplexCategory)
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    ((edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app A).app k =
      (QuillenQ.underlyingIso (edgewiseStageVertexMapIso F A k)).hom :=
  rfl

/-- Componentwise naturality formula for the functor comparison. -/
theorem edgewiseStageQuillenSimplexFunctor_mapIso_hom_naturality
    (a : SimplexCategory)
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) :
    (edgewiseStageQuillenSimplexFunctor D a).map
          ((mapStageWeak C D F _).map f) ≫
        (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app B =
      (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app A ≫
        ((QuillenQ.map F).mapComposableArrows a.len).map
          ((edgewiseStageQuillenSimplexFunctor C a).map f) :=
  (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.naturality f

end AlgebraicKTheory

end
