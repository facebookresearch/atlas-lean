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

public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctorMap

/-!
# Tests for exact-functor naturality of Stage-shell Quillen simplices

The clients below keep the object and morphism universes of the source and
target exact categories independent.  They exercise the vertex, arbitrary
shell, simplex, and functor comparison formulas in degrees zero, one, two,
and a symbolic degree, including identity and composition on Stage
morphisms.  The packet makes no grid-lift, outer-reindex, nerve, realization,
weak-equivalence, group, spectrum, or direct Q/S-equivalence claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.KTheory.Categorical
namespace SpanFlagStageShellFunctorMapTests

open AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

section Symbolic

variable {a : SimplexCategory}
variable {A B E : StageWeakCategory C (edgewiseQ.obj a).len}

example (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    edgewiseStageVertex ((mapStageWeak C D F _).obj A).obj k ≅
      F.obj (edgewiseStageVertex A.obj k) :=
  edgewiseStageVertexMapIso F A k

example (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageVertexMapIso F A k).hom = F.map (𝟙 _) :=
  edgewiseStageVertexMapIso_hom F A k

example (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageVertexIso ((mapStageWeak C D F _).map f) k).trans
        (edgewiseStageVertexMapIso F B k) =
      (edgewiseStageVertexMapIso F A k).trans
        (F.mapIso (edgewiseStageVertexIso f k)) :=
  edgewiseStageVertexMapIso_naturality F f k

example (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized
          ((mapStageWeak C D F _).obj A).obj k l hkl ≫
        (QuillenQ.underlyingIso
          (edgewiseStageVertexMapIso F A l)).hom =
      (QuillenQ.underlyingIso
          (edgewiseStageVertexMapIso F A k)).hom ≫
        (QuillenQ.map F).map
          (edgewiseStageShellClassNormalized A.obj k l hkl) :=
  edgewiseStageShellClassNormalized_map F A k l hkl

example (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    edgewiseStageQuillenSimplex ((mapStageWeak C D F _).obj A).obj ≅
      ((QuillenQ.map F).mapComposableArrows a.len).obj
        (edgewiseStageQuillenSimplex A.obj) :=
  edgewiseStageQuillenSimplexMapIso F A

example (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageQuillenSimplexMapIso F A).hom.app k =
      (QuillenQ.underlyingIso (edgewiseStageVertexMapIso F A k)).hom :=
  edgewiseStageQuillenSimplexMapIso_hom_app F A k

example (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageQuillenSimplex
        ((mapStageWeak C D F _).obj A).obj).map (homOfLE hkl) ≫
        (edgewiseStageQuillenSimplexMapIso F A).hom.app l =
      (edgewiseStageQuillenSimplexMapIso F A).hom.app k ≫
        (((QuillenQ.map F).mapComposableArrows a.len).obj
          (edgewiseStageQuillenSimplex A.obj)).map (homOfLE hkl) :=
  edgewiseStageQuillenSimplexMapIso_naturality_homOfLE F A k l hkl

example :
    mapStageWeak C D F (edgewiseQ.obj a).len ⋙
        edgewiseStageQuillenSimplexFunctor D a ≅
      edgewiseStageQuillenSimplexFunctor C a ⋙
        (QuillenQ.map F).mapComposableArrows a.len :=
  edgewiseStageQuillenSimplexFunctor_mapIso F a

example (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app A =
      (edgewiseStageQuillenSimplexMapIso F A).hom :=
  edgewiseStageQuillenSimplexFunctor_mapIso_hom_app F a A

example (f : A ⟶ B) :
    (edgewiseStageQuillenSimplexFunctor D a).map
          ((mapStageWeak C D F _).map f) ≫
        (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app B =
      (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app A ≫
        ((QuillenQ.map F).mapComposableArrows a.len).map
          ((edgewiseStageQuillenSimplexFunctor C a).map f) :=
  edgewiseStageQuillenSimplexFunctor_mapIso_hom_naturality F a f

example (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (edgewiseStageQuillenSimplexFunctor D a).map
        ((mapStageWeak C D F _).map (𝟙 A)) = 𝟙 _ := by
  rw [(mapStageWeak C D F _).map_id]
  exact (edgewiseStageQuillenSimplexFunctor D a).map_id _

example (f : A ⟶ B) (g : B ⟶ E) :
    (edgewiseStageQuillenSimplexFunctor D a).map
        ((mapStageWeak C D F _).map (f ≫ g)) =
      (edgewiseStageQuillenSimplexFunctor D a).map
          ((mapStageWeak C D F _).map f) ≫
        (edgewiseStageQuillenSimplexFunctor D a).map
          ((mapStageWeak C D F _).map g) := by
  rw [(mapStageWeak C D F _).map_comp]
  exact (edgewiseStageQuillenSimplexFunctor D a).map_comp _ _

end Symbolic

section Degrees

example (A : StageWeakCategory C (edgewiseQ.obj ⦋0⦌).len) :
    edgewiseStageQuillenSimplex ((mapStageWeak C D F _).obj A).obj ≅
      ((QuillenQ.map F).mapComposableArrows ⦋0⦌.len).obj
        (edgewiseStageQuillenSimplex A.obj) :=
  edgewiseStageQuillenSimplexMapIso F A

example (A : StageWeakCategory C (edgewiseQ.obj ⦋1⦌).len) :
    edgewiseStageQuillenSimplex ((mapStageWeak C D F _).obj A).obj ≅
      ((QuillenQ.map F).mapComposableArrows ⦋1⦌.len).obj
        (edgewiseStageQuillenSimplex A.obj) :=
  edgewiseStageQuillenSimplexMapIso F A

example (A : StageWeakCategory C (edgewiseQ.obj ⦋2⦌).len) :
    edgewiseStageQuillenSimplex ((mapStageWeak C D F _).obj A).obj ≅
      ((QuillenQ.map F).mapComposableArrows ⦋2⦌.len).obj
        (edgewiseStageQuillenSimplex A.obj) :=
  edgewiseStageQuillenSimplexMapIso F A

end Degrees

section IdentityFunctor

variable {a : SimplexCategory}

example (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    edgewiseStageQuillenSimplex
        ((mapStageWeak C C (𝟭 C) _).obj A).obj ≅
      ((QuillenQ.map (𝟭 C)).mapComposableArrows a.len).obj
        (edgewiseStageQuillenSimplex A.obj) :=
  edgewiseStageQuillenSimplexMapIso (𝟭 C) A

example :
    mapStageWeak C C (𝟭 C) (edgewiseQ.obj a).len ⋙
        edgewiseStageQuillenSimplexFunctor C a ≅
      edgewiseStageQuillenSimplexFunctor C a ⋙
        (QuillenQ.map (𝟭 C)).mapComposableArrows a.len :=
  edgewiseStageQuillenSimplexFunctor_mapIso (𝟭 C) a

end IdentityFunctor

section Nonclaims

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridLiftMap

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridLiftMap_reindex

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridNerveMap

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenQSPointedEquiv

end Nonclaims

#print axioms AlgebraicKTheory.edgewiseStageVertexMapIso
#print axioms AlgebraicKTheory.edgewiseStageVertexMapIso_naturality
#print axioms AlgebraicKTheory.edgewiseStageShellClassNormalized_map
#print axioms AlgebraicKTheory.edgewiseStageQuillenSimplexMapIso
#print axioms AlgebraicKTheory.edgewiseStageQuillenSimplexMapIso_naturality_homOfLE
#print axioms AlgebraicKTheory.edgewiseStageQuillenSimplexFunctor_mapIso
#print axioms AlgebraicKTheory.edgewiseStageQuillenSimplexFunctor_mapIso_hom_naturality

end SpanFlagStageShellFunctorMapTests
end MathlibExtTest.KTheory.Categorical
