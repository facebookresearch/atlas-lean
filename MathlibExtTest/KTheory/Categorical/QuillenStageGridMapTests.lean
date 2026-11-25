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

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMap

/-!
# Tests for exact-functor maps of degreewise Quillen Stage-grid lifts

The clients retain four independent universes and exercise the discrete
Quillen-simplex action, mapped agreement, lift restriction, material and
retained-Q components, functor identity/composition, and both strict
projection laws in symbolic and low degrees.
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
namespace QuillenStageGridMapTests

open AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

section InstanceNonleak

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing C

end InstanceNonleak

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

section Symbolic

variable {a : SimplexCategory}
variable {X Y Z : QuillenStageGridLift C a}

example :
    Discrete (QuillenQSimplex C a) ⥤ Discrete (QuillenQSimplex D a) :=
  quillenQSimplexDiscreteMap F a

example (q : Discrete (QuillenQSimplex C a)) :
    ((quillenQSimplexDiscreteMap F a).obj q).as =
      ((QuillenQ.map F).mapComposableArrows a.len).obj q.as :=
  quillenQSimplexDiscreteMap_obj_as F a q

example :
    quillenQSimplexDiscreteInclusion C a ⋙
        (QuillenQ.map F).mapComposableArrows a.len =
      quillenQSimplexDiscreteMap F a ⋙
        quillenQSimplexDiscreteInclusion D a :=
  quillenQSimplexDiscreteInclusion_map F a

example :
    QuillenStageGridAgreement C a ⥤ QuillenStageGridAgreement D a :=
  quillenStageGridAgreementMap F a

example (A : QuillenStageGridAgreement C a) :
    ((quillenStageGridAgreementMap F a).obj A).left =
      (mapStageWeak C D F (edgewiseQ.obj a).len).obj A.left :=
  quillenStageGridAgreementMap_obj_left F a A

example (A : QuillenStageGridAgreement C a) :
    ((quillenStageGridAgreementMap F a).obj A).right.as =
      ((QuillenQ.map F).mapComposableArrows a.len).obj A.right.as :=
  quillenStageGridAgreementMap_obj_right_as F a A

example (A : QuillenStageGridAgreement C a) :
    ((quillenStageGridAgreementMap F a).obj A).hom =
      (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app A.left ≫
        ((QuillenQ.map F).mapComposableArrows a.len).map A.hom ≫
        (eqToIso (quillenQSimplexDiscreteInclusion_map F a)).hom.app
          A.right :=
  quillenStageGridAgreementMap_obj_hom F a A

example (X : QuillenStageGridLift C a) :
    IsIso ((quillenStageGridAgreementMap F a).obj X.obj).hom :=
  quillenStageGridAgreementMap_isLift F X

example : QuillenStageGridLift C a ⥤ QuillenStageGridLift D a :=
  quillenStageGridLiftMap F a

example (X : QuillenStageGridLift C a) :
    ((quillenStageGridLiftMap F a).obj X).grid =
      (mapStageWeak C D F (edgewiseQ.obj a).len).obj X.grid :=
  quillenStageGridLiftMap_obj_grid F a X

example (X : QuillenStageGridLift C a) :
    ((quillenStageGridLiftMap F a).obj X).q =
      ((QuillenQ.map F).mapComposableArrows a.len).obj X.q :=
  quillenStageGridLiftMap_obj_q F a X

example (f : X ⟶ Y) :
    ((quillenStageGridLiftMap F a).map f).hom.left =
      (mapStageWeak C D F (edgewiseQ.obj a).len).map f.hom.left :=
  quillenStageGridLiftMap_map_hom_left F a f

example (f : X ⟶ Y) :
    ((quillenStageGridLiftMap F a).map f).hom.right =
      (quillenQSimplexDiscreteMap F a).map f.hom.right :=
  quillenStageGridLiftMap_map_hom_right F a f

example (X : QuillenStageGridLift C a) :
    (quillenStageGridLiftMap F a).map (𝟙 X) = 𝟙 _ :=
  (quillenStageGridLiftMap F a).map_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    (quillenStageGridLiftMap F a).map (f ≫ g) =
      (quillenStageGridLiftMap F a).map f ≫
        (quillenStageGridLiftMap F a).map g :=
  (quillenStageGridLiftMap F a).map_comp f g

example :
    quillenStageGridLiftMap F a ⋙ quillenStageGridProjection D a =
      quillenStageGridProjection C a ⋙
        mapStageWeak C D F (edgewiseQ.obj a).len :=
  quillenStageGridLiftMap_gridProjection F a

example :
    quillenStageGridLiftMap F a ⋙ quillenStageGridQProjection D a =
      quillenStageGridQProjection C a ⋙
        quillenQSimplexDiscreteMap F a :=
  quillenStageGridLiftMap_qProjection F a

#guard_msgs (error, substring := true) in
#synth (quillenStageGridLiftMap F a).Full

#guard_msgs (error, substring := true) in
#synth (quillenStageGridLiftMap F a).Faithful

#guard_msgs (error, substring := true) in
#synth (quillenStageGridLiftMap F a).IsEquivalence

end Symbolic

section Degrees

example : QuillenStageGridLift C ⦋0⦌ ⥤ QuillenStageGridLift D ⦋0⦌ :=
  quillenStageGridLiftMap F ⦋0⦌

example : QuillenStageGridLift C ⦋1⦌ ⥤ QuillenStageGridLift D ⦋1⦌ :=
  quillenStageGridLiftMap F ⦋1⦌

example : QuillenStageGridLift C ⦋2⦌ ⥤ QuillenStageGridLift D ⦋2⦌ :=
  quillenStageGridLiftMap F ⦋2⦌

end Degrees

section Nonclaims

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridAgreementMap_reindex

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridLiftMap_reindex

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridNerveMap

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenQSPointedEquiv

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridToStageSpectrumMap

end Nonclaims

#print axioms AlgebraicKTheory.quillenQSimplexDiscreteMap
#print axioms AlgebraicKTheory.quillenQSimplexDiscreteInclusion_map
#print axioms AlgebraicKTheory.quillenStageGridAgreementMap
#print axioms AlgebraicKTheory.quillenStageGridAgreementMap_isLift
#print axioms AlgebraicKTheory.quillenStageGridLiftMap
#print axioms AlgebraicKTheory.quillenStageGridLiftMap_obj_grid
#print axioms AlgebraicKTheory.quillenStageGridLiftMap_map_hom_left
#print axioms AlgebraicKTheory.quillenStageGridLiftMap_gridProjection
#print axioms AlgebraicKTheory.quillenStageGridLiftMap_qProjection

end QuillenStageGridMapTests
end MathlibExtTest.KTheory.Categorical
