/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusAttractingSchemeModels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The actual attracting correspondence and closure-generated order

The correspondence is the native scheme image of the two evaluation
maps. Its nilpotents are retained. The order is exactly the transitive
closure of intersection of an attracting closure with a fixed component.
The full attracting set is the union over lower components, as in
Maulik--Okounkov1211.1287v3, Section3.2.3 and Lemma3.2.7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusAttractingOrderModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open AlgebraicWeightBundleModels TorusFixedSchemeModels TorusAttractingSchemeModels

variable [ThetaQuotientSources.ContractingAction ℂ]
  (A : Over base) [GrpObj A] (X : Over base) [ModObj A X]
  (lambda : Gm ⟶ A) [IsMonHom lambda]
  {F : FixedSchemeModel A X} (R : AttractingScheme A X lambda F)
  (Z : FixedComponents A X F)

/-- Actual evaluation at one on the represented zero-component fibre. -/
def attractingImage (i : Fin Z.count) : Set X.left :=
  Set.range (componentEvaluation A X lambda R (Z.component i))

/-- Closure intersection, with orientation lower precedes upper. -/
def closureStep (lower upper : Fin Z.count) : Prop :=
  ¬Disjoint (_root_.closure (attractingImage A X lambda R Z upper))
    (Set.range ((Z.component lower).toAmbient A X).left)

/-- No independent order relation or comparison matrix is supplied. -/
def precedes (lower upper : Fin Z.count) : Prop :=
  Relation.ReflTransGen (closureStep A X lambda R Z) lower upper

/-- The full attracting support uses exactly the lower-component images. -/
def fullAttracting (upper : Fin Z.count) : Set X.left :=
  ⋃ lower : Fin Z.count, ⋃ (_h : precedes A X lambda R Z lower upper),
    attractingImage A X lambda R Z lower

/-- The second evaluation is the native pullback projection to the fixed component. -/
def componentZero (i : Fin Z.count) :
    componentAttractor A X lambda R (Z.component i) ⟶ (Z.component i).data.scheme :=
  Over.homMk (pullback.snd R.evalZero.left (Z.component i).inclusion.left) (by
    change pullback.snd _ _ ≫ (Z.component i).data.scheme.hom =
      pullback.fst _ _ ≫ R.scheme.hom
    rw [← (Z.component i).inclusion.w, ← Category.assoc, ← pullback.condition]
    rw [Category.assoc, R.evalZero.w])

/-- The first evaluation is the original map to X over C. -/
def componentOne (i : Fin Z.count) :
    componentAttractor A X lambda R (Z.component i) ⟶ X :=
  Over.homMk (componentEvaluation A X lambda R (Z.component i)) (by
    change (pullback.fst _ _ ≫ R.evalOne.left) ≫ X.hom = _
    rw [Category.assoc, R.evalOne.w]
    rfl)

/-- The actual map to X times its fixed component. -/
def correspondenceMap (i : Fin Z.count) :
    componentAttractor A X lambda R (Z.component i) ⟶ X ⊗ (Z.component i).data.scheme :=
  CartesianMonoidalCategory.lift (componentOne A X lambda R Z i) (componentZero A X lambda R Z i)

/-- The actual image subscheme supplies the closed attracting correspondence. -/
def correspondenceScheme (i : Fin Z.count) : Scheme :=
  (correspondenceMap A X lambda R Z i).left.image

def correspondenceInclusion (i : Fin Z.count) :
    correspondenceScheme A X lambda R Z i ⟶ (X ⊗ (Z.component i).data.scheme).left :=
  (correspondenceMap A X lambda R Z i).left.imageι

/-- Its proper-supported trace uses this actual projection to X. -/
def correspondenceProjection (i : Fin Z.count) :
    correspondenceScheme A X lambda R Z i ⟶ X.left :=
  correspondenceInclusion A X lambda R Z i ≫ (fst X (Z.component i).data.scheme).left

end MathlibExt.AlgebraicGeometry.TorusAttractingOrderModels
