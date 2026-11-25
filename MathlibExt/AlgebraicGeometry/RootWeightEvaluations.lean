/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DenominatorRootStacks
public import MathlibExt.AlgebraicGeometry.ParabolicSheafCategories

/-!
# Actual root-weight lines and section-induced arrows on parameter schemes

The source weight sheaf is evaluated on every actual scheme T→U→X by
the native inverse-image generator followed by the literal diagonal
T→U×_X T. Lines are the actual groupified DF root lines on T. Positive
weight arrows are computed from the root section, unit, tensor product,
groupified positive comparison and multiplication; labels are retained.

The ordinary functor uses exactly these object and arrow maps, with its
algebraic identity/composition proof boundary explicit. Universal stack
weight lines and the pi_*(F tensor Lambda_v) comparison continue separately.

Source: Niels Borne and Angelo Vistoli,
https://arxiv.org/abs/1001.0466v2, Proposition 5.2/Corollary 5.4 and
Theorem 6.1, pp27–35.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootWeightEvaluations
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
open MathlibExt.AlgebraicGeometry.NativeTensorComparisons
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

universe u

/-- The actual labelled weight arrow induced by the positive DF section. -/
def lineArrow {Y : Scheme.{u}} {P : CommMonCat.{u}} {D : DeligneFaltingsChart Y P}
    (G : GroupifiedChart D) {v w : Weight P} (a : v ⟶ w) : G.line v.value ⟶ G.line w.value :=
  (tensorLeftUnit Y (G.line v.value)).inv ≫
    tensorMap (D.sectionMap a.label) (𝟙 (G.line v.value)) ≫
    tensorMap (G.positive a.label).inv (𝟙 (G.line v.value)) ≫
    (G.multiplication (Algebra.GrothendieckGroup.of a.label) v.value).hom ≫
    eqToHom (congrArg G.line a.equation)

/-- Proof laws for these fixed native line and section maps. -/
structure LineFunctorLaws {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} (G : GroupifiedChart D) where
  identity : ∀ v : Weight P, lineArrow G (𝟙 v) = 𝟙 (G.line v.value)
  composition : ∀ {v w z : Weight P} (a : v ⟶ w) (b : w ⟶ z),
    lineArrow G (a ≫ b) = lineArrow G a ≫ lineArrow G b

/-- The actual line-weight functor is implemented from the fixed object/map recipe. -/
def lineFunctor {Y : Scheme.{u}} {P : CommMonCat.{u}}
    {D : DeligneFaltingsChart Y P} {G : GroupifiedChart D} (K : LineFunctorLaws G) :
    Weight P ⥤ Y.Modules where
  obj v := G.line v.value
  map a := lineArrow G a
  map_id := K.identity
  map_comp := K.composition

abbrev identityEtale (T : Scheme.{u}) : T.Etale := Scheme.Etale.mk (𝟙 T)

/-- The genuine diagonal section of the source-etale base change. -/
def localDiagonal {X : Scheme.{u}} (U : X.Etale) (T : Over U.left) :
    identityEtale T.left ⟶ (etaleBaseChange (T.hom ≫ U.hom)).obj U :=
  MorphismProperty.Over.homMk
    (pullback.lift T.hom (𝟙 T.left) (Category.id_comp (T.hom ≫ U.hom)).symm) (by
      change pullback.lift T.hom (𝟙 T.left) _ ≫
        pullback.snd U.hom (T.hom ≫ U.hom) = 𝟙 T.left
      exact pullback.lift_snd _ _ _)

/-- Native inverse-image generators, restricted along the actual diagonal. -/
def localGenerators {X : Scheme.{u}}
    (B : DeligneFaltingsSheaves.MonoidSheaf X) (U : X.Etale) (T : Over U.left)
    [HasInverseImage (T.hom ≫ U.hom)] :
    B.obj.obj (op U) →* ((monoidPullback (T.hom ≫ U.hom)).obj B).obj.obj
      (op (identityEtale T.left)) :=
  (((monoidPullback (T.hom ≫ U.hom)).obj B).obj.map (localDiagonal U T).op).hom.comp
    (generator (T.hom ≫ U.hom) B U)

variable {X : Scheme.{u}}
  [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{u})
  {A B : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A) (j : A ⟶ B)

/-- Actual family weight evaluation on every root object over every T→U. -/
def weightFunctorAt (U : X.Etale) (T : Over U.left)
    (E : rootsAt I D j (Over.mk (T.hom ≫ U.hom)))
    (G : GroupifiedDF E.of.extended) (K : LineFunctorLaws (G.chart (identityEtale T.left))) :
    Weight (B.obj.obj (op U)) ⥤ T.left.Modules :=
  weightMap (localGenerators B U T) ⋙ lineFunctor K

end MathlibExt.AlgebraicGeometry.RootWeightEvaluations
