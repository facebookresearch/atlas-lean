/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagramHomotopy
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationHomotopy
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoherence

/-!
# Actual filtered BK homotopies for second translations

The canonical scalar, zero and biproduct comma cylinders give actual
strictly natural diagram homotopies. Their inner prisms induce the signed
BK total homotopies and homotopies on every finite and complete horizontal
stage. The endpoints are the existing second-coordinate diagram maps.

This specialization retains the original second-translation maps and
cylinders at every common object/Hom universe of the input category.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject MonoidalCategory Simplicial
open HomologicalComplex₂

universe u

namespace CategoryTheory.SInverseS

/-- Canonical common-universe additive colimits for the filtered second-translation BK maps. -/
noncomputable local instance secondTranslationBKAdditiveColimits :
    HasColimitsOfSize.{u, u} AddCommGrpCat.{u} :=
  { has_colimits_of_shape := fun (J : Type u) (hJ : Category.{u} J) => by
      letI : Category.{u} J := hJ
      letI : Small.{u} J := small_self J
      exact AddCommGrpCat.hasColimitsOfShape.{u, u, u} (J := J) }

/-- Canonical common-universe additive coproducts for the filtered second-translation BK maps. -/
noncomputable local instance secondTranslationBKAdditiveCoproducts :
    HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun (J : Type u) => by
    let _ : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := secondTranslationBKAdditiveColimits
    exact HasColimitsOfSize.has_colimits_of_shape (C := AddCommGrpCat.{u}) (J := Discrete J)

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

local notation "D" => SSet.rightCommaNerveDiagram (translationProjection (C := C))

/-- The prescribed scalar-isomorphism cylinders form a strictly natural
homotopy of the actual second-translation diagram maps. -/
def secondTranslationDiagramScalarHomotopy {A A' : C} (e : A ≅ A') :
    SSet.DiagramHomotopy (secondTranslationRightCommaNerveDiagramNatTrans A)
      (secondTranslationRightCommaNerveDiagramNatTrans A') where
  app b := secondTranslationRightCommaScalarHomotopy e b
  naturality a := secondTranslationCostructuredIsoOfIso_nerveMap_baseChange e a

/-- The canonical zero cylinder is strictly natural and has the actual
second translation by zero and identity diagram map as endpoints. -/
def secondTranslationDiagramZeroHomotopy :
    SSet.DiagramHomotopy (secondTranslationRightCommaNerveDiagramNatTrans (0 : C)) (𝟙 D) where
  app b :=
    { h := (NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso b).hom).h
      h₀ := by
        change SSet.ι₀ ≫
          (NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso b).hom).h =
            nerveMap (secondTranslationCostructuredMap (0 : C) b)
        exact (NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso b).hom).h₀
      h₁ := by
        change SSet.ι₁ ≫
          (NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso b).hom).h =
            𝟙 (nerve (CostructuredArrow (translationProjection (C := C)) b))
        simpa only [nerveMap_id] using
          (NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso b).hom).h₁
      rel := (NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso b).hom).rel }
  naturality a := secondTranslationCostructuredZeroIso_nerveMap_baseChange a

/-- The canonical multiplication cylinder is strictly natural and compares
the sum translation with the prescribed composite of second translations. -/
def secondTranslationDiagramBiprodHomotopy (A A' : C) :
    SSet.DiagramHomotopy (secondTranslationRightCommaNerveDiagramNatTrans (A ⊞ A'))
      (secondTranslationRightCommaNerveDiagramNatTrans A' ≫
        secondTranslationRightCommaNerveDiagramNatTrans A) where
  app b :=
    { h := (NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' b).hom).h
      h₀ := by
        change SSet.ι₀ ≫
          (NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' b).hom).h =
            nerveMap (secondTranslationCostructuredMap (A ⊞ A') b)
        exact (NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' b).hom).h₀
      h₁ := by
        change SSet.ι₁ ≫
          (NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' b).hom).h =
            nerveMap (secondTranslationCostructuredMap A' b) ≫
              nerveMap (secondTranslationCostructuredMap A b)
        simpa only [nerveMap_comp] using
          (NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' b).hom).h₁
      rel := (NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' b).hom).rel }
  naturality a := secondTranslationCostructuredBiprodIso_nerveMap_baseChange A A' a

variable (R : AddCommGrpCat.{u})

local notation "K" => SSet.bkAlternatingBicomplex AddCommGrpCat R D

/-- The actual second-coordinate BK bicomplex endomorphism. -/
def secondTranslationBKBicomplexMap (A : C) : K ⟶ K :=
  (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} R).map
    (secondTranslationRightCommaNerveDiagramNatTrans A)

/-- The actual second-coordinate signed BK total endomorphism. -/
def secondTranslationBKTotalComplexMap (A : C) :
    SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R D ⟶
      SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R D :=
  (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} R).map
    (secondTranslationRightCommaNerveDiagramNatTrans A)

/-- The actual second-coordinate map on a finite horizontal-filtration stage. -/
def secondTranslationBKFiniteMap (A : C) (k : ℕ) :
    horizontalFilteredTotalComplex K k ⟶ horizontalFilteredTotalComplex K k :=
  horizontalFilteredTotalComplexMapOfBicomplex (secondTranslationBKBicomplexMap R A) k

/-- The actual second-coordinate map on an arbitrary complete filtration stage. -/
def secondTranslationBKCompleteMap (A : C) (i : EInt) :
    horizontalCompleteFilteredTotalComplex K i ⟶ horizontalCompleteFilteredTotalComplex K i :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex (secondTranslationBKBicomplexMap R A) i

/-- Scalar isomorphisms give the actual signed BK total homotopy. -/
def secondTranslationBKTotalScalarHomotopy {A A' : C} (e : A ≅ A') :
    _root_.Homotopy (secondTranslationBKTotalComplexMap R A)
      (secondTranslationBKTotalComplexMap R A') :=
  verticalTotalHomotopy ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy
    AddCommGrpCat.{u} R)

/-- The actual second translation by zero is chain homotopic to the identity of the BK total. -/
def secondTranslationBKTotalZeroHomotopy :
    _root_.Homotopy (secondTranslationBKTotalComplexMap R (0 : C))
      (𝟙 (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R D)) := by
  let H := verticalTotalHomotopy
    ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R)
  exact H.trans (_root_.Homotopy.ofEq (by
    change (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} R).map (𝟙 D) =
      𝟙 (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R D)
    exact (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} R).map_id D))

/-- Biproduct translation is chain homotopic to the prescribed composite on the actual BK total. -/
def secondTranslationBKTotalBiprodHomotopy (A A' : C) :
    _root_.Homotopy (secondTranslationBKTotalComplexMap R (A ⊞ A'))
      (secondTranslationBKTotalComplexMap R A' ≫ secondTranslationBKTotalComplexMap R A) := by
  let H := verticalTotalHomotopy
    ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R)
  exact H.trans (_root_.Homotopy.ofEq
    ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} R).map_comp _ _))

/-- Scalar isomorphisms give chain homotopies on every actual finite filtration stage. -/
def secondTranslationBKFiniteScalarHomotopy {A A' : C} (e : A ≅ A') (k : ℕ) :
    _root_.Homotopy (secondTranslationBKFiniteMap R A k)
      (secondTranslationBKFiniteMap R A' k) :=
  horizontalFilteredTotalHomotopy
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) k

/-- Zero translation is homotopic to the identity on every actual finite stage. -/
def secondTranslationBKFiniteZeroHomotopy (k : ℕ) :
    _root_.Homotopy (secondTranslationBKFiniteMap R (0 : C) k)
      (𝟙 (horizontalFilteredTotalComplex K k)) := by
  let H := horizontalFilteredTotalHomotopy
    ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) k
  exact H.trans (_root_.Homotopy.ofEq (by
    simp only [Functor.map_id, horizontalFilteredTotalComplexMapOfBicomplex_id]))

/-- Multiplication translation is homotopic to its actual composite on every finite stage. -/
def secondTranslationBKFiniteBiprodHomotopy (A A' : C) (k : ℕ) :
    _root_.Homotopy (secondTranslationBKFiniteMap R (A ⊞ A') k)
      (secondTranslationBKFiniteMap R A' k ≫ secondTranslationBKFiniteMap R A k) := by
  let H := horizontalFilteredTotalHomotopy
    ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) k
  exact H.trans (_root_.Homotopy.ofEq (by
    simp only [Functor.map_comp, horizontalFilteredTotalComplexMapOfBicomplex_comp,
      secondTranslationBKFiniteMap, secondTranslationBKBicomplexMap]))

/-- Scalar isomorphisms give the actual homotopies at all complete EInt stages. -/
def secondTranslationBKCompleteScalarHomotopy {A A' : C} (e : A ≅ A') (i : EInt) :
    _root_.Homotopy (secondTranslationBKCompleteMap R A i)
      (secondTranslationBKCompleteMap R A' i) :=
  horizontalCompleteFilteredTotalHomotopy
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) i

/-- The actual zero translation is homotopic to the identity at every complete stage. -/
def secondTranslationBKCompleteZeroHomotopy (i : EInt) :
    _root_.Homotopy (secondTranslationBKCompleteMap R (0 : C) i)
      (𝟙 (horizontalCompleteFilteredTotalComplex K i)) := by
  let H := horizontalCompleteFilteredTotalHomotopy
    ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) i
  exact H.trans (_root_.Homotopy.ofEq (by
    simp only [Functor.map_id, horizontalCompleteFilteredTotalComplexMapOfBicomplex_id]))

/-- The actual sum translation is homotopic to the prescribed composite at every complete stage. -/
def secondTranslationBKCompleteBiprodHomotopy (A A' : C) (i : EInt) :
    _root_.Homotopy (secondTranslationBKCompleteMap R (A ⊞ A') i)
      (secondTranslationBKCompleteMap R A' i ≫ secondTranslationBKCompleteMap R A i) := by
  let H := horizontalCompleteFilteredTotalHomotopy
    ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) i
  exact H.trans (_root_.Homotopy.ofEq (by
    simp only [Functor.map_comp, horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp,
      secondTranslationBKCompleteMap, secondTranslationBKBicomplexMap]))

/-- The actual scalar homotopy commutes with complete-stage inclusion into the BK total. -/
@[reassoc]
theorem secondTranslationBKCompleteScalarHomotopy_toTotal {A A' : C} (e : A ≅ A')
    (i : EInt) (n m : ℕ) :
    (secondTranslationBKCompleteScalarHomotopy R e i).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal K i).f m =
      (horizontalCompleteFilteredTotalToTotal K i).f n ≫
        (secondTranslationBKTotalScalarHomotopy R e).hom n m :=
  horizontalCompleteFilteredTotalHomotopy_toTotal
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) i n m

/-- The actual zero homotopy commutes with complete-stage inclusion into the BK total. -/
@[reassoc]
theorem secondTranslationBKCompleteZeroHomotopy_toTotal (i : EInt) (n m : ℕ) :
    (secondTranslationBKCompleteZeroHomotopy R i).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal K i).f m =
      (horizontalCompleteFilteredTotalToTotal K i).f n ≫
        (secondTranslationBKTotalZeroHomotopy R).hom n m := by
  simpa only [secondTranslationBKCompleteZeroHomotopy, secondTranslationBKTotalZeroHomotopy,
    _root_.Homotopy.trans_hom, _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalCompleteFilteredTotalHomotopy_toTotal
      ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) i n m

/-- The actual multiplication homotopy commutes with complete-stage inclusion into the total. -/
@[reassoc]
theorem secondTranslationBKCompleteBiprodHomotopy_toTotal
    (A A' : C) (i : EInt) (n m : ℕ) :
    (secondTranslationBKCompleteBiprodHomotopy R A A' i).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal K i).f m =
      (horizontalCompleteFilteredTotalToTotal K i).f n ≫
        (secondTranslationBKTotalBiprodHomotopy R A A').hom n m := by
  simpa only [secondTranslationBKCompleteBiprodHomotopy, secondTranslationBKTotalBiprodHomotopy,
    _root_.Homotopy.trans_hom, _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalCompleteFilteredTotalHomotopy_toTotal
      ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) i n m

/-- The actual scalar homotopy commutes with finite-stage inclusion into the BK total. -/
@[reassoc]
theorem secondTranslationBKFiniteScalarHomotopy_toTotal {A A' : C} (e : A ≅ A')
    (k n m : ℕ) :
    (secondTranslationBKFiniteScalarHomotopy R e k).hom n m ≫
        (horizontalFilteredTotalComplexToTotal K k).f m =
      (horizontalFilteredTotalComplexToTotal K k).f n ≫
        (secondTranslationBKTotalScalarHomotopy R e).hom n m :=
  horizontalFilteredTotalHomotopy_toTotal
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) k n m

/-- The actual zero homotopy commutes with finite-stage inclusion into the BK total. -/
@[reassoc]
theorem secondTranslationBKFiniteZeroHomotopy_toTotal (k n m : ℕ) :
    (secondTranslationBKFiniteZeroHomotopy R k).hom n m ≫
        (horizontalFilteredTotalComplexToTotal K k).f m =
      (horizontalFilteredTotalComplexToTotal K k).f n ≫
        (secondTranslationBKTotalZeroHomotopy R).hom n m := by
  simpa only [secondTranslationBKFiniteZeroHomotopy, secondTranslationBKTotalZeroHomotopy,
    _root_.Homotopy.trans_hom, _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalFilteredTotalHomotopy_toTotal
      ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) k n m

/-- The actual multiplication homotopy commutes with finite-stage inclusion into the total. -/
@[reassoc]
theorem secondTranslationBKFiniteBiprodHomotopy_toTotal (A A' : C) (k n m : ℕ) :
    (secondTranslationBKFiniteBiprodHomotopy R A A' k).hom n m ≫
        (horizontalFilteredTotalComplexToTotal K k).f m =
      (horizontalFilteredTotalComplexToTotal K k).f n ≫
        (secondTranslationBKTotalBiprodHomotopy R A A').hom n m := by
  simpa only [secondTranslationBKFiniteBiprodHomotopy, secondTranslationBKTotalBiprodHomotopy,
    _root_.Homotopy.trans_hom, _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalFilteredTotalHomotopy_toTotal
      ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) k n m

/-- Scalar homotopies commute with every complete filtration transition. -/
theorem secondTranslationBKCompleteScalarHomotopy_naturality {A A' : C} (e : A ≅ A')
    {i j : EInt} (hij : i ≤ j) (n m : ℕ) :
    (horizontalCompleteFilteredTotalMap K hij).f n ≫
        (secondTranslationBKCompleteScalarHomotopy R e j).hom n m =
      (secondTranslationBKCompleteScalarHomotopy R e i).hom n m ≫
        (horizontalCompleteFilteredTotalMap K hij).f m :=
  horizontalCompleteFilteredTotalHomotopy_naturality
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) hij n m

/-- Zero homotopies commute with every complete filtration transition. -/
theorem secondTranslationBKCompleteZeroHomotopy_naturality
    {i j : EInt} (hij : i ≤ j) (n m : ℕ) :
    (horizontalCompleteFilteredTotalMap K hij).f n ≫
        (secondTranslationBKCompleteZeroHomotopy R j).hom n m =
      (secondTranslationBKCompleteZeroHomotopy R i).hom n m ≫
        (horizontalCompleteFilteredTotalMap K hij).f m := by
  simpa only [secondTranslationBKCompleteZeroHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalCompleteFilteredTotalHomotopy_naturality
      ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) hij n m

/-- Multiplication homotopies commute with every complete filtration transition. -/
theorem secondTranslationBKCompleteBiprodHomotopy_naturality (A A' : C)
    {i j : EInt} (hij : i ≤ j) (n m : ℕ) :
    (horizontalCompleteFilteredTotalMap K hij).f n ≫
        (secondTranslationBKCompleteBiprodHomotopy R A A' j).hom n m =
      (secondTranslationBKCompleteBiprodHomotopy R A A' i).hom n m ≫
        (horizontalCompleteFilteredTotalMap K hij).f m := by
  simpa only [secondTranslationBKCompleteBiprodHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalCompleteFilteredTotalHomotopy_naturality
      ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) hij n m

/-- Scalar homotopies commute with every finite filtration transition. -/
theorem secondTranslationBKFiniteScalarHomotopy_naturality {A A' : C} (e : A ≅ A')
    {k l : ℕ} (hkl : k ≤ l) (n m : ℕ) :
    (horizontalFilteredTotalComplexMap K hkl).f n ≫
        (secondTranslationBKFiniteScalarHomotopy R e l).hom n m =
      (secondTranslationBKFiniteScalarHomotopy R e k).hom n m ≫
        (horizontalFilteredTotalComplexMap K hkl).f m :=
  horizontalFilteredTotalHomotopy_naturality
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) hkl n m

/-- Zero homotopies commute with every finite filtration transition. -/
theorem secondTranslationBKFiniteZeroHomotopy_naturality
    {k l : ℕ} (hkl : k ≤ l) (n m : ℕ) :
    (horizontalFilteredTotalComplexMap K hkl).f n ≫
        (secondTranslationBKFiniteZeroHomotopy R l).hom n m =
      (secondTranslationBKFiniteZeroHomotopy R k).hom n m ≫
        (horizontalFilteredTotalComplexMap K hkl).f m := by
  simpa only [secondTranslationBKFiniteZeroHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalFilteredTotalHomotopy_naturality
      ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) hkl n m

/-- Multiplication homotopies commute with every finite filtration transition. -/
theorem secondTranslationBKFiniteBiprodHomotopy_naturality (A A' : C)
    {k l : ℕ} (hkl : k ≤ l) (n m : ℕ) :
    (horizontalFilteredTotalComplexMap K hkl).f n ≫
        (secondTranslationBKFiniteBiprodHomotopy R A A' l).hom n m =
      (secondTranslationBKFiniteBiprodHomotopy R A A' k).hom n m ≫
        (horizontalFilteredTotalComplexMap K hkl).f m := by
  simpa only [secondTranslationBKFiniteBiprodHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, Pi.zero_apply, add_zero] using
    horizontalFilteredTotalHomotopy_naturality
      ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) hkl n m

/-- The actual second-coordinate map on each interval cone of the spectral object. -/
def secondTranslationBKIntervalMap (A : C) (I : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationMappingConeFunctor K).obj I ⟶
      (horizontalCompleteFiltrationMappingConeFunctor K).obj I :=
  (horizontalCompleteFiltrationMappingConeNatTrans (secondTranslationBKBicomplexMap R A)).app I

/-- The scalar homotopy acts on the actual interval cone, with the
prescribed second-translation interval maps as endpoints. -/
def secondTranslationBKIntervalScalarHomotopy {A A' : C} (e : A ≅ A')
    (I : ComposableArrows EInt 1) :
    _root_.Homotopy (secondTranslationBKIntervalMap R A I)
      (secondTranslationBKIntervalMap R A' I) :=
  horizontalCompleteFiltrationMappingConeHomotopy
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat.{u} R) I

/-- Zero translation is homotopic to the identity on every actual interval cone. -/
def secondTranslationBKIntervalZeroHomotopy (I : ComposableArrows EInt 1) :
    _root_.Homotopy (secondTranslationBKIntervalMap R (0 : C) I)
      (𝟙 ((horizontalCompleteFiltrationMappingConeFunctor K).obj I)) := by
  let H := horizontalCompleteFiltrationMappingConeHomotopy
    ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat.{u} R) I
  exact H.trans (_root_.Homotopy.ofEq (by
    simp only [Functor.map_id, horizontalCompleteFiltrationMappingConeNatTrans_id]))

/-- Sum translation is homotopic to the prescribed composite on every actual interval cone. -/
def secondTranslationBKIntervalBiprodHomotopy (A A' : C) (I : ComposableArrows EInt 1) :
    _root_.Homotopy (secondTranslationBKIntervalMap R (A ⊞ A') I)
      (secondTranslationBKIntervalMap R A' I ≫ secondTranslationBKIntervalMap R A I) := by
  let H := horizontalCompleteFiltrationMappingConeHomotopy
    ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat.{u} R) I
  exact H.trans (_root_.Homotopy.ofEq (by
    simp only [Functor.map_comp, horizontalCompleteFiltrationMappingConeNatTrans_comp,
      secondTranslationBKIntervalMap, secondTranslationBKBicomplexMap]))

end CategoryTheory.SInverseS
