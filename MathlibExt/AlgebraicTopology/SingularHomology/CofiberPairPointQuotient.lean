/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SingularHomology.PointedRelativeReducedComparison
public import
  MathlibExt.Topology.Category.TopPair.GoodPair
public import MathlibExt.Topology.Category.TopPair.PointQuotient

import MathlibExt.AlgebraicTopology.EilenbergSteenrod.GoodPairPointQuotient
import MathlibExt.AlgebraicTopology.SingularHomology.Coproducts
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Relative homology and reduced homology of point quotients

For a good pair, or for a pair with empty subspace, relative singular homology
is canonically isomorphic to reduced singular homology of its point quotient.
The good branch uses excision; the empty branch proves the canonical map an
isomorphism directly from the point-quotient pushout.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Pairs for which the point-quotient homology comparison is available. -/
def isPointQuotientHomologyPair : ObjectProperty TopPair.{w} :=
  fun P => Nonempty (TopPair.GoodPairData P) ∨ IsEmpty P.snd

/-- The full subcategory of good pairs and pairs with empty subspace. -/
abbrev PointQuotientHomologyPair :=
  isPointQuotientHomologyPair.FullSubcategory

namespace PointQuotientHomologyPair

/-- Forget the evidence that a pair is good or has empty subspace. -/
abbrev inclusion : PointQuotientHomologyPair.{w} ⥤ TopPair.{w} :=
  ObjectProperty.ι isPointQuotientHomologyPair

end PointQuotientHomologyPair

private abbrev pairArrow : TopPair.{w} ⥤ Arrow TopCat.{w} :=
  MorphismProperty.Arrow.forget _ _ _

private abbrev pairLeft (P : TopPair.{w}) : TopCat.{w} :=
  Arrow.leftFunc.obj (pairArrow.obj P)

private abbrev pairRight (P : TopPair.{w}) : TopCat.{w} :=
  Arrow.rightFunc.obj (pairArrow.obj P)

private abbrev pairMap (P : TopPair.{w}) : pairLeft P ⟶ pairRight P :=
  (pairArrow.obj P).hom

private def isInitialOfIsEmptyTopCat (X : TopCat.{w}) [IsEmpty X] :
    IsInitial X :=
  IsInitial.ofUniqueHom
    (fun Y => TopCat.ofHom
      ⟨isEmptyElim, continuous_of_discreteTopology⟩)
    (fun _ f => by
      apply ConcreteCategory.hom_ext
      intro x
      exact isEmptyElim x)

set_option linter.style.haveILetI false in
private theorem emptyPointQuotientChainSquare_isPushout
    (R : C) (P : TopPair.{w}) [IsEmpty P.snd] :
    IsPushout
      (((singularChainComplexFunctor C).obj R).map (pairMap P))
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.isTerminalPUnit.from (pairLeft P)))
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.pointQuotientProjection.app (pairArrow.obj P)))
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.pointQuotientPoint (pairArrow.obj P))) := by
  let chain := (singularChainComplexFunctor C).obj R
  let hTop : IsColimit
      (BinaryCofan.mk
        (TopCat.pointQuotientProjection.app (pairArrow.obj P))
        (TopCat.pointQuotientPoint (pairArrow.obj P))) := by
    change IsColimit
      (BinaryCofan.mk
        (pushout.inl P.map (TopCat.isTerminalPUnit.from P.snd))
        (pushout.inr P.map (TopCat.isTerminalPUnit.from P.snd)))
    exact isCoproductOfIsInitialIsPushout _ _ P.map
      (TopCat.isTerminalPUnit.from P.snd)
      (isInitialOfIsEmptyTopCat P.snd)
      (pushoutIsPushout P.map (TopCat.isTerminalPUnit.from P.snd))
  letI : PreservesFiniteCoproducts chain := ⟨fun n => by
      letI : PreservesColimitsOfShape
          (Discrete (ULift.{w} (Fin n))) chain :=
        singularChainComplexFunctorObj_preservesColimitsOfShape_discrete
          R (ULift.{w} (Fin n))
      exact preservesColimitsOfShape_of_equiv
        (Discrete.equivalence Equiv.ulift) chain⟩
  let hMapped := mapIsColimitOfPreservesOfIsColimit chain
    (TopCat.pointQuotientProjection.app (pairArrow.obj P))
    (TopCat.pointQuotientPoint (pairArrow.obj P)) hTop
  letI : IsEmpty (pairLeft P) := inferInstanceAs (IsEmpty P.snd)
  let hZero := isZero_singularChainFunctor_of_isEmpty C R (pairLeft P)
  have h := IsPushout.of_is_coproduct' hMapped hZero.isInitial
  dsimp [chain] at h ⊢
  convert h using 1 <;> apply hZero.eq_of_src

private theorem emptyPointQuotientRelativeChainMap_isIso
    (R : C) (P : TopPair.{w}) [IsEmpty P.snd] :
    IsIso ((relativeSingularChainFunctor C R).map
      (TopPair.pointQuotientComparison.app P)) := by
  let hPush := emptyPointQuotientChainSquare_isPushout C R P
  change IsIso (cokernel.map
    (((singularChainComplexFunctor C).obj R).map (pairMap P))
    (((singularChainComplexFunctor C).obj R).map
      (TopCat.pointQuotientPoint (pairArrow.obj P)))
    (((singularChainComplexFunctor C).obj R).map
      (TopCat.isTerminalPUnit.from (pairLeft P)))
    (((singularChainComplexFunctor C).obj R).map
      (TopCat.pointQuotientProjection.app (pairArrow.obj P)))
    hPush.w)
  exact isIso_cokernel_map_of_isPushout hPush

set_option linter.style.haveILetI false in
/-- The canonical point-quotient pair map induces an isomorphism on relative
homology when the original subspace is empty. -/
theorem isIso_relativeSingularHomology_map_pointQuotientComparison_of_isEmpty
    (R : C) (P : TopPair.{w}) [IsEmpty P.snd] (n : ℕ) :
    IsIso ((relativeSingularHomologyFunctor C R n).map
      (TopPair.pointQuotientComparison.app P)) := by
  letI : IsIso ((relativeSingularChainFunctor C R).map
      (TopPair.pointQuotientComparison.app P)) :=
    emptyPointQuotientRelativeChainMap_isIso C R P
  change IsIso (HomologicalComplex.homologyMap
    ((relativeSingularChainFunctor C R).map
      (TopPair.pointQuotientComparison.app P)) n)
  infer_instance

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Relative homology of a good pair, or a pair with empty subspace, is
naturally isomorphic to reduced homology of its point quotient. -/
noncomputable def pointQuotientRelativeReducedSingularHomologyNatIso
    (R : C) (n : ℕ)
    [(singularHomologyIntData C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive] :
    PointQuotientHomologyPair.inclusion ⋙
        relativeSingularHomologyFunctor C R n ≅
      PointQuotientHomologyPair.inclusion ⋙
        TopPair.pointQuotientFunctor ⋙
        Under.forget (TopCat.of PUnit) ⋙
        reducedSingularHomologyFunctor C R n := by
  let pointedRelativeReducedIso :=
    pointedRelativeReducedSingularHomologyNatIso C R n
  let β : PointQuotientHomologyPair.inclusion ⋙
        relativeSingularHomologyFunctor C R n ⟶
      PointQuotientHomologyPair.inclusion ⋙
        TopPair.pointQuotientFunctor ⋙
        Under.forget (TopCat.of PUnit) ⋙
        reducedSingularHomologyFunctor C R n := by
    refine
      { app := fun P =>
          (relativeSingularHomologyFunctor C R n).map
              (TopPair.pointQuotientComparison.app P.obj) ≫
            pointedRelativeReducedIso.inv.app
              (TopPair.pointQuotientFunctor.obj P.obj)
        naturality := ?_ }
    intro P Q f
    let qf := TopPair.pointQuotientFunctor.map f.hom
    have hPointedRelativeReducedNaturality :=
      pointedRelativeReducedIso.inv.naturality qf
    have hPoint :
        f.hom ≫ TopPair.pointQuotientComparison.app Q.obj =
          TopPair.pointQuotientComparison.app P.obj ≫
            TopPair.pointQuotientPairFunctor.map f.hom := by
      simpa using TopPair.pointQuotientComparison.naturality f.hom
    change
      (relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientPairFunctor.map f.hom) ≫
          pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj Q.obj) =
        pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj P.obj) ≫
          (reducedSingularHomologyFunctor C R n).map
            qf.right at hPointedRelativeReducedNaturality
    change
      (relativeSingularHomologyFunctor C R n).map f.hom ≫
          ((relativeSingularHomologyFunctor C R n).map
              (TopPair.pointQuotientComparison.app Q.obj) ≫
            pointedRelativeReducedIso.inv.app
              (TopPair.pointQuotientFunctor.obj Q.obj)) =
        ((relativeSingularHomologyFunctor C R n).map
              (TopPair.pointQuotientComparison.app P.obj) ≫
            pointedRelativeReducedIso.inv.app
              (TopPair.pointQuotientFunctor.obj P.obj)) ≫
          (reducedSingularHomologyFunctor C R n).map qf.right
    calc
      _ = ((relativeSingularHomologyFunctor C R n).map f.hom ≫
          (relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientComparison.app Q.obj)) ≫
          pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj Q.obj) := by
        rw [Category.assoc]
      _ = (relativeSingularHomologyFunctor C R n).map
            (f.hom ≫ TopPair.pointQuotientComparison.app Q.obj) ≫
          pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj Q.obj) := by
        rw [Functor.map_comp]
      _ = (relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientComparison.app P.obj ≫
              TopPair.pointQuotientPairFunctor.map f.hom) ≫
          pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj Q.obj) := by
        rw [hPoint]
      _ = ((relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientComparison.app P.obj) ≫
          (relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientPairFunctor.map f.hom)) ≫
          pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj Q.obj) := by
        rw [Functor.map_comp]
      _ = (relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientComparison.app P.obj) ≫
          ((relativeSingularHomologyFunctor C R n).map
              (TopPair.pointQuotientPairFunctor.map f.hom) ≫
            pointedRelativeReducedIso.inv.app
              (TopPair.pointQuotientFunctor.obj Q.obj)) := by
        rw [Category.assoc]
      _ = (relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientComparison.app P.obj) ≫
          (pointedRelativeReducedIso.inv.app
              (TopPair.pointQuotientFunctor.obj P.obj) ≫
            (reducedSingularHomologyFunctor C R n).map qf.right) := by
        rw [hPointedRelativeReducedNaturality]
      _ = _ := by rw [Category.assoc]
  refine NatIso.ofComponents (fun P => ?_) ?_
  · let hCanon : IsIso
        ((relativeSingularHomologyFunctor C R n).map
          (TopPair.pointQuotientComparison.app P.obj)) := by
      rcases P.property with hGood | hEmpty
      · let d := Classical.choice hGood
        let hInt : IsIso (((singularHomologyIntData C R).Hₚ (n : ℤ)).map
            (TopPair.pointQuotientComparison.app P.obj)) :=
          TopPair.HomologyTheoryData.IsExact.isIso_map_pointQuotientComparison
            (singularHomologyIntData C R) (n : ℤ) d
        let hTarget : IsIso
            ((relativeSingularHomologyNatToIntIso C R n).hom.app
              (TopPair.pointQuotientPairFunctor.obj P.obj)) :=
          NatIso.hom_app_isIso _ _
        have hNat :=
          (relativeSingularHomologyNatToIntIso C R n).hom.naturality
            (TopPair.pointQuotientComparison.app P.obj)
        let hTail : IsIso
            (((singularHomologyIntData C R).Hₚ (n : ℤ)).map
                (TopPair.pointQuotientComparison.app P.obj) ≫
              (relativeSingularHomologyNatToIntIso C R n).hom.app
                (TopPair.pointQuotientPairFunctor.obj P.obj)) :=
          @IsIso.comp_isIso C _ _ _ _ _ _ hInt hTarget
        exact @IsIso.of_isIso_fac_left C _ _ _ _ _ _ _
          (NatIso.hom_app_isIso _ P.obj) hTail hNat.symm
      · letI : IsEmpty P.obj.snd := hEmpty
        exact
          isIso_relativeSingularHomology_map_pointQuotientComparison_of_isEmpty
            C R P.obj n
    let pointedRelativeReducedInvIsIso : IsIso
        (pointedRelativeReducedIso.inv.app
        (TopPair.pointQuotientFunctor.obj P.obj)) :=
      NatIso.inv_app_isIso _ _
    let hβ : IsIso (β.app P) := by
      change IsIso
        ((relativeSingularHomologyFunctor C R n).map
            (TopPair.pointQuotientComparison.app P.obj) ≫
          pointedRelativeReducedIso.inv.app
            (TopPair.pointQuotientFunctor.obj P.obj))
      exact @IsIso.comp_isIso C _ _ _ _ _ _ hCanon
        pointedRelativeReducedInvIsIso
    letI : IsIso (β.app P) := hβ
    exact asIso (β.app P)
  · intro P Q f
    change _ ≫ β.app Q = β.app P ≫ _
    exact β.naturality f

/-- The comparison component is the canonical relative point-quotient map
followed by the inverse pointed-relative/reduced comparison. -/
@[simp]
theorem pointQuotientRelativeReducedSingularHomologyNatIso_hom_app
    (R : C) (n : ℕ)
    [(singularHomologyIntData C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive]
    (P : PointQuotientHomologyPair.{w}) :
    (pointQuotientRelativeReducedSingularHomologyNatIso C R n).hom.app P =
      (relativeSingularHomologyFunctor C R n).map
          (TopPair.pointQuotientComparison.app P.obj) ≫
        (pointedRelativeReducedSingularHomologyNatIso C R n).inv.app
          (TopPair.pointQuotientFunctor.obj P.obj) := by
  rfl

omit [Abelian C] [HasCoproducts.{w} C] in
private theorem isoSquareInverse
    {A B C₀ D : C} (eA : A ≅ B) (eC : C₀ ≅ D)
    (f : A ⟶ C₀) (g : B ⟶ D)
    (h : f ≫ eC.hom = eA.hom ≫ g) :
    g ≫ eC.inv = eA.inv ≫ f := by
  apply (cancel_epi eA.hom).1
  calc
    eA.hom ≫ (g ≫ eC.inv) =
        (eA.hom ≫ g) ≫ eC.inv := (Category.assoc _ _ _).symm
    _ = (f ≫ eC.hom) ≫ eC.inv := by rw [h]
    _ = f ≫ (eC.hom ≫ eC.inv) := Category.assoc _ _ _
    _ = f := by simp
    _ = eA.hom ≫ (eA.inv ≫ f) := by simp

omit [Abelian C] [HasCoproducts.{w} C] in
private theorem naturalityComp
    {A B C₀ D E F : C}
    (fR : A ⟶ B) (gR : B ⟶ C₀)
    (fS : D ⟶ E) (gS : E ⟶ F)
    (a : A ⟶ D) (b : B ⟶ E) (c : C₀ ⟶ F)
    (hf : fR ≫ b = a ≫ fS)
    (hg : b ≫ gS = gR ≫ c) :
    a ≫ (fS ≫ gS) = (fR ≫ gR) ≫ c := by
  rw [← Category.assoc, ← hf, Category.assoc, hg, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem pointedRelativeReducedInverse_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : PointedTopCat.{w}) :
    ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
          (PointedTopCat.pointedPair.obj X) ≫
        (pointedRelativeReducedSingularHomologyNatIso C S n).inv.app X =
      (pointedRelativeReducedSingularHomologyNatIso C R n).inv.app X ≫
        ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right := by
  exact isoSquareInverse C
    ((pointedRelativeReducedSingularHomologyNatIso C R n).app X)
    ((pointedRelativeReducedSingularHomologyNatIso C S n).app X) _ _
    (pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient
      (C := C) (n := n) a X)

set_option backward.isDefEq.respectTransparency false in
/-- The point-quotient relative/reduced comparison is natural in the
coefficient object. -/
theorem pointQuotientRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ)
    [(singularHomologyIntData C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive]
    [(singularHomologyIntData C S :
      TopPair.HomologyTheoryData.{w} C).IsExcisive]
    (P : PointQuotientHomologyPair.{w}) :
    ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
          P.obj ≫
        (pointQuotientRelativeReducedSingularHomologyNatIso C S n).hom.app P =
      (pointQuotientRelativeReducedSingularHomologyNatIso C R n).hom.app P ≫
        ((reducedSingularHomologyCoefficientFunctor C n).map a).app
          (TopPair.pointQuotientFunctor.obj P.obj).right := by
  rw [pointQuotientRelativeReducedSingularHomologyNatIso_hom_app,
    pointQuotientRelativeReducedSingularHomologyNatIso_hom_app]
  let f := TopPair.pointQuotientComparison.app P.obj
  let X := TopPair.pointQuotientFunctor.obj P.obj
  have hRel :=
    ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).naturality f
  have hInv := pointedRelativeReducedInverse_naturality_coefficient C a n X
  exact naturalityComp C
    ((relativeSingularHomologyFunctor C R n).map f)
    ((pointedRelativeReducedSingularHomologyNatIso C R n).inv.app X)
    ((relativeSingularHomologyFunctor C S n).map f)
    ((pointedRelativeReducedSingularHomologyNatIso C S n).inv.app X)
    (((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
      P.obj)
    (((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
      (TopPair.pointQuotientPairFunctor.obj P.obj))
    (((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right)
    hRel hInv

end AlgebraicTopology
