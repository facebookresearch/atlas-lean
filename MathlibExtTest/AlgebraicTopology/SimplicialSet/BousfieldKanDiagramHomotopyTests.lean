/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagramHomotopy
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationHomotopy
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoherence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Tactic.NormNum

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject MonoidalCategory Simplicial Opposite
open CategoryTheory.SInverseS HomologicalComplex₂

namespace SSet

private abbrev Modules := ModuleCat.{0} ℤ
private def unitModule : Modules := ModuleCat.of ℤ ℤ
private def zeroPair : Pair Modules := ⟨0, 0⟩
private def stabilizedPair : Pair Modules :=
  ⟨unitModule ⊞ zeroPair.fst, unitModule ⊞ zeroPair.snd⟩
private def rawStabilization : RawHom zeroPair stabilizedPair :=
  RawHom.diagonalAdd unitModule zeroPair
private def stabilization : zeroPair ⟶ stabilizedPair := Hom.mk rawStabilization
private abbrev p : Pair Modules ⥤ Translation Modules := translationProjection
private def baseArrow : p.obj zeroPair ⟶ p.obj stabilizedPair := p.map stabilization

-- Pull the actual large comma diagram back along a finite small-hom-set
-- index. This tests general BK universes without enlarging the inherited wrapper.
private abbrev Index := InducedCategory WalkingSpan
  (fun j : ULift.{1} WalkingSpan => j.down)
private def indexFunctor : Index ⥤ Translation Modules :=
  inducedFunctor (fun j : ULift.{1} WalkingSpan => j.down) ⋙ span baseArrow baseArrow
private def diagram : Index ⥤ SSet.{1} :=
  indexFunctor ⋙ CostructuredArrow.functor p ⋙ CategoryTheory.nerveFunctor

private def scalar : Modules := unitModule ⊞ unitModule
private def exchange : scalar ≅ scalar := biprod.braiding unitModule unitModule

private def translationMap (A : Modules) : diagram ⟶ diagram where
  app j := nerveMap (secondTranslationCostructuredMap A (indexFunctor.obj j))
  naturality j k a := by
    change nerveMap (CostructuredArrow.map (S := p) (indexFunctor.map a)) ≫
        nerveMap (secondTranslationCostructuredMap A (indexFunctor.obj k)) =
      nerveMap (secondTranslationCostructuredMap A (indexFunctor.obj j)) ≫
        nerveMap (CostructuredArrow.map (S := p) (indexFunctor.map a))
    rw [nerveMap_comp, nerveMap_comp,
      secondTranslationCostructuredMap_naturality A (indexFunctor.map a)]

private def diagramHomotopy : DiagramHomotopy (translationMap scalar) (translationMap scalar) where
  app j := NatTrans.nerveHomotopy
    (secondTranslationCostructuredIsoOfIso exchange (indexFunctor.obj j)).hom
  naturality a := secondTranslationCostructuredIsoOfIso_nerveMap_baseChange
    exchange (indexFunctor.map a)

private def coefficient : AddCommGrpCat.{1} := AddCommGrpCat.of (ULift.{1} ℤ)
private abbrev K := bkAlternatingBicomplex AddCommGrpCat.{1} coefficient diagram
private def vertical := diagramHomotopy.bicomplexHomotopy AddCommGrpCat.{1} coefficient
private def totalHomotopy := verticalTotalHomotopy vertical

-- The stabilizer is the actual nonzero rank-one integral module.
example : ¬ IsZero rawStabilization.stabilizer := by
  intro h
  have hs : Subsingleton ℤ := ModuleCat.subsingleton_of_isZero h
  have he : (0 : ℤ) = 1 := hs.elim _ _
  norm_num at he

-- The scalar homotopy uses a nonidentity summand swap.
example : exchange ≠ Iso.refl scalar := by
  intro h
  have he := congrArg (fun e : scalar ≅ scalar =>
    (biprod.inl : unitModule ⟶ scalar) ≫ e.hom ≫
      (biprod.fst : scalar ⟶ unitModule)) h
  have hid : (𝟙 unitModule : unitModule ⟶ unitModule) = 0 := by
    simpa [exchange, scalar, biprod.braiding] using he.symm
  have he' := ConcreteCategory.congr_hom hid (1 : ℤ)
  change (1 : ℤ) = 0 at he'
  norm_num at he'

-- The zeroth outer face uses the genuine base-change map, not a constant diagram.
example :
    (StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit Index) diagram 0 0 ▷
        (Δ[1] : SSet.{1})) ≫ diagramHomotopy.barCylinder 0 =
      diagramHomotopy.barCylinder 1 ≫
        StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit Index) diagram 0 0 :=
  diagramHomotopy.barCylinder_δ 0 0

-- The inner degree-zero prism has the required minus sign.
example (p : ℕ) :
    (diagramHomotopy.verticalHomotopy AddCommGrpCat.{1} coefficient p).hom 0 1 =
      -((sigmaConst : AddCommGrpCat.{1} ⥤ (Type 1 ⥤ AddCommGrpCat.{1})).obj coefficient).map
        ((diagramHomotopy.barHomotopy p).toSimplicialObjectHomotopy.h (0 : Fin 1)) := by
  simpa using diagramHomotopy.verticalHomotopy_hom AddCommGrpCat.{1} coefficient p 0

-- Column zero has no extra total sign.
example :
    K.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫ totalHomotopy.hom 0 1 =
      (diagramHomotopy.verticalHomotopy AddCommGrpCat.{1} coefficient 0).hom 0 1 ≫
        K.ιTotal (ComplexShape.down ℕ) 0 1 1 rfl := by
  simpa [totalHomotopy, vertical] using
    ιTotal_verticalTotalHomotopy_hom vertical 0 0 0 rfl

-- Column one reverses the vertical sign, so its minus inner prism becomes positive.
example :
    K.ιTotal (ComplexShape.down ℕ) 1 0 1 rfl ≫ totalHomotopy.hom 1 2 =
      -((diagramHomotopy.verticalHomotopy AddCommGrpCat.{1} coefficient 1).hom 0 1 ≫
        K.ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) := by
  simpa [totalHomotopy, vertical, Units.neg_smul] using
    ιTotal_verticalTotalHomotopy_hom vertical 1 0 1 rfl

-- A prism on the filtration boundary remains in that same stage.
example :
    horizontalFilteredTotalι K 1 1 (⟨⟨(1, 0), rfl⟩, le_rfl⟩) ≫
        (horizontalFilteredTotalHomotopy vertical 1).hom 1 2 =
      -((vertical.hom 0 1).f 1 ≫
        horizontalFilteredTotalι K 1 2 (⟨⟨(1, 1), rfl⟩, le_rfl⟩)) := by
  simpa [horizontalFilteredTotalHomotopy, horizontalFilteredTotalHomotopyIndex,
    Units.neg_smul] using
    horizontalFilteredTotalHomotopyHom_ι vertical 1 1 (⟨⟨(1, 0), rfl⟩, le_rfl⟩)

example (n m : ℕ) : (horizontalCompleteFilteredTotalHomotopy vertical ⊥).hom n m = 0 :=
  horizontalCompleteFilteredTotalHomotopy_hom_bot vertical n m

example (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy vertical ((-1 : ℤ) : EInt)).hom n m = 0 :=
  horizontalCompleteFilteredTotalHomotopy_hom_coe_of_neg vertical (-1) (by norm_num) n m

example (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy vertical ⊤).hom n m = totalHomotopy.hom n m :=
  horizontalCompleteFilteredTotalHomotopy_hom_top vertical n m

example (n m : ℕ) :
    (horizontalFilteredTotalComplexMap K (show 0 ≤ 1 by omega)).f n ≫
        (horizontalFilteredTotalHomotopy vertical 1).hom n m =
      (horizontalFilteredTotalHomotopy vertical 0).hom n m ≫
        (horizontalFilteredTotalComplexMap K (show 0 ≤ 1 by omega)).f m :=
  horizontalFilteredTotalHomotopy_naturality vertical (show 0 ≤ 1 by omega) n m

private def interval : ComposableArrows EInt 1 :=
  ComposableArrows.mk₁ (homOfLE (show (0 : EInt) ≤ 1 by decide))

-- The interval map is the actual spectral-object cone, including its upper coordinate.
example (n m : ℤ) :
    (CochainComplex.mappingCone.inr
        ((horizontalCompleteFiltrationCochainDiagram K).map (interval.map' 0 1))).f n ≫
        (horizontalCompleteFiltrationMappingConeHomotopy vertical interval).hom n m =
      (horizontalCompleteFiltrationCochainHomotopy vertical (interval.obj 1)).hom n m ≫
        (CochainComplex.mappingCone.inr
          ((horizontalCompleteFiltrationCochainDiagram K).map (interval.map' 0 1))).f m :=
  horizontalCompleteFiltrationMappingConeHomotopy_inr vertical interval n m

end SSet
