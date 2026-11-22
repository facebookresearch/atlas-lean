/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalProjectiveDerivedColimits
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.KanExtensions
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Actual ordinary projective left Kan extensions and derived colimit comparison

Both plain-category projective models use the supplied original coefficient
generation data at its same cardinal. Working-size colimits construct every
actual comma-category Kan extension. The resulting genuine left Kan
adjunction is Quillen by both original objectwise right classes.

The original projective Q followed by the actual Kan functor preserves all
objectwise weak arrows and gives the full chosen derived adjunction on the
original homotopy categories. The canonical ordinary Kan/colimit Iso and
the comparison on the earned cofibrant Kan image of Q give the whole
derived Kan/homotopy-colimit comparison, with each original diagram and map.

No Kan functor, diagram model, source comparison or desired weak outcome
is supplied. Right Kan/injective alternatives, arbitrary homotopy-cofinality
and simplex diagonal/realization results remain separate source work.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w uJ vJ uK vK uC vC
open CategoryTheory Limits HomotopicalAlgebra Opposite
open CategoryTheory.Functor

namespace HomotopicalAlgebra.OriginalProjectiveLeftKan

variable {J : Type uJ} [Category.{vJ} J] [Small.{w} J] [LocallySmall.{w} J]
  {K : Type uK} [Category.{vK} K] [Small.{w} K] [LocallySmall.{w} K]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (u : J ⥤ K)

omit [Small.{w} K] in
include d in
private theorem pointwise_exists (F : J ⥤ C) : u.HasPointwiseLeftKanExtension F := by
  intro k
  let : HasColimitsOfShape (CostructuredArrow u k) C := d.hasColimitsOfShape
  infer_instance

omit [Small.{w} K] in
include d in
private theorem leftKan_exists (F : J ⥤ C) : u.HasLeftKanExtension F := by
  let : u.HasPointwiseLeftKanExtension F := pointwise_exists d u F
  infer_instance

omit [Small.{w} K] in
/-- The actual left Kan functor is constructed from the original coefficient colimits at every comma object. -/
def functor : (J ⥤ C) ⥤ (K ⥤ C) := by
  let : ∀ F : J ⥤ C, u.HasLeftKanExtension F := leftKan_exists d u
  exact u.lan

omit [Small.{w} K] in
/-- The genuine original left Kan unit and ordinary Hom functions give its full restriction adjunction. -/
def adjunction : functor d u ⊣ (whiskeringLeft J K C).obj u := by
  let : ∀ F : J ⥤ C, u.HasLeftKanExtension F := leftKan_exists d u
  exact u.lanAdjunction C

/-- Both original objectwise right classes earn the actual projective left Kan Quillen adjunction. -/
theorem isQuillen :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    (adjunction d u).IsQuillenAdjunction := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : ∀ F : J ⥤ C, u.HasLeftKanExtension F := leftKan_exists d u
  exact FunctorProjective.KanExtensions.isQuillen_of_pointwise_right_classes u
    (FunctorProjective.fibrations_eq (J := J) d)
    (FunctorProjective.fibrations_eq (J := K) d)
    (FunctorProjective.trivialFibrations_eq (J := J) d)
    (FunctorProjective.trivialFibrations_eq (J := K) d)

omit [Small.{w} K] in
/-- The pointwise original Kan value is the actual full comma colimit of the original diagram. -/
def objectIsoColimit (F : J ⥤ C) (k : K) :
    letI : u.HasPointwiseLeftKanExtension F := pointwise_exists d u F
    ((functor d u).obj F).obj k ≅ colimit (CostructuredArrow.proj u k ⋙ F) := by
  let : ∀ F : J ⥤ C, u.HasLeftKanExtension F := leftKan_exists d u
  let : u.HasPointwiseLeftKanExtension F := pointwise_exists d u F
  exact u.leftKanExtensionObjIsoColimit F k

/-- The original projective Q remains whole before its actual original Kan extension is taken. -/
def pointsetDerived : (J ⥤ C) ⥤ (K ⥤ C) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := J) d) ⋙ functor d u

/-- Every actual Kan image of the SAME original projective Q is projectively cofibrant by the earned Quillen adjunction.
-/
theorem pointsetDerived_cofibrant (F : J ⥤ C) :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    IsCofibrant ((pointsetDerived d u).obj F) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : (adjunction d u).IsQuillenAdjunction := isQuillen d u
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adjunction d u)
    (GeneratedFunctorialReplacements.Q_isCofibrant (FunctorProjective.generationData (D := J) d) F)

/-- The actual original Q/Kan composite is homotopical on every original objectwise weak diagram map. -/
theorem pointsetDerived_map_weak {F G : J ⥤ C} (f : F ⟶ G)
    (hf : (weakEquivalences C).functorCategory J f) :
    (weakEquivalences C).functorCategory K ((pointsetDerived d u).map f) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let dJ := FunctorProjective.generationData (D := J) d
  let : (adjunction d u).IsQuillenAdjunction := isQuillen d u
  have hf' : weakEquivalences (J ⥤ C) f := by rw [FunctorProjective.weakEquivalences_eq d]; exact hf
  let : WeakEquivalence ((GeneratedFunctorialReplacements.Q dJ).map f) :=
    (weakEquivalence_iff _).mpr (GeneratedFunctorialReplacements.Q_map_weak dJ f hf')
  let : IsCofibrant ((GeneratedFunctorialReplacements.Q dJ).obj F) :=
    GeneratedFunctorialReplacements.Q_isCofibrant dJ F
  let : IsCofibrant ((GeneratedFunctorialReplacements.Q dJ).obj G) :=
    GeneratedFunctorialReplacements.Q_isCofibrant dJ G
  have h : weakEquivalences (K ⥤ C) ((pointsetDerived d u).map f) :=
    (weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adjunction d u) _)
  rw [FunctorProjective.weakEquivalences_eq d] at h
  exact h

/-- The SAME original Kan adjunction and both original diagram Q/R records give ALL four derived conditions and the full
derived Hom/unit/counit. -/
def derivedAdjunctionData :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    QuillenDerivedAdjunctionData (adjunction d u) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : (adjunction d u).IsQuillenAdjunction := isQuillen d u
  exact DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (adjunction d u)
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d))
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := K) d))

/-- The ordinary actual Kan-colimit comparison retains the complete original Kan unit and both colimit functors. -/
def kanColimitIso :
    letI : HasColimitsOfShape J C := d.hasColimitsOfShape
    letI : HasColimitsOfShape K C := d.hasColimitsOfShape
    functor d u ⋙ (colim : (K ⥤ C) ⥤ C) ≅ (colim : (J ⥤ C) ⥤ C) := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : HasColimitsOfShape K C := d.hasColimitsOfShape
  let : ∀ F : J ⥤ C, u.HasLeftKanExtension F := leftKan_exists d u
  exact u.lanCompColimIso

/-- The actual original derived Kan and its earned cofibrancy give the entire original homotopy-colimit comparison. -/
def derivedKanColimitComparison :
    pointsetDerived d u ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⟶
      OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : HasColimitsOfShape K C := d.hasColimitsOfShape
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let Q := GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := J) d)
  exact whiskerLeft (pointsetDerived d u) (OriginalProjectiveDerivedColimits.comparison (J := K) d) ≫
    (associator Q (functor d u) colim).hom ≫ whiskerLeft Q (kanColimitIso d u).hom

/-- Actual cofibrancy of Kan(QF), the original comparison and the canonical Kan-colimit Iso earn weakness of the full
comparison. -/
theorem derivedKanColimitComparison_weak (F : J ⥤ C) :
    weakEquivalences C ((derivedKanColimitComparison d u).app F) := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : HasColimitsOfShape K C := d.hasColimitsOfShape
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let Q := GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := J) d)
  have hq := OriginalProjectiveDerivedColimits.comparison_weak_of_cofibrant d
    ((functor d u).obj (Q.obj F)) (pointsetDerived_cofibrant d u F)
  change weakEquivalences C
    ((OriginalProjectiveDerivedColimits.comparison (J := K) d).app ((functor d u).obj (Q.obj F)) ≫
      (𝟙 _ ≫ (kanColimitIso d u).hom.app (Q.obj F)))
  rw [Category.id_comp]
  exact (weakEquivalences C).comp_mem _ _ hq (mem_weakEquivalences _)

/-- Every actual original comparison component localizes to the full natural derived Kan/homotopy-colimit Iso. -/
def derivedKanColimitHoIso :
    pointsetDerived d u ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙
        toHomotopyCategory C ≅
      OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C := by
  let τ := whiskerRight (derivedKanColimitComparison d u) (toHomotopyCategory C)
  let (F : J ⥤ C) : IsIso (τ.app F) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (derivedKanColimitComparison_weak d u F)
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- Every full original diagram map preserves the entire actual derived Kan-colimit comparison. -/
theorem derivedKanColimitHoIso_naturality {F G : J ⥤ C} (f : F ⟶ G) :
    (pointsetDerived d u ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙
      toHomotopyCategory C).map f ≫ (derivedKanColimitHoIso d u).hom.app G =
    (derivedKanColimitHoIso d u).hom.app F ≫
      (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C).map f :=
  (derivedKanColimitHoIso d u).hom.naturality f

section FullDerivedComparison

local notation "HPJ" => toHomotopyCategory (J ⥤ C)
local notation "HPK" => toHomotopyCategory (K ⥤ C)
local notation "WPJ" => weakEquivalences (J ⥤ C)

/-- The full original chosen Kan derived functor is the left member of the actual constructed derived adjunction. -/
def derivedFunctor :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    HomotopyCategory (J ⥤ C) ⥤ HomotopyCategory (K ⥤ C) := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact (derivedAdjunctionData d u).leftDerived

/-- BOTH original projection functions retain the exact original Q/Kan functor on every source diagram. -/
def derivedFunctorProjection :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    HPJ ⋙ derivedFunctor d u ≅ pointsetDerived d u ⋙ HPK := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : (adjunction d u).IsQuillenAdjunction := isQuillen d u
  exact eqToIso (DerivedFunctorCoherence.left_projection (adjunction d u)
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d)))

private def sourceDerivedColimit :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    HomotopyCategory (J ⥤ C) ⥤ HomotopyCategory C := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact (OriginalProjectiveDerivedColimits.derivedAdjunctionData (J := J) d).leftDerived

private def sourceDerivedColimitProjection :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    HPJ ⋙ sourceDerivedColimit (J := J) d ≅
      OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C := by
  let : HasColimitsOfShape J C := d.hasColimitsOfShape
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction :=
    OriginalProjectiveDerivedColimits.colimit_isQuillen (J := J) d
  exact eqToIso (DerivedFunctorCoherence.left_projection (colimConstAdj (J := J) (C := C))
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d)))

/-- Every full composite projection keeps BOTH original Kan and colimit Q comparison maps. -/
def derivedCompositeProjection :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    HPJ ⋙ (derivedFunctor d u ⋙ sourceDerivedColimit (J := K) d) ≅
      pointsetDerived d u ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙
        toHomotopyCategory C := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  exact (associator HPJ (derivedFunctor d u) (sourceDerivedColimit (J := K) d)).symm ≪≫
    isoWhiskerRight (derivedFunctorProjection d u) (sourceDerivedColimit (J := K) d) ≪≫
      associator (pointsetDerived d u) HPK (sourceDerivedColimit (J := K) d) ≪≫
        isoWhiskerLeft (pointsetDerived d u) (sourceDerivedColimitProjection (J := K) d)

/-- Actual original Kan cofibrancy and the two full source projections give the derived Kan-colimit NatIso on ALL
projective-Ho objects and maps. -/
def derivedKanColimitIso :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    derivedFunctor d u ⋙ sourceDerivedColimit (J := K) d ≅ sourceDerivedColimit (J := J) d := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  let : Localization.Lifting HPJ WPJ
      (pointsetDerived d u ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙
        toHomotopyCategory C)
      (derivedFunctor d u ⋙ sourceDerivedColimit (J := K) d) := ⟨derivedCompositeProjection d u⟩
  let : Localization.Lifting HPJ WPJ
      (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C)
      (sourceDerivedColimit (J := J) d) := ⟨sourceDerivedColimitProjection (J := J) d⟩
  exact Localization.liftNatIso HPJ WPJ
    (pointsetDerived d u ⋙ OriginalProjectiveDerivedColimits.homotopyColimit (J := K) d ⋙
      toHomotopyCategory C)
    (OriginalProjectiveDerivedColimits.homotopyColimit (J := J) d ⋙ toHomotopyCategory C)
    (derivedFunctor d u ⋙ sourceDerivedColimit (J := K) d) (sourceDerivedColimit (J := J) d)
    (derivedKanColimitHoIso d u)

/-- Every full original projective-Ho morphism retains BOTH functions of the SAME derived Kan-colimit comparison. -/
theorem derivedKanColimitIso_naturality :
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    letI : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
    ∀ {F G : HomotopyCategory (J ⥤ C)} (f : F ⟶ G),
      (derivedFunctor d u ⋙ sourceDerivedColimit (J := K) d).map f ≫ (derivedKanColimitIso d u).hom.app G =
        (derivedKanColimitIso d u).hom.app F ≫ (sourceDerivedColimit (J := J) d).map f := by
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : ModelCategory (K ⥤ C) := FunctorProjective.modelCategory (J := K) d
  intro F G f
  exact (derivedKanColimitIso d u).hom.naturality f

end FullDerivedComparison

end HomotopicalAlgebra.OriginalProjectiveLeftKan
