/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberConnectingIntegerPi
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison

/-!
# Actual original Q cofiber rotation on integer homotopy

The next cofiber uses the actual target inclusion of the same original Q
arrow. Its Q counit is compared with the strict chosen cofiber by actual
cofibrant pushout gluing. Rotation then reaches the unchanged original
I-Q suspension. The following boundary retains the reversal constructed
from the two original weak double-cone collapses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberRotationIntegerPiGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberConnectingIntegerPiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index.{u, v})
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := Index.{u, v})
private abbrev cone := OriginalICone.cone (B := B) (I := Index.{u, v})
private abbrev ι := OriginalICone.inclusion (B := B) (I := Index.{u, v})
private abbrev c := OriginalISuspension.cocone (B := B) (I := Index.{u, v})
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := Index.{u, v})

/-- The strict chosen cofiber uses the unchanged original I-cone on every original raw arrow. -/
abbrev strictCofiberFunctor : Arrow Carrier.{u, v} ⥤ Carrier.{u, v} :=
  OrdinaryHoChosenPuppe.cofiberFunctor cone ι c hc

/-- The actual raw strict target leg is typed at its entire original chosen cofiber object. -/
def strictCofiberTargetLeg (F : Arrow Carrier.{u, v}) : F.right ⟶ strictCofiberFunctor.obj F :=
  (c F).inr

/-- The actual raw strict cone leg retains its original I-cone source. -/
def strictCofiberConeLeg (F : Arrow Carrier.{u, v}) :
    cone.obj F.left ⟶ strictCofiberFunctor.obj F := (c F).inl

/-- The original replacement counit is retained on both components of the complete raw arrow. -/
def qArrowCounit (F : Arrow Carrier.{u, v}) : Q.mapArrow.obj F ⟶ F :=
  Arrow.homMk (ε.app F.left) (ε.app F.right) (ε.naturality F.hom).symm

/-- The original left component of the entire Q counit square is unchanged. -/
theorem qArrowCounit_left (F : Arrow Carrier.{u, v}) :
    (qArrowCounit F).left = ε.app F.left := rfl

/-- The original right component of the entire Q counit square is unchanged. -/
theorem qArrowCounit_right (F : Arrow Carrier.{u, v}) :
    (qArrowCounit F).right = ε.app F.right := rfl

/-- The entire original Q/counit arrow square is natural on both original components. -/
def qArrowCounitNatTrans : Q.mapArrow ⟶ 𝟭 (Arrow Carrier.{u, v}) where
  app F := qArrowCounit F
  naturality _ _ m := by
    apply Arrow.hom_ext
    · exact ε.naturality m.left
    · exact ε.naturality m.right

/-- The actual strict cofiber comparison is the full original Q-counit cofiber map. -/
def strictCofiberCounit (F : Arrow Carrier.{u, v}) :
    cofiber.obj F ⟶ strictCofiberFunctor.obj F := strictCofiberFunctor.map (qArrowCounit F)

/-- The full cofiber counit preserves the original left I-cone and counit map. -/
theorem strictCofiberCounit_cone (F : Arrow Carrier.{u, v}) :
    cofiberConeLeg F ≫ strictCofiberCounit F =
      cone.map (ε.app F.left) ≫ strictCofiberConeLeg F :=
  OrdinaryHoChosenPuppe.cofiberMap_cone cone ι c hc (qArrowCounit F)

/-- The full cofiber counit preserves the original right counit and target inclusion. -/
theorem strictCofiberCounit_target (F : Arrow Carrier.{u, v}) :
    inclusion F ≫ strictCofiberCounit F = ε.app F.right ≫ strictCofiberTargetLeg F :=
  OrdinaryHoChosenPuppe.cofiberMap_target cone ι c hc (qArrowCounit F)

/-- The same actual cofiber counit is a natural family on the entire original Arrow category. -/
def strictCofiberCounitNatTrans : cofiber.{u, v} ⟶ strictCofiberFunctor where
  app F := strictCofiberCounit F
  naturality F G m := by
    change strictCofiberFunctor.map (Q.mapArrow.map m) ≫
        strictCofiberFunctor.map (qArrowCounit G) =
      strictCofiberFunctor.map (qArrowCounit F) ≫ strictCofiberFunctor.map m
    rw [← strictCofiberFunctor.map_comp, ← strictCofiberFunctor.map_comp]
    exact strictCofiberFunctor.congr_map (qArrowCounitNatTrans.naturality m)

private theorem coneCollapse_weak (X : Carrier.{u, v}) :
    weakEquivalences Carrier (OrdinaryHoChosenPuppe.toZero
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (cone.obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration (B := B) X).2

/-- The strict cofiber counit is actually level weak between cofibrant original endpoints. -/
theorem strictCofiberCounit_weak (F : Arrow Carrier.{u, v})
    [IsCofibrant F.left] [IsCofibrant F.right] :
    weakEquivalences Carrier (strictCofiberCounit F) := by
  let _ : IsCofibrant (Q.mapArrow.obj F).left := by
    change IsCofibrant (Q.obj F.left)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.left
  let _ : IsCofibrant (Q.mapArrow.obj F).right := by
    change IsCofibrant (Q.obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : Cofibration (ι.app (Q.mapArrow.obj F).left) := by
    change Cofibration (ι.app (Q.obj F.left))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj F.left))
  let _ : Cofibration (ι.app F.left) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration F.left)
  let _ : WeakEquivalence (qArrowCounit F).left :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) F.left)
  let _ : WeakEquivalence (qArrowCounit F).right :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) F.right)
  exact OrdinaryHoChosenFiberCofiberComparison.chosenCofiberMap_weak
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone ι c hc (qArrowCounit F)
    (coneCollapse_weak (Q.obj F.left)) (coneCollapse_weak F.left)

/-- The original Q-cofiber target inclusion is a genuine native cofibration. -/
theorem inclusion_cofibration (F : Arrow Carrier.{u, v}) : Cofibration (inclusion F) := by
  let _ : Cofibration (ι.app (Q.mapArrow.obj F).left) := by
    change Cofibration (ι.app (Q.obj F.left))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj F.left))
  exact OrdinaryHoChosenPuppe.cofiberTarget_cofibration cone ι c hc (Q.mapArrow.obj F)

/-- Every original Q cofiber is genuinely cofibrant through its actual target inclusion. -/
theorem cofiber_obj_isCofibrant (F : Arrow Carrier.{u, v}) : IsCofibrant (cofiber.obj F) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ := inclusion_cofibration F
  exact isCofibrant_of_cofibration (inclusion F)

/-- The actual next source arrow is the same original Q-target inclusion into the same cofiber. -/
abbrev targetInclusionArrow (F : Arrow Carrier.{u, v}) : Arrow Carrier.{u, v} :=
  Arrow.mk (inclusion F)

/-- Every original square acts on both complete components of the original target inclusion. -/
def targetInclusionFunctor : Arrow Carrier.{u, v} ⥤ Arrow Carrier.{u, v} :=
  Q.mapArrow ⋙ OrdinaryHoChosenPuppeRotation.targetArrowFunctor cone ι c hc

/-- The complete next source is the original chosen target inclusion, as an entire arrow. -/
theorem targetInclusionFunctor_obj (F : Arrow Carrier.{u, v}) :
    targetInclusionFunctor.obj F = targetInclusionArrow F := rfl

/-- The actual next cofiber uses the same strict chosen cocones on the complete target arrow. -/
abbrev strictNextCofiberFunctor : Arrow Carrier.{u, v} ⥤ Carrier.{u, v} :=
  targetInclusionFunctor ⋙ strictCofiberFunctor

/-- Actual rotation collapses the original target cone to the unchanged I-Q suspension. -/
def rotationComparison (F : Arrow Carrier.{u, v}) :
    strictNextCofiberFunctor.obj F ⟶ originalISuspensionQFunctor.obj F.left :=
  OrdinaryHoChosenPuppeRotation.rotationComparison cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)

/-- The complete rotation cofiber leg is the same entire original chosen boundary. -/
theorem rotationComparison_cofiber (F : Arrow Carrier.{u, v}) :
    strictCofiberTargetLeg (targetInclusionArrow F) ≫ rotationComparison F = boundary F :=
  OrdinaryHoChosenPuppeRotation.rotationComparison_cofiber cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)

/-- The complete original rotation comparison is weak by actual cofibrant pushout gluing. -/
theorem rotationComparison_weak (F : Arrow Carrier.{u, v}) :
    weakEquivalences Carrier (rotationComparison F) := by
  let _ : IsCofibrant (Q.mapArrow.obj F).right := by
    change IsCofibrant (Q.obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : Cofibration (ι.app (Q.mapArrow.obj F).left) := by
    change Cofibration (ι.app (Q.obj F.left))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj F.left))
  let _ : Cofibration (ι.app (Q.mapArrow.obj F).right) := by
    change Cofibration (ι.app (Q.obj F.right))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj F.right))
  exact OrdinaryHoChosenPuppeRotation.rotationComparison_weak cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)
    (coneCollapse_weak (Q.obj F.right))

/-- Both full original Arrow components retain the complete natural rotation square. -/
def rotationComparisonNatTrans : strictNextCofiberFunctor.{u, v} ⟶
    Arrow.leftFunc ⋙ originalISuspensionQFunctor where
  app F := rotationComparison F
  naturality _ _ m := OrdinaryHoChosenPuppeRotation.rotationComparison_naturality
    cone ι c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.map m)

/-- The original next Q-cofiber uses the same actual inclusion arrow on every source square. -/
abbrev nextQCofiberFunctor : Arrow Carrier.{u, v} ⥤ Carrier.{u, v} :=
  targetInclusionFunctor ⋙ cofiber

/-- The next Q-cofiber reaches I-Q suspension by the same counit and original weak rotation. -/
def rotationQComparison (F : Arrow Carrier.{u, v}) :
    nextQCofiberFunctor.obj F ⟶ originalISuspensionQFunctor.obj F.left :=
  strictCofiberCounit (targetInclusionArrow F) ≫ rotationComparison F

/-- The entire rotation-Q comparison uses the original natural counit and original rotation. -/
def rotationQComparisonNatTrans : nextQCofiberFunctor.{u, v} ⟶
    Arrow.leftFunc ⋙ originalISuspensionQFunctor :=
  Functor.whiskerLeft targetInclusionFunctor strictCofiberCounitNatTrans ≫
    rotationComparisonNatTrans

/-- The actual natural comparison component is the complete same original two-map word. -/
theorem rotationQComparisonNatTrans_app (F : Arrow Carrier.{u, v}) :
    rotationQComparisonNatTrans.app F = rotationQComparison F := rfl

/-- Every raw source arrow has a genuinely weak next-Q-cofiber rotation comparison. -/
theorem rotationQComparison_weak (F : Arrow Carrier.{u, v}) :
    weakEquivalences Carrier (rotationQComparison F) := by
  let _ : IsCofibrant (targetInclusionArrow F).left := by
    change IsCofibrant (Q.obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : IsCofibrant (targetInclusionArrow F).right := by
    change IsCofibrant (cofiber.obj F)
    exact cofiber_obj_isCofibrant F
  exact (weakEquivalences Carrier).comp_mem _ _
    (strictCofiberCounit_weak (targetInclusionArrow F)) (rotationComparison_weak F)

/-- Both original integer comparison functions arise from the actual level-weak rotation word. -/
def rotationQIntegerIso (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (integerStablePiFunctor q).obj (nextQCofiberFunctor.obj F) ≅
      (integerStablePiFunctor q).obj (originalISuspensionQFunctor.obj F.left) :=
  integerStablePiLevelWeakIso q (rotationQComparison F) (rotationQComparison_weak F)

/-- The entire forward integer function is the same actual counit/rotation quotient map. -/
theorem rotationQIntegerIso_hom (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (rotationQIntegerIso q F).hom = (integerStablePiFunctor q).map (rotationQComparison F) :=
  integerStablePiLevelWeakIso_hom q (rotationQComparison F) (rotationQComparison_weak F)

/-- Every original whole Arrow retains both integer rotation comparison functions naturally. -/
def rotationQIntegerNatIso (q : ℤ) : nextQCofiberFunctor.{u, v} ⋙ integerStablePiFunctor q ≅
    (Arrow.leftFunc ⋙ originalISuspensionQFunctor) ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (rotationQIntegerIso q) (by
    intro F G m
    rw [rotationQIntegerIso_hom, rotationQIntegerIso_hom]
    exact (Functor.whiskerRight rotationQComparisonNatTrans
      (integerStablePiFunctor q)).naturality m)

/-- The complete rotation-Iso family has its original actual counit/rotation forward word. -/
theorem rotationQIntegerNatIso_hom (q : ℤ) :
    (rotationQIntegerNatIso.{u, v} q).hom =
      Functor.whiskerRight rotationQComparisonNatTrans (integerStablePiFunctor q) := by
  apply NatTrans.ext
  funext F
  exact rotationQIntegerIso_hom q F

/-- The entire original next-cofiber target inclusion maps to the unchanged original boundary. -/
theorem rotationQ_inclusionHo (F : Arrow Carrier.{u, v}) :
    inclusionHo (targetInclusionArrow F) ≫ H.map (rotationQComparison F) =
      H.map (boundary F) := by
  let J := targetInclusionArrow F
  calc
    _ = (qCounitHoIso J.right).inv ≫
        H.map (inclusion J ≫ strictCofiberCounit J) ≫ H.map (rotationComparison F) := by
      rw [inclusionHo, rotationQComparison, H.map_comp, H.map_comp]
      simp only [J, Category.assoc]
    _ = (qCounitHoIso J.right).inv ≫ H.map (ε.app J.right) ≫
        H.map (strictCofiberTargetLeg J) ≫ H.map (rotationComparison F) := by
      rw [strictCofiberCounit_target, H.map_comp]
      simp only [Category.assoc]
    _ = H.map (strictCofiberTargetLeg J) ≫ H.map (rotationComparison F) := by
      change (qCounitHoIso J.right).inv ≫
        ((qCounitHoIso J.right).hom ≫ H.map (strictCofiberTargetLeg J) ≫
          H.map (rotationComparison F)) = _
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = H.map (boundary F) := by
      rw [← H.map_comp, rotationComparison_cofiber]

/-- Every original integer degree retains the exact same Q/inclusion-to-boundary function. -/
theorem rotationQ_inclusionInteger (q : ℤ) (F : Arrow Carrier.{u, v}) :
    inclusionInteger q (targetInclusionArrow F) ≫
        (integerStablePiHoFunctor q).map (H.map (rotationQComparison F)) =
      (integerStablePiHoFunctor q).map (H.map (boundary F)) := by
  rw [inclusionInteger, ← Functor.map_comp, rotationQ_inclusionHo]

/-- The actual rotation word identifies every original inclusion class with its boundary class. -/
theorem rotationQ_inclusionInteger_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiHoFunctor q).obj (H.obj (cofiber.obj F))) :
    ((integerStablePiHoFunctor q).map (H.map (rotationQComparison F))).hom
        ((inclusionInteger q (targetInclusionArrow F)).hom a) =
      ((integerStablePiHoFunctor q).map (H.map (boundary F))).hom a :=
  ConcreteCategory.congr_hom (rotationQ_inclusionInteger q F) a

/-- Both Ho comparison functions of the actual rotation word
come from its proved native weakness. -/
def rotationQHoIso (F : Arrow Carrier.{u, v}) :
    H.obj (nextQCofiberFunctor.obj F) ≅ H.obj (originalISuspensionQFunctor.obj F.left) :=
  Localization.Construction.wIso (rotationQComparison F) (rotationQComparison_weak F)

/-- The actual projected integer Iso is the same original level-weak rotation Iso. -/
theorem rotationQHoIso_integerIso (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (integerStablePiHoFunctor q).mapIso (rotationQHoIso F) = rotationQIntegerIso q F := by
  apply Iso.ext
  change (integerStablePiHoFunctor q).map (H.map (rotationQComparison F)) =
    (rotationQIntegerIso q F).hom
  rw [integerStablePiHoFunctor_map, rotationQIntegerIso_hom]

/-- The native I-Q reversal is built from the two actual weak double-cone collapses. -/
def suspensionReversalQ (X : Carrier.{u, v}) :
    H.obj (originalISuspensionQFunctor.obj X) ≅ H.obj (originalISuspensionQFunctor.obj X) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  let _ : Cofibration (ι.app (Q.obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj X))
  exact OrdinaryHoChosenPuppeRotation.suspensionReversal cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.obj X) (coneCollapse_weak (Q.obj X))

/-- Every full original source arrow retains the actual two-collapse reversal square. -/
theorem suspensionReversalQ_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    H.map (originalISuspensionQFunctor.map f) ≫ (suspensionReversalQ Y).hom =
      (suspensionReversalQ X).hom ≫ H.map (originalISuspensionQFunctor.map f) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) Y
  let _ : Cofibration (ι.app (Q.obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj X))
  let _ : Cofibration (ι.app (Q.obj Y)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj Y))
  exact OrdinaryHoChosenPuppeRotation.suspensionReversal_naturality
    cone ι c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.map f)
    (coneCollapse_weak (Q.obj X)) (coneCollapse_weak (Q.obj Y))

/-- The full actual reversal is a natural automorphism of original I-Q suspension in Ho. -/
def suspensionReversalQNatIso :
    originalISuspensionQFunctor.{u, v} ⋙ H ≅ originalISuspensionQFunctor ⋙ H :=
  NatIso.ofComponents suspensionReversalQ (suspensionReversalQ_naturality)

/-- Each original integer group keeps the entire actual two-collapse reversal. -/
def reversalQIntegerNatIso (q : ℤ) :
    originalISuspensionQFunctor.{u, v} ⋙ integerStablePiFunctor q ≅
      originalISuspensionQFunctor ⋙ integerStablePiFunctor q :=
  (projectedIntegerClassNatIso originalISuspensionQFunctor q).symm ≪≫
    Functor.isoWhiskerRight suspensionReversalQNatIso (integerStablePiHoFunctor q) ≪≫
      projectedIntegerClassNatIso originalISuspensionQFunctor q

/-- The whole forward reversal function is the actual integer image of the original Ho reversal. -/
theorem reversalQIntegerNatIso_hom_app (q : ℤ) (X : Carrier.{u, v}) :
    (reversalQIntegerNatIso q).hom.app X =
      (integerStablePiHoFunctor q).map (suspensionReversalQ X).hom := by
  change 𝟙 _ ≫ (integerStablePiHoFunctor q).map (suspensionReversalQ X).hom ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- The whole inverse reversal function retains the same two original collapse inverses. -/
theorem reversalQIntegerNatIso_inv_app (q : ℤ) (X : Carrier.{u, v}) :
    (reversalQIntegerNatIso q).inv.app X =
      (integerStablePiHoFunctor q).map (suspensionReversalQ X).inv := by
  change 𝟙 _ ≫ (integerStablePiHoFunctor q).map (suspensionReversalQ X).inv ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- Original I suspension preserves the actual Q counit on every cofibrant source. -/
theorem originalSuspensionCounit_weak (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier (S.map (ε.app X)) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  let _ : IsCofibrant ((𝟭 Carrier).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : WeakEquivalence (ε.app X) := (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  let _ : Cofibration (ι.app (Q.obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj X))
  let _ : Cofibration (ι.app X) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  let _ : Cofibration (ι.app ((𝟭 Carrier).obj X)) := by
    change Cofibration (ι.app X)
    exact (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  exact OrdinaryHoChosenPuppeRotation.suspensionMap_weak_of_cofibrant
    cone ι c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (ε.app X)
    (coneCollapse_weak (Q.obj X)) (coneCollapse_weak X)

/-- The original I-Q counit on Q objects is weak for every original raw spectrum. -/
theorem suspensionQCounit_weak (X : Carrier.{u, v}) :
    weakEquivalences Carrier (S.map (ε.app (Q.obj X))) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  exact originalSuspensionCounit_weak (Q.obj X)

/-- The complete Q/I counit retains the same original source maps before both suspensions. -/
def suspensionQCounitNatTrans : Q ⋙ originalISuspensionQFunctor.{u, v} ⟶
    originalISuspensionQFunctor where
  app X := S.map (ε.app (Q.obj X))
  naturality X Y f := by
    change S.map (Q.map (Q.map f)) ≫ S.map (ε.app (Q.obj Y)) =
      S.map (ε.app (Q.obj X)) ≫ S.map (Q.map f)
    rw [← S.map_comp, ← S.map_comp]
    exact S.congr_map (ε.naturality (Q.map f))

/-- Actual level weakness gives both full original integer functions of the suspended Q counit. -/
def suspensionQCounitIntegerNatIso (q : ℤ) :
    (Q ⋙ originalISuspensionQFunctor.{u, v}) ⋙ integerStablePiFunctor q ≅
      originalISuspensionQFunctor ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents
    (fun X => integerStablePiLevelWeakIso q (S.map (ε.app (Q.obj X)))
      (suspensionQCounit_weak X)) (by
        intro X Y f
        rw [integerStablePiLevelWeakIso_hom, integerStablePiLevelWeakIso_hom]
        exact (Functor.whiskerRight suspensionQCounitNatTrans
          (integerStablePiFunctor q)).naturality f)

/-- The forward suspended-Q counit is the same actual original integer quotient map. -/
theorem suspensionQCounitIntegerNatIso_hom_app (q : ℤ) (X : Carrier.{u, v}) :
    (suspensionQCounitIntegerNatIso q).hom.app X =
      (integerStablePiFunctor q).map (S.map (ε.app (Q.obj X))) :=
  integerStablePiLevelWeakIso_hom q (S.map (ε.app (Q.obj X))) (suspensionQCounit_weak X)

/-- Rotation's entire target correction retains reversal, suspended Q counit and both I-Q maps. -/
def rotationTargetCorrectionNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    Q ⋙ integerStablePiFunctor q :=
  integerISuspensionPiNatIso q ≪≫ reversalQIntegerNatIso (q + 1) ≪≫
    (suspensionQCounitIntegerNatIso (q + 1)).symm ≪≫
      Functor.associator Q originalISuspensionQFunctor (integerStablePiFunctor (q + 1)) ≪≫
        Functor.isoWhiskerLeft Q (integerISuspensionPiNatIso q).symm

/-- The complete correction's forward map keeps the actual signed original rotation word. -/
theorem rotationTargetCorrectionNatIso_hom (q : ℤ) :
    (rotationTargetCorrectionNatIso.{u, v} q).hom =
      (integerISuspensionPiNatIso q).hom ≫
        (reversalQIntegerNatIso (q + 1)).hom ≫
          (suspensionQCounitIntegerNatIso (q + 1)).inv ≫
            (Functor.associator Q originalISuspensionQFunctor
              (integerStablePiFunctor (q + 1))).hom ≫
                Functor.whiskerLeft Q (integerISuspensionPiNatIso q).inv := rfl

/-- The raw strict Puppe boundary uses the same original chosen cone and zero endpoints. -/
def strictBoundary (F : Arrow Carrier.{u, v}) :
    strictCofiberFunctor.obj F ⟶ S.obj F.left :=
  OrdinaryHoChosenPuppe.boundary cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero F

/-- Both original Q counit endpoints retain the entire strict-boundary square. -/
theorem strictCofiberCounit_boundary (F : Arrow Carrier.{u, v}) :
    strictCofiberCounit F ≫ strictBoundary F = boundary F ≫ S.map (ε.app F.left) :=
  OrdinaryHoChosenPuppe.boundary_naturality cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (qArrowCounit F)

/-- The strict next boundary has the unchanged original I-Q target of the original right object. -/
def relativeNextBoundary (F : Arrow Carrier.{u, v}) :
    strictNextCofiberFunctor.obj F ⟶ originalISuspensionQFunctor.obj F.right :=
  strictBoundary (targetInclusionArrow F)

/-- The actual next Puppe boundary keeps the complete original suspension reversal. -/
theorem rotationComparison_boundary (F : Arrow Carrier.{u, v}) :
    H.map (rotationComparison F) ≫ H.map (originalISuspensionQFunctor.map F.hom) ≫
        (suspensionReversalQ F.right).hom = H.map (relativeNextBoundary F) := by
  let _ : IsCofibrant (Q.mapArrow.obj F).right := by
    change IsCofibrant (Q.obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : Cofibration (ι.app (Q.mapArrow.obj F).right) := by
    change Cofibration (ι.app (Q.obj F.right))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration (Q.obj F.right))
  exact OrdinaryHoChosenPuppeRotation.rotationComparison_boundary cone ι c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)
    (coneCollapse_weak (Q.obj F.right))

/-- The next-Q boundary retains reversal and the original suspended Q counit on the right. -/
theorem rotationQComparison_boundary (F : Arrow Carrier.{u, v}) :
    H.map (rotationQComparison F) ≫ H.map (originalISuspensionQFunctor.map F.hom) ≫
        (suspensionReversalQ F.right).hom =
      H.map (boundary (targetInclusionArrow F)) ≫ H.map (S.map (ε.app (Q.obj F.right))) := by
  rw [rotationQComparison, H.map_comp, Category.assoc, rotationComparison_boundary]
  change H.map (strictCofiberCounit (targetInclusionArrow F)) ≫
      H.map (strictBoundary (targetInclusionArrow F)) =
    H.map (boundary (targetInclusionArrow F)) ≫
      H.map (S.map (ε.app (targetInclusionArrow F).left))
  rw [← H.map_comp, strictCofiberCounit_boundary, H.map_comp]

/-- Every original integer class retains the full signed next-Q boundary and suspended counit. -/
theorem rotationQInteger_boundary (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (rotationQIntegerIso q F).hom ≫
        (integerStablePiFunctor q).map (originalISuspensionQFunctor.map F.hom) ≫
          (reversalQIntegerNatIso q).hom.app F.right =
      (integerStablePiFunctor q).map (boundary (targetInclusionArrow F)) ≫
        (suspensionQCounitIntegerNatIso q).hom.app F.right := by
  have h := (integerStablePiHoFunctor q).congr_map (rotationQComparison_boundary F)
  simp only [Functor.map_comp, integerStablePiHoFunctor_map] at h
  rw [← rotationQIntegerIso_hom, ← reversalQIntegerNatIso_hom_app,
    ← suspensionQCounitIntegerNatIso_hom_app] at h
  exact h

/-- The target correction after original desuspension retains actual reversal and both counit
maps. -/
theorem rotationTargetCorrectionNatIso_after_inverse (q : ℤ) :
    (integerISuspensionPiNatIso.{u, v} q).inv ≫
        (rotationTargetCorrectionNatIso q).hom =
      (reversalQIntegerNatIso (q + 1)).hom ≫
        (suspensionQCounitIntegerNatIso (q + 1)).inv ≫
          (Functor.associator Q originalISuspensionQFunctor
            (integerStablePiFunctor (q + 1))).hom ≫
              Functor.whiskerLeft Q (integerISuspensionPiNatIso q).inv := by
  rw [rotationTargetCorrectionNatIso_hom]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual rotation comparison is desuspended by the complete original all-integer I-Q map. -/
def rotationSourceDesuspensionNatTrans (q : ℤ) :
    nextQCofiberFunctor.{u, v} ⋙ integerStablePiFunctor (q + 1) ⟶
      Arrow.leftFunc ⋙ integerStablePiFunctor q :=
  (rotationQIntegerNatIso (q + 1)).hom ≫
    (Functor.associator Arrow.leftFunc originalISuspensionQFunctor
      (integerStablePiFunctor (q + 1))).hom ≫
        Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso q).inv

/-- Each original rotation-desuspension class retains its complete weak-Q rotation and I-Q
inverse. -/
def rotationSourceDesuspension (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F ⟶
      (integerStablePiFunctor q).obj F.left :=
  (rotationSourceDesuspensionNatTrans q).app F

/-- The full rotation-desuspension function is the same original two integer functions. -/
theorem rotationSourceDesuspension_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F) :
    (rotationSourceDesuspension q F).hom a =
      ((integerISuspensionPiNatIso q).inv.app F.left).hom
        ((rotationQIntegerIso (q + 1) F).hom.hom a) := by
  dsimp only [rotationSourceDesuspension, rotationSourceDesuspensionNatTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator, rotationQIntegerNatIso]
  rfl

/-- The actual next inclusion boundary is a complete original integer natural family. -/
def nextConnectingPlusOneNatTrans (q : ℤ) :
    nextQCofiberFunctor.{u, v} ⋙ integerStablePiFunctor (q + 1) ⟶
      Arrow.rightFunc ⋙ (Q ⋙ integerStablePiFunctor q) where
  app F := connectingPlusOne q (targetInclusionArrow F)
  naturality _ _ m := connectingPlusOne_naturality q (targetInclusionFunctor.map m)

/-- Every actual next boundary class retains its exact original chosen-boundary connecting
function. -/
def nextConnectingPlusOne (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F ⟶
      (Q ⋙ integerStablePiFunctor q).obj F.right :=
  (nextConnectingPlusOneNatTrans q).app F

/-- The next actual connecting map retains the complete original rotation target correction. -/
theorem nextConnectingPlusOne_correction_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F) :
    (nextConnectingPlusOne q F).hom a =
      ((rotationTargetCorrectionNatIso q).hom.app F.right).hom
        (((integerStablePiFunctor q).map F.hom).hom
          ((rotationSourceDesuspension q F).hom a)) := by
  let b := (rotationQIntegerIso (q + 1) F).hom.hom a
  let d := ((integerStablePiFunctor (q + 1)).map
    (originalISuspensionQFunctor.map F.hom)).hom b
  have hn := ConcreteCategory.congr_hom
    (integerISuspensionPiNatIso_inv_naturality q F.hom) b
  change ((integerISuspensionPiNatIso q).inv.app F.right).hom d =
    ((integerStablePiFunctor q).map F.hom).hom
      (((integerISuspensionPiNatIso q).inv.app F.left).hom b) at hn
  have hc := ConcreteCategory.congr_hom
    (congr_app (rotationTargetCorrectionNatIso_after_inverse q) F.right) d
  change ((rotationTargetCorrectionNatIso q).hom.app F.right).hom
      (((integerISuspensionPiNatIso q).inv.app F.right).hom d) =
    ((integerISuspensionPiNatIso q).inv.app (Q.obj F.right)).hom
      (((suspensionQCounitIntegerNatIso (q + 1)).inv.app F.right).hom
        (((reversalQIntegerNatIso (q + 1)).hom.app F.right).hom d)) at hc
  have hr := ConcreteCategory.congr_hom (rotationQInteger_boundary (q + 1) F) a
  change ((reversalQIntegerNatIso (q + 1)).hom.app F.right).hom d =
    ((suspensionQCounitIntegerNatIso (q + 1)).hom.app F.right).hom
      (((integerStablePiFunctor (q + 1)).map
        (boundary (targetInclusionArrow F))).hom a) at hr
  have ht := ConcreteCategory.congr_hom
    ((suspensionQCounitIntegerNatIso (q + 1)).app F.right).hom_inv_id
      (((integerStablePiFunctor (q + 1)).map (boundary (targetInclusionArrow F))).hom a)
  change ((suspensionQCounitIntegerNatIso (q + 1)).inv.app F.right).hom
      (((suspensionQCounitIntegerNatIso (q + 1)).hom.app F.right).hom
        (((integerStablePiFunctor (q + 1)).map
          (boundary (targetInclusionArrow F))).hom a)) =
    ((integerStablePiFunctor (q + 1)).map (boundary (targetInclusionArrow F))).hom a at ht
  rw [rotationSourceDesuspension_apply]
  change (connectingPlusOne q (targetInclusionArrow F)).hom a =
    ((rotationTargetCorrectionNatIso q).hom.app F.right).hom
      (((integerStablePiFunctor q).map F.hom).hom
        (((integerISuspensionPiNatIso q).inv.app F.left).hom b))
  rw [← hn, hc, hr, ht, connectingPlusOne_apply]
  rfl

/-- The entire rotation/desuspension comparison is an actual original integer Iso. -/
def rotationSourceDesuspensionIso (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F ≅
      (integerStablePiFunctor q).obj F.left :=
  rotationQIntegerIso (q + 1) F ≪≫ ((integerISuspensionPiNatIso q).app F.left).symm

/-- Both inverse directions retain the same original weak-rotation and I-Q functions. -/
theorem rotationSourceDesuspensionIso_hom (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (rotationSourceDesuspensionIso q F).hom = rotationSourceDesuspension q F := by
  apply GrpCat.hom_ext
  ext a
  exact (rotationSourceDesuspension_apply q F a).symm

/-- The actual next target inclusion maps to the same entire original connecting class. -/
theorem rotationSourceDesuspension_inclusion_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F)) :
    (rotationSourceDesuspension q F).hom
        (((inclusionIntegerNatTrans (q + 1)).app (targetInclusionArrow F)).hom a) =
      (connectingPlusOne q F).hom a := by
  have h := rotationQ_inclusionInteger (q + 1) F
  rw [inclusionInteger_formula, qCounitHoIso_integer_inverse] at h
  rw [integerStablePiHoFunctor_map, integerStablePiHoFunctor_map,
    ← rotationQIntegerIso_hom] at h
  have h' := ConcreteCategory.congr_hom h a
  rw [rotationSourceDesuspension_apply, inclusionIntegerNatTrans_app,
    inclusionInteger_formula, qCounitHoIso_integer_inverse, connectingPlusOne_apply]
  exact congrArg ((integerISuspensionPiNatIso q).inv.app F.left).hom h'

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberRotationIntegerPiGeometry
