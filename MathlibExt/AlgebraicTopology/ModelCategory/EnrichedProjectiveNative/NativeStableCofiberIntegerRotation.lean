/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerMaps
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison

/-!
# Integer homotopy maps for cofiber rotation

Compares iterated chosen cofibers with the I-suspension of the cofibrant replacement. Rotation, suspension reversal and counit corrections induce natural isomorphisms on integer homotopy groups, with formulas for the cofiber boundary and connecting maps. The strict cofiber counit is level weak when both original endpoints are cofibrant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerMaps
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I}

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev C := (Carrier.{u, v} (I := I))
private abbrev Index := I
private abbrev H := toHomotopyCategory (Carrier.{u, v} (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev cone := OriginalICone.cone (B := B) (I := I)
private abbrev ι := OriginalICone.inclusion (B := B) (I := I)
private abbrev c := OriginalISuspension.cocone (B := B) (I := I)
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := I)
private abbrev CQ := CofiberNullity.cofiberQ (B := B) (I := I)

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerRotation

/-- The strict chosen cofiber uses the unchanged original I-cone on every original raw arrow. -/
abbrev strictCofiberFunctor : Arrow (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) :=
  OrdinaryHoChosenPuppe.cofiberFunctor (cone (I := I)) (ι (I := I)) c hc

/-- The actual raw strict target leg is typed at its entire original chosen cofiber object. -/
def strictCofiberTargetLeg (F : Arrow (Carrier.{u, v} (I := I))) : F.right ⟶
  strictCofiberFunctor.obj F :=
  (c F).inr

/-- The actual raw strict cone leg retains its original I-cone source. -/
def strictCofiberConeLeg (F : Arrow (Carrier.{u, v} (I := I))) :
    (cone (I := I)).obj F.left ⟶ strictCofiberFunctor.obj F := (c F).inl

/-- The original replacement counit is retained on both components of the complete raw arrow. -/
def qArrowCounit (F : Arrow (Carrier.{u, v} (I := I))) : (Q (I := I)).mapArrow.obj F ⟶ F :=
  Arrow.homMk ((ε (I := I)).app F.left) ((ε (I := I)).app F.right) ((ε (I := I)).naturality
    F.hom).symm

/-- The original left component of the entire Q counit square is unchanged. -/
theorem qArrowCounit_left (F : Arrow (Carrier.{u, v} (I := I))) :
    (qArrowCounit F).left = (ε (I := I)).app F.left := rfl

/-- The original right component of the entire Q counit square is unchanged. -/
theorem qArrowCounit_right (F : Arrow (Carrier.{u, v} (I := I))) :
    (qArrowCounit F).right = (ε (I := I)).app F.right := rfl

/-- The entire original Q/counit arrow square is natural on both original components. -/
def qArrowCounitNatTrans : (Q (I := I)).mapArrow ⟶ 𝟭 (Arrow (Carrier.{u, v} (I := I))) where
  app F := qArrowCounit F
  naturality _ _ m := by
    apply Arrow.hom_ext
    · exact (ε (I := I)).naturality m.left
    · exact (ε (I := I)).naturality m.right

/-- The actual strict cofiber comparison is the full original Q-counit cofiber map. -/
def strictCofiberCounit (F : Arrow (Carrier.{u, v} (I := I))) :
    (cofiber (I := I)).obj F ⟶ strictCofiberFunctor.obj F := strictCofiberFunctor.map
      (qArrowCounit F)

/-- The full cofiber counit preserves the original left I-cone and counit map. -/
theorem strictCofiberCounit_cone (F : Arrow (Carrier.{u, v} (I := I))) :
    cofiberConeLeg F ≫ strictCofiberCounit F =
      (cone (I := I)).map ((ε (I := I)).app F.left) ≫ strictCofiberConeLeg F :=
  OrdinaryHoChosenPuppe.cofiberMap_cone (cone (I := I)) (ι (I := I)) c hc (qArrowCounit F)

/-- The full cofiber counit preserves the original right counit and target inclusion. -/
theorem strictCofiberCounit_target (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusion F ≫ strictCofiberCounit F = (ε (I := I)).app F.right ≫ strictCofiberTargetLeg F :=
  OrdinaryHoChosenPuppe.cofiberMap_target (cone (I := I)) (ι (I := I)) c hc (qArrowCounit F)

/-- The same actual cofiber counit is a natural family on the entire original Arrow category. -/
def strictCofiberCounitNatTrans : (cofiber.{u, v} (I := I)) ⟶ strictCofiberFunctor where
  app F := strictCofiberCounit F
  naturality F G m := by
    change strictCofiberFunctor.map ((Q (I := I)).mapArrow.map m) ≫
        strictCofiberFunctor.map (qArrowCounit G) =
      strictCofiberFunctor.map (qArrowCounit F) ≫ strictCofiberFunctor.map m
    rw [← strictCofiberFunctor.map_comp, ← strictCofiberFunctor.map_comp]
    exact strictCofiberFunctor.congr_map (qArrowCounitNatTrans.naturality m)

private theorem coneCollapse_weak (X : (Carrier.{u, v} (I := I))) :
    weakEquivalences (Carrier (I := I)) (OrdinaryHoChosenPuppe.toZero
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((cone (I := I)).obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone (I := I)).obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration (B := B) X).2

/-- The strict cofiber counit is actually level weak between cofibrant original endpoints. -/
theorem strictCofiberCounit_weak (F : Arrow (Carrier.{u, v} (I := I)))
    [IsCofibrant F.left] [IsCofibrant F.right] :
    weakEquivalences (Carrier (I := I)) (strictCofiberCounit F) := by
  let _ : IsCofibrant ((Q (I := I)).mapArrow.obj F).left := by
    change IsCofibrant ((Q (I := I)).obj F.left)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.left
  let _ : IsCofibrant ((Q (I := I)).mapArrow.obj F).right := by
    change IsCofibrant ((Q (I := I)).obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).mapArrow.obj F).left) := by
    change Cofibration ((ι (I := I)).app ((Q (I := I)).obj F.left))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj F.left))
  let _ : Cofibration ((ι (I := I)).app F.left) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration F.left)
  let _ : WeakEquivalence (qArrowCounit F).left :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) F.left)
  let _ : WeakEquivalence (qArrowCounit F).right :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) F.right)
  exact OrdinaryHoChosenFiberCofiberComparison.chosenCofiberMap_weak
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (cone (I := I)) (ι (I := I)) c hc
      (qArrowCounit F)
    (coneCollapse_weak ((Q (I := I)).obj F.left)) (coneCollapse_weak F.left)

/-- The original Q-cofiber target inclusion is a genuine native cofibration. -/
theorem inclusion_cofibration (F : Arrow (Carrier.{u, v} (I := I))) : Cofibration (inclusion F) :=
  by
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).mapArrow.obj F).left) := by
    change Cofibration ((ι (I := I)).app ((Q (I := I)).obj F.left))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj F.left))
  exact OrdinaryHoChosenPuppe.cofiberTarget_cofibration (cone (I := I)) (ι (I := I)) c hc ((Q (I
    := I)).mapArrow.obj F)

/-- Every original Q cofiber is genuinely cofibrant through its actual target inclusion. -/
theorem cofiber_obj_isCofibrant (F : Arrow (Carrier.{u, v} (I := I))) : IsCofibrant ((cofiber (I
  := I)).obj F) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ := inclusion_cofibration F
  exact isCofibrant_of_cofibration (inclusion F)

/-- The actual next source arrow is the same original Q-target inclusion into the same cofiber. -/
abbrev targetInclusionArrow (F : Arrow (Carrier.{u, v} (I := I))) : Arrow (Carrier.{u, v} (I :=
  I)) :=
  Arrow.mk (inclusion F)

/-- Every original square acts on both complete components of the original target inclusion. -/
def targetInclusionFunctor : Arrow (Carrier.{u, v} (I := I)) ⥤ Arrow (Carrier.{u, v} (I := I)) :=
  (Q (I := I)).mapArrow ⋙ OrdinaryHoChosenPuppeRotation.targetArrowFunctor (cone (I := I)) (ι (I
    := I)) c hc

/-- The complete next source is the original chosen target inclusion, as an entire arrow. -/
theorem targetInclusionFunctor_obj (F : Arrow (Carrier.{u, v} (I := I))) :
    targetInclusionFunctor.obj F = targetInclusionArrow F := rfl

/-- The actual next cofiber uses the same strict chosen cocones on the complete target arrow. -/
abbrev strictNextCofiberFunctor : Arrow (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) :=
  targetInclusionFunctor ⋙ strictCofiberFunctor

/-- Actual rotation collapses the original target cone to the unchanged I-Q suspension. -/
def rotationComparison (F : Arrow (Carrier.{u, v} (I := I))) :
    strictNextCofiberFunctor.obj F ⟶ (originalISuspensionQFunctor (I := I)).obj F.left :=
  OrdinaryHoChosenPuppeRotation.rotationComparison (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)

/-- The complete rotation cofiber leg is the same entire original chosen boundary. -/
theorem rotationComparison_cofiber (F : Arrow (Carrier.{u, v} (I := I))) :
    strictCofiberTargetLeg (targetInclusionArrow F) ≫ rotationComparison F = boundary F :=
  OrdinaryHoChosenPuppeRotation.rotationComparison_cofiber (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)

/-- The complete original rotation comparison is weak by actual cofibrant pushout gluing. -/
theorem rotationComparison_weak (F : Arrow (Carrier.{u, v} (I := I))) :
    weakEquivalences (Carrier (I := I)) (rotationComparison F) := by
  let _ : IsCofibrant ((Q (I := I)).mapArrow.obj F).right := by
    change IsCofibrant ((Q (I := I)).obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).mapArrow.obj F).left) := by
    change Cofibration ((ι (I := I)).app ((Q (I := I)).obj F.left))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj F.left))
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).mapArrow.obj F).right) := by
    change Cofibration ((ι (I := I)).app ((Q (I := I)).obj F.right))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj F.right))
  exact OrdinaryHoChosenPuppeRotation.rotationComparison_weak (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)
    (coneCollapse_weak ((Q (I := I)).obj F.right))

/-- Both full original Arrow components retain the complete natural rotation square. -/
def rotationComparisonNatTrans : strictNextCofiberFunctor.{u, v} ⟶
    Arrow.leftFunc ⋙ (originalISuspensionQFunctor (I := I)) where
  app F := rotationComparison F
  naturality _ _ m := OrdinaryHoChosenPuppeRotation.rotationComparison_naturality
    (cone (I := I)) (ι (I := I)) c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I :=
      I)).mapArrow.map m)

/-- The original next Q-cofiber uses the same actual inclusion arrow on every source square. -/
abbrev nextQCofiberFunctor : Arrow (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) :=
  targetInclusionFunctor ⋙ (cofiber (I := I))

/-- The next Q-cofiber reaches I-Q suspension by the same counit and original weak rotation. -/
def rotationQComparison (F : Arrow (Carrier.{u, v} (I := I))) :
    nextQCofiberFunctor.obj F ⟶ (originalISuspensionQFunctor (I := I)).obj F.left :=
  strictCofiberCounit (targetInclusionArrow F) ≫ rotationComparison F

/-- The entire rotation-Q comparison uses the original natural counit and original rotation. -/
def rotationQComparisonNatTrans : nextQCofiberFunctor.{u, v} ⟶
    Arrow.leftFunc ⋙ (originalISuspensionQFunctor (I := I)) :=
  Functor.whiskerLeft targetInclusionFunctor strictCofiberCounitNatTrans ≫
    rotationComparisonNatTrans

/-- The actual natural comparison component is the complete same original two-map word. -/
theorem rotationQComparisonNatTrans_app (F : Arrow (Carrier.{u, v} (I := I))) :
    rotationQComparisonNatTrans.app F = rotationQComparison F := rfl

/-- Every raw source arrow has a genuinely weak next-Q-cofiber rotation comparison. -/
theorem rotationQComparison_weak (F : Arrow (Carrier.{u, v} (I := I))) :
    weakEquivalences (Carrier (I := I)) (rotationQComparison F) := by
  let _ : IsCofibrant (targetInclusionArrow F).left := by
    change IsCofibrant ((Q (I := I)).obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : IsCofibrant (targetInclusionArrow F).right := by
    change IsCofibrant ((cofiber (I := I)).obj F)
    exact cofiber_obj_isCofibrant F
  exact (weakEquivalences (Carrier (I := I))).comp_mem _ _
    (strictCofiberCounit_weak (targetInclusionArrow F)) (rotationComparison_weak F)

/-- Both original integer comparison functions arise from the actual level-weak rotation word. -/
def rotationQIntegerIso (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (integerPiFunctor j q).obj (nextQCofiberFunctor.obj F) ≅
      (integerPiFunctor j q).obj ((originalISuspensionQFunctor (I := I)).obj F.left) :=
  integerPiLevelWeakIso (j := j) q (rotationQComparison F) (rotationQComparison_weak F)

/-- The entire forward integer function is the same actual counit/rotation quotient map. -/
theorem rotationQIntegerIso_hom (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (rotationQIntegerIso (j := j) q F).hom = (integerPiFunctor j q).map (rotationQComparison F) :=
  integerPiLevelWeakIso_hom (j := j) q (rotationQComparison F) (rotationQComparison_weak F)

/-- Every original whole Arrow retains both integer rotation comparison functions naturally. -/
def rotationQIntegerNatIso (q : ℤ) : nextQCofiberFunctor.{u, v} ⋙ integerPiFunctor j q ≅
    (Arrow.leftFunc ⋙ (originalISuspensionQFunctor (I := I))) ⋙ integerPiFunctor j q :=
  NatIso.ofComponents (rotationQIntegerIso (j := j) q) (by
    intro F G m
    rw [rotationQIntegerIso_hom (j := j), rotationQIntegerIso_hom (j := j)]
    exact (Functor.whiskerRight rotationQComparisonNatTrans
      (integerPiFunctor j q)).naturality m)

/-- The complete rotation-Iso family has its original actual counit/rotation forward word. -/
theorem rotationQIntegerNatIso_hom (q : ℤ) :
    (rotationQIntegerNatIso.{u, v} (j := j) q).hom =
      Functor.whiskerRight rotationQComparisonNatTrans (integerPiFunctor j q) := by
  apply NatTrans.ext
  funext F
  exact rotationQIntegerIso_hom (j := j) q F

/-- The entire original next-cofiber target inclusion maps to the unchanged original boundary. -/
theorem rotationQ_inclusionHo (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusionHo (targetInclusionArrow F) ≫ (H (I := I)).map (rotationQComparison F) =
      (H (I := I)).map (boundary F) := by
  let J := targetInclusionArrow F
  calc
    _ = (qCounitHoIso J.right).inv ≫
        (H (I := I)).map (inclusion J ≫ strictCofiberCounit J) ≫ (H (I := I)).map
          (rotationComparison F) := by
      rw [inclusionHo, rotationQComparison, (H (I := I)).map_comp, (H (I := I)).map_comp]
      simp only [J, Category.assoc]
    _ = (qCounitHoIso J.right).inv ≫ (H (I := I)).map ((ε (I := I)).app J.right) ≫
        (H (I := I)).map (strictCofiberTargetLeg J) ≫ (H (I := I)).map (rotationComparison F) := by
      rw [strictCofiberCounit_target, (H (I := I)).map_comp]
      simp only [Category.assoc]
    _ = (H (I := I)).map (strictCofiberTargetLeg J) ≫ (H (I := I)).map (rotationComparison F) := by
      change (qCounitHoIso J.right).inv ≫
        ((qCounitHoIso J.right).hom ≫ (H (I := I)).map (strictCofiberTargetLeg J) ≫
          (H (I := I)).map (rotationComparison F)) = _
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (H (I := I)).map (boundary F) := by
      rw [← (H (I := I)).map_comp, rotationComparison_cofiber]

/-- Every original integer degree retains the exact same Q/inclusion-to-boundary function. -/
theorem rotationQ_inclusionInteger (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    inclusionInteger (j := j) q (targetInclusionArrow F) ≫
        (integerPiHoFunctor j q).map ((H (I := I)).map (rotationQComparison F)) =
      (integerPiHoFunctor j q).map ((H (I := I)).map (boundary F)) := by
  rw [inclusionInteger, ← Functor.map_comp, rotationQ_inclusionHo]

/-- The actual rotation word identifies every original inclusion class with its boundary class. -/
theorem rotationQ_inclusionInteger_apply (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiHoFunctor j q).obj ((H (I := I)).obj ((cofiber (I := I)).obj F))) :
    ((integerPiHoFunctor j q).map ((H (I := I)).map (rotationQComparison F))).hom
        ((inclusionInteger (j := j) q (targetInclusionArrow F)).hom a) =
      ((integerPiHoFunctor j q).map ((H (I := I)).map (boundary F))).hom a :=
  ConcreteCategory.congr_hom (rotationQ_inclusionInteger (j := j) q F) a

/-- Both Ho comparison functions of the actual rotation word
come from its proved native weakness. -/
def rotationQHoIso (F : Arrow (Carrier.{u, v} (I := I))) :
    (H (I := I)).obj (nextQCofiberFunctor.obj F) ≅ (H (I := I)).obj ((originalISuspensionQFunctor
      (I := I)).obj F.left) :=
  Localization.Construction.wIso (rotationQComparison F) (rotationQComparison_weak F)

/-- The actual projected integer Iso is the same original level-weak rotation Iso. -/
theorem rotationQHoIso_integerIso (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (integerPiHoFunctor j q).mapIso (rotationQHoIso F) = rotationQIntegerIso (j := j) q F := by
  apply Iso.ext
  change (integerPiHoFunctor j q).map ((H (I := I)).map (rotationQComparison F)) =
    (rotationQIntegerIso (j := j) q F).hom
  rw [integerPiHoFunctor_map (j := j), rotationQIntegerIso_hom (j := j)]

/-- The native I-Q reversal is built from the two actual weak double-cone collapses. -/
def suspensionReversalQ (X : (Carrier.{u, v} (I := I))) :
    (H (I := I)).obj ((originalISuspensionQFunctor (I := I)).obj X) ≅ (H (I := I)).obj
      ((originalISuspensionQFunctor (I := I)).obj X) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj X))
  exact OrdinaryHoChosenPuppeRotation.suspensionReversal (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).obj X) (coneCollapse_weak ((Q
      (I := I)).obj X))

/-- Every full original source arrow retains the actual two-collapse reversal square. -/
theorem suspensionReversalQ_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) :
    (H (I := I)).map ((originalISuspensionQFunctor (I := I)).map f) ≫ (suspensionReversalQ Y).hom =
      (suspensionReversalQ X).hom ≫ (H (I := I)).map ((originalISuspensionQFunctor (I := I)).map
        f) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) Y
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj X))
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).obj Y)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj Y))
  exact OrdinaryHoChosenPuppeRotation.suspensionReversal_naturality
    (cone (I := I)) (ι (I := I)) c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I :=
      I)).map f)
    (coneCollapse_weak ((Q (I := I)).obj X)) (coneCollapse_weak ((Q (I := I)).obj Y))

/-- The full actual reversal is a natural automorphism of original I-Q suspension in Ho. -/
def suspensionReversalQNatIso :
    (originalISuspensionQFunctor.{u, v} (I := I)) ⋙ (H (I := I)) ≅ (originalISuspensionQFunctor (I
      := I)) ⋙ (H (I := I)) :=
  NatIso.ofComponents suspensionReversalQ (suspensionReversalQ_naturality)

/-- Each original integer group keeps the entire actual two-collapse reversal. -/
def reversalQIntegerNatIso (q : ℤ) :
    (originalISuspensionQFunctor.{u, v} (I := I)) ⋙ integerPiFunctor j q ≅
      (originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j q :=
  (projectedIntegerClassNatIso (j := j) (originalISuspensionQFunctor (I := I)) q).symm ≪≫
    Functor.isoWhiskerRight suspensionReversalQNatIso (integerPiHoFunctor j q) ≪≫
      projectedIntegerClassNatIso (j := j) (originalISuspensionQFunctor (I := I)) q

/-- The whole forward reversal function is the actual integer image of the original Ho reversal. -/
theorem reversalQIntegerNatIso_hom_app (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (reversalQIntegerNatIso (j := j) q).hom.app X =
      (integerPiHoFunctor j q).map (suspensionReversalQ X).hom := by
  change 𝟙 _ ≫ (integerPiHoFunctor j q).map (suspensionReversalQ X).hom ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- The whole inverse reversal function retains the same two original collapse inverses. -/
theorem reversalQIntegerNatIso_inv_app (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (reversalQIntegerNatIso (j := j) q).inv.app X =
      (integerPiHoFunctor j q).map (suspensionReversalQ X).inv := by
  change 𝟙 _ ≫ (integerPiHoFunctor j q).map (suspensionReversalQ X).inv ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- Original I suspension preserves the actual Q counit on every cofibrant source. -/
theorem originalSuspensionCounit_weak (X : (Carrier.{u, v} (I := I))) [IsCofibrant X] :
    weakEquivalences (Carrier (I := I)) ((S (I := I)).map ((ε (I := I)).app X)) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  let _ : IsCofibrant ((𝟭 (Carrier (I := I))).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : WeakEquivalence ((ε (I := I)).app X) := (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).obj X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj X))
  let _ : Cofibration ((ι (I := I)).app X) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  let _ : Cofibration ((ι (I := I)).app ((𝟭 (Carrier (I := I))).obj X)) := by
    change Cofibration ((ι (I := I)).app X)
    exact (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration X)
  exact OrdinaryHoChosenPuppeRotation.suspensionMap_weak_of_cofibrant
    (cone (I := I)) (ι (I := I)) c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((ε (I :=
      I)).app X)
    (coneCollapse_weak ((Q (I := I)).obj X)) (coneCollapse_weak X)

/-- The original I-Q counit on Q objects is weak for every original raw spectrum. -/
theorem suspensionQCounit_weak (X : (Carrier.{u, v} (I := I))) :
    weakEquivalences (Carrier (I := I)) ((S (I := I)).map ((ε (I := I)).app ((Q (I := I)).obj X)))
      := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) X
  exact originalSuspensionCounit_weak ((Q (I := I)).obj X)

/-- The complete Q/I counit retains the same original source maps before both suspensions. -/
def suspensionQCounitNatTrans : (Q (I := I)) ⋙ (originalISuspensionQFunctor.{u, v} (I := I)) ⟶
    (originalISuspensionQFunctor (I := I)) where
  app X := (S (I := I)).map ((ε (I := I)).app ((Q (I := I)).obj X))
  naturality X Y f := by
    change (S (I := I)).map ((Q (I := I)).map ((Q (I := I)).map f)) ≫ (S (I := I)).map ((ε (I :=
      I)).app ((Q (I := I)).obj Y)) =
      (S (I := I)).map ((ε (I := I)).app ((Q (I := I)).obj X)) ≫ (S (I := I)).map ((Q (I :=
        I)).map f)
    rw [← (S (I := I)).map_comp, ← (S (I := I)).map_comp]
    exact (S (I := I)).congr_map ((ε (I := I)).naturality ((Q (I := I)).map f))

/-- Actual level weakness gives both full original integer functions of the suspended Q counit. -/
def suspensionQCounitIntegerNatIso (q : ℤ) :
    ((Q (I := I)) ⋙ (originalISuspensionQFunctor.{u, v} (I := I))) ⋙ integerPiFunctor j q ≅
      (originalISuspensionQFunctor (I := I)) ⋙ integerPiFunctor j q :=
  NatIso.ofComponents
    (fun X => integerPiLevelWeakIso (j := j) q ((S (I := I)).map ((ε (I := I)).app ((Q (I :=
      I)).obj X)))
      (suspensionQCounit_weak X)) (by
        intro X Y f
        rw [integerPiLevelWeakIso_hom (j := j), integerPiLevelWeakIso_hom (j := j)]
        exact (Functor.whiskerRight suspensionQCounitNatTrans
          (integerPiFunctor j q)).naturality f)

/-- The forward suspended-Q counit is the same actual original integer quotient map. -/
theorem suspensionQCounitIntegerNatIso_hom_app (q : ℤ) (X : (Carrier.{u, v} (I := I))) :
    (suspensionQCounitIntegerNatIso (j := j) q).hom.app X =
      (integerPiFunctor j q).map ((S (I := I)).map ((ε (I := I)).app ((Q (I := I)).obj X))) :=
  integerPiLevelWeakIso_hom (j := j) q ((S (I := I)).map ((ε (I := I)).app ((Q (I := I)).obj X)))
    (suspensionQCounit_weak X)

/-- Rotation's entire target correction retains reversal, suspended Q counit and both I-Q maps. -/
def rotationTargetCorrectionNatIso (q : ℤ) : integerPiFunctor j q ≅
    (Q (I := I)) ⋙ integerPiFunctor j q :=
  integerISuspensionPiNatIso (j := j) q ≪≫ reversalQIntegerNatIso (j := j) (q + 1) ≪≫
    (suspensionQCounitIntegerNatIso (j := j) (q + 1)).symm ≪≫
      Functor.associator (Q (I := I)) (originalISuspensionQFunctor (I := I)) (integerPiFunctor j
        (q + 1)) ≪≫
        Functor.isoWhiskerLeft (Q (I := I)) (integerISuspensionPiNatIso (j := j) q).symm

/-- The complete correction's forward map keeps the actual signed original rotation word. -/
theorem rotationTargetCorrectionNatIso_hom (q : ℤ) :
    (rotationTargetCorrectionNatIso.{u, v} (j := j) q).hom =
      (integerISuspensionPiNatIso (j := j) q).hom ≫
        (reversalQIntegerNatIso (j := j) (q + 1)).hom ≫
          (suspensionQCounitIntegerNatIso (j := j) (q + 1)).inv ≫
            (Functor.associator (Q (I := I)) (originalISuspensionQFunctor (I := I))
              (integerPiFunctor j (q + 1))).hom ≫
                Functor.whiskerLeft (Q (I := I)) (integerISuspensionPiNatIso (j := j) q).inv := rfl

/-- The raw strict Puppe boundary uses the same original chosen cone and zero endpoints. -/
def strictBoundary (F : Arrow (Carrier.{u, v} (I := I))) :
    strictCofiberFunctor.obj F ⟶ (S (I := I)).obj F.left :=
  OrdinaryHoChosenPuppe.boundary (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero F

/-- Both original Q counit endpoints retain the entire strict-boundary square. -/
theorem strictCofiberCounit_boundary (F : Arrow (Carrier.{u, v} (I := I))) :
    strictCofiberCounit F ≫ strictBoundary F = boundary F ≫ (S (I := I)).map ((ε (I := I)).app
      F.left) :=
  OrdinaryHoChosenPuppe.boundary_naturality (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (qArrowCounit F)

/-- The strict next boundary has the unchanged original I-Q target of the original right object. -/
def relativeNextBoundary (F : Arrow (Carrier.{u, v} (I := I))) :
    strictNextCofiberFunctor.obj F ⟶ (originalISuspensionQFunctor (I := I)).obj F.right :=
  strictBoundary (targetInclusionArrow F)

/-- The actual next Puppe boundary keeps the complete original suspension reversal. -/
theorem rotationComparison_boundary (F : Arrow (Carrier.{u, v} (I := I))) :
    (H (I := I)).map (rotationComparison F) ≫ (H (I := I)).map ((originalISuspensionQFunctor (I :=
      I)).map F.hom) ≫
        (suspensionReversalQ F.right).hom = (H (I := I)).map (relativeNextBoundary F) := by
  let _ : IsCofibrant ((Q (I := I)).mapArrow.obj F).right := by
    change IsCofibrant ((Q (I := I)).obj F.right)
    exact Replacement.isCofibrant_cofibrantReplacement (B := B) (A := Index) F.right
  let _ : Cofibration ((ι (I := I)).app ((Q (I := I)).mapArrow.obj F).right) := by
    change Cofibration ((ι (I := I)).app ((Q (I := I)).obj F.right))
    exact (HomotopicalAlgebra.cofibration_iff _).mpr
      (OriginalICone.inclusion_cofibration ((Q (I := I)).obj F.right))
  exact OrdinaryHoChosenPuppeRotation.rotationComparison_boundary (cone (I := I)) (ι (I := I)) c hc
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((Q (I := I)).mapArrow.obj F)
    (coneCollapse_weak ((Q (I := I)).obj F.right))

/-- The next-Q boundary retains reversal and the original suspended Q counit on the right. -/
theorem rotationQComparison_boundary (F : Arrow (Carrier.{u, v} (I := I))) :
    (H (I := I)).map (rotationQComparison F) ≫ (H (I := I)).map ((originalISuspensionQFunctor (I
      := I)).map F.hom) ≫
        (suspensionReversalQ F.right).hom =
      (H (I := I)).map (boundary (targetInclusionArrow F)) ≫ (H (I := I)).map ((S (I := I)).map
        ((ε (I := I)).app ((Q (I := I)).obj F.right))) := by
  rw [rotationQComparison, (H (I := I)).map_comp, Category.assoc, rotationComparison_boundary]
  change (H (I := I)).map (strictCofiberCounit (targetInclusionArrow F)) ≫
      (H (I := I)).map (strictBoundary (targetInclusionArrow F)) =
    (H (I := I)).map (boundary (targetInclusionArrow F)) ≫
      (H (I := I)).map ((S (I := I)).map ((ε (I := I)).app (targetInclusionArrow F).left))
  rw [← (H (I := I)).map_comp, strictCofiberCounit_boundary, (H (I := I)).map_comp]

/-- Every original integer class retains the full signed next-Q boundary and suspended counit. -/
theorem rotationQInteger_boundary (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (rotationQIntegerIso (j := j) q F).hom ≫
        (integerPiFunctor j q).map ((originalISuspensionQFunctor (I := I)).map F.hom) ≫
          (reversalQIntegerNatIso (j := j) q).hom.app F.right =
      (integerPiFunctor j q).map (boundary (targetInclusionArrow F)) ≫
        (suspensionQCounitIntegerNatIso (j := j) q).hom.app F.right := by
  have h := (integerPiHoFunctor j q).congr_map (rotationQComparison_boundary F)
  simp only [Functor.map_comp, integerPiHoFunctor_map (j := j)] at h
  rw [← rotationQIntegerIso_hom (j := j), ← reversalQIntegerNatIso_hom_app (j := j),
    ← suspensionQCounitIntegerNatIso_hom_app (j := j)] at h
  exact h

/-- The target correction after original desuspension retains actual reversal and both counit
maps. -/
theorem rotationTargetCorrectionNatIso_after_inverse (q : ℤ) :
    (integerISuspensionPiNatIso.{u, v} (j := j) q).inv ≫
        (rotationTargetCorrectionNatIso (j := j) q).hom =
      (reversalQIntegerNatIso (j := j) (q + 1)).hom ≫
        (suspensionQCounitIntegerNatIso (j := j) (q + 1)).inv ≫
          (Functor.associator (Q (I := I)) (originalISuspensionQFunctor (I := I))
            (integerPiFunctor j (q + 1))).hom ≫
              Functor.whiskerLeft (Q (I := I)) (integerISuspensionPiNatIso (j := j) q).inv := by
  rw [rotationTargetCorrectionNatIso_hom (j := j)]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual rotation comparison is desuspended by the complete original all-integer I-Q map. -/
def rotationSourceDesuspensionNatTrans (q : ℤ) :
    nextQCofiberFunctor.{u, v} ⋙ integerPiFunctor j (q + 1) ⟶
      Arrow.leftFunc ⋙ integerPiFunctor j q :=
  (rotationQIntegerNatIso (j := j) (q + 1)).hom ≫
    (Functor.associator Arrow.leftFunc (originalISuspensionQFunctor (I := I))
      (integerPiFunctor j (q + 1))).hom ≫
        Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso (j := j) q).inv

/-- Each original rotation-desuspension class retains its complete weak-Q rotation and I-Q
inverse. -/
def rotationSourceDesuspension (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F ⟶
      (integerPiFunctor j q).obj F.left :=
  (rotationSourceDesuspensionNatTrans (j := j) q).app F

/-- The full rotation-desuspension function is the same original two integer functions. -/
theorem rotationSourceDesuspension_apply (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F) :
    (rotationSourceDesuspension (j := j) q F).hom a =
      ((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom
        ((rotationQIntegerIso (j := j) (q + 1) F).hom.hom a) := by
  dsimp only [rotationSourceDesuspension, rotationSourceDesuspensionNatTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator, rotationQIntegerNatIso]
  rfl

/-- The actual next inclusion boundary is a complete original integer natural family. -/
def nextConnectingPlusOneNatTrans (q : ℤ) :
    nextQCofiberFunctor.{u, v} ⋙ integerPiFunctor j (q + 1) ⟶
      Arrow.rightFunc ⋙ ((Q (I := I)) ⋙ integerPiFunctor j q) where
  app F := connectingPlusOne (j := j) q (targetInclusionArrow F)
  naturality _ _ m := connectingPlusOne_naturality (j := j) q (targetInclusionFunctor.map m)

/-- Every actual next boundary class retains its exact original chosen-boundary connecting
function. -/
def nextConnectingPlusOne (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F ⟶
      ((Q (I := I)) ⋙ integerPiFunctor j q).obj F.right :=
  (nextConnectingPlusOneNatTrans (j := j) q).app F

/-- The next actual connecting map retains the complete original rotation target correction. -/
theorem nextConnectingPlusOne_correction_apply (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F) :
    (nextConnectingPlusOne (j := j) q F).hom a =
      ((rotationTargetCorrectionNatIso (j := j) q).hom.app F.right).hom
        (((integerPiFunctor j q).map F.hom).hom
          ((rotationSourceDesuspension (j := j) q F).hom a)) := by
  let b := (rotationQIntegerIso (j := j) (q + 1) F).hom.hom a
  let d := ((integerPiFunctor j (q + 1)).map
    ((originalISuspensionQFunctor (I := I)).map F.hom)).hom b
  have hn := ConcreteCategory.congr_hom
    (integerISuspensionPiNatIso_inv_naturality (j := j) q F.hom) b
  change ((integerISuspensionPiNatIso (j := j) q).inv.app F.right).hom d =
    ((integerPiFunctor j q).map F.hom).hom
      (((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom b) at hn
  have hc := ConcreteCategory.congr_hom
    (congr_app (rotationTargetCorrectionNatIso_after_inverse (j := j) q) F.right) d
  change ((rotationTargetCorrectionNatIso (j := j) q).hom.app F.right).hom
      (((integerISuspensionPiNatIso (j := j) q).inv.app F.right).hom d) =
    ((integerISuspensionPiNatIso (j := j) q).inv.app ((Q (I := I)).obj F.right)).hom
      (((suspensionQCounitIntegerNatIso (j := j) (q + 1)).inv.app F.right).hom
        (((reversalQIntegerNatIso (j := j) (q + 1)).hom.app F.right).hom d)) at hc
  have hr := ConcreteCategory.congr_hom (rotationQInteger_boundary (j := j) (q + 1) F) a
  change ((reversalQIntegerNatIso (j := j) (q + 1)).hom.app F.right).hom d =
    ((suspensionQCounitIntegerNatIso (j := j) (q + 1)).hom.app F.right).hom
      (((integerPiFunctor j (q + 1)).map
        (boundary (targetInclusionArrow F))).hom a) at hr
  have ht := ConcreteCategory.congr_hom
    ((suspensionQCounitIntegerNatIso (j := j) (q + 1)).app F.right).hom_inv_id
      (((integerPiFunctor j (q + 1)).map (boundary (targetInclusionArrow F))).hom a)
  change ((suspensionQCounitIntegerNatIso (j := j) (q + 1)).inv.app F.right).hom
      (((suspensionQCounitIntegerNatIso (j := j) (q + 1)).hom.app F.right).hom
        (((integerPiFunctor j (q + 1)).map
          (boundary (targetInclusionArrow F))).hom a)) =
    ((integerPiFunctor j (q + 1)).map (boundary (targetInclusionArrow F))).hom a at ht
  rw [rotationSourceDesuspension_apply (j := j)]
  change (connectingPlusOne (j := j) q (targetInclusionArrow F)).hom a =
    ((rotationTargetCorrectionNatIso (j := j) q).hom.app F.right).hom
      (((integerPiFunctor j q).map F.hom).hom
        (((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom b))
  rw [← hn, hc, hr, ht, connectingPlusOne_apply (j := j)]
  rfl

/-- The entire rotation/desuspension comparison is an actual original integer Iso. -/
def rotationSourceDesuspensionIso (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F ≅
      (integerPiFunctor j q).obj F.left :=
  rotationQIntegerIso (j := j) (q + 1) F ≪≫ ((integerISuspensionPiNatIso (j := j) q).app
    F.left).symm

/-- Both inverse directions retain the same original weak-rotation and I-Q functions. -/
theorem rotationSourceDesuspensionIso_hom (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (rotationSourceDesuspensionIso (j := j) q F).hom = rotationSourceDesuspension (j := j) q F := by
  apply GrpCat.hom_ext
  ext a
  exact (rotationSourceDesuspension_apply (j := j) q F a).symm

/-- The actual next target inclusion maps to the same entire original connecting class. -/
theorem rotationSourceDesuspension_inclusion_apply (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F)) :
    (rotationSourceDesuspension (j := j) q F).hom
        (((inclusionIntegerNatTrans (j := j) (q + 1)).app (targetInclusionArrow F)).hom a) =
      (connectingPlusOne (j := j) q F).hom a := by
  have h := rotationQ_inclusionInteger (j := j) (q + 1) F
  rw [inclusionInteger_formula (j := j), qCounitHoIso_integer_inverse (j := j)] at h
  rw [integerPiHoFunctor_map (j := j), integerPiHoFunctor_map (j := j),
    ← rotationQIntegerIso_hom (j := j)] at h
  have h' := ConcreteCategory.congr_hom h a
  rw [rotationSourceDesuspension_apply (j := j), inclusionIntegerNatTrans_app (j := j),
    inclusionInteger_formula (j := j), qCounitHoIso_integer_inverse (j := j),
      connectingPlusOne_apply (j := j)]
  exact congrArg ((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom h'

end HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerRotation
