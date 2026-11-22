/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerMaps
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ISuspensionIntegerPi

/-!
# Actual integer connecting maps for the original Q cofiber

Every connecting map uses the same original chosen cofiber boundary into
the original I suspension of QX, followed by the proved integer I-Q inverse.
Both original components of every Arrow square and the complete integer
predecessor transport are retained. No long exact sequence is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberConnectingIntegerPiGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index.{u, v})
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index.{u, v})
private abbrev cone := OriginalICone.cone (B := B) (I := Index.{u, v})
private abbrev ι := OriginalICone.inclusion (B := B) (I := Index.{u, v})
private abbrev c := OriginalISuspension.cocone (B := B) (I := Index.{u, v})
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := Index.{u, v})
private abbrev suspensionCocone (X : Carrier.{u, v}) := c (Arrow.mk (Diagrams.toZero X))

/-- The complete original cone leg is typed at the actual original cofiber object. -/
def cofiberConeLeg (F : Arrow Carrier.{u, v}) : cone.obj (Q.obj F.left) ⟶ cofiber.obj F :=
  (c (Q.mapArrow.obj F)).inl

/-- The original cofiber map retains its complete original Q cone leg. -/
theorem cofiberMap_cone {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    cofiberConeLeg F ≫ cofiber.map m = cone.map (Q.map m.left) ≫ cofiberConeLeg G :=
  OrdinaryHoChosenPuppe.cofiberMap_cone cone ι c hc (Q.mapArrow.map m)

/-- The native zero leg retains the exact original I-Q suspension target. -/
def suspensionZeroLeg (X : Carrier.{u, v}) :
    Diagrams.zeroDiagram ⟶ originalISuspensionQFunctor.obj X :=
  (suspensionCocone (Q.obj X)).inr

/-- The original I-Q cone leg keeps its complete actual suspension target. -/
def suspensionConeLeg (X : Carrier.{u, v}) :
    cone.obj (Q.obj X) ⟶ originalISuspensionQFunctor.obj X :=
  (suspensionCocone (Q.obj X)).inl

/-- The complete original cofiber cone leg maps to the same original suspension cone leg. -/
theorem cofiberConeLeg_boundary (F : Arrow Carrier.{u, v}) :
    cofiberConeLeg F ≫ boundary F = suspensionConeLeg F.left := boundary_cone F

/-- The original inclusion/boundary square retains the native zero leg at its actual target. -/
theorem originalInclusionBoundary (F : Arrow Carrier.{u, v}) :
    inclusion F ≫ boundary F = Diagrams.toZero (Q.obj F.right) ≫ suspensionZeroLeg F.left :=
  inclusion_boundary F

/-- The actual chosen boundary retains the full original Q and I-suspension source map. -/
def originalBoundaryNatTrans : cofiber.{u, v} ⟶
    Arrow.leftFunc ⋙ originalISuspensionQFunctor where
  app F := boundary F
  naturality _ _ m := boundary_naturality m

/-- The boundary and the proved desuspension compose as whole original natural families. -/
def connectingPlusOneNatTrans (q : ℤ) : cofiber.{u, v} ⋙ integerStablePiFunctor (q + 1) ⟶
    Arrow.leftFunc ⋙ integerStablePiFunctor q :=
  Functor.whiskerRight originalBoundaryNatTrans (integerStablePiFunctor (q + 1)) ≫
    (Functor.associator Arrow.leftFunc originalISuspensionQFunctor
      (integerStablePiFunctor (q + 1))).hom ≫
        Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso q).inv

/-- The actual boundary in degree q+1 is desuspended by the entire original I-Q inverse. -/
def connectingPlusOne (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (integerStablePiFunctor (q + 1)).obj (cofiber.obj F) ⟶
      (integerStablePiFunctor q).obj F.left :=
  (connectingPlusOneNatTrans q).app F

/-- The whole family keeps the original chosen boundary and the complete I-Q inverse. -/
theorem connectingPlusOneNatTrans_formula (q : ℤ) :
    connectingPlusOneNatTrans.{u, v} q =
      Functor.whiskerRight originalBoundaryNatTrans (integerStablePiFunctor (q + 1)) ≫
        (Functor.associator Arrow.leftFunc originalISuspensionQFunctor
          (integerStablePiFunctor (q + 1))).hom ≫
            Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso q).inv := rfl

/-- Every actual class keeps the original chosen boundary and all I-Q inverse factors. -/
theorem connectingPlusOne_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F)) :
    (connectingPlusOne q F).hom a =
      ((integerISuspensionPiNatIso q).inv.app F.left).hom
        (((integerStablePiFunctor (q + 1)).map (boundary F)).hom a) := by
  dsimp only [connectingPlusOne, connectingPlusOneNatTrans, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, originalBoundaryNatTrans,
    Functor.associator]
  rfl

/-- Both components of the original Arrow square retain the same complete connecting square. -/
theorem connectingPlusOne_naturality (q : ℤ) {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (integerStablePiFunctor (q + 1)).map (cofiber.map m) ≫ connectingPlusOne q G =
      connectingPlusOne q F ≫ (integerStablePiFunctor q).map m.left :=
  (connectingPlusOneNatTrans q).naturality m

/-- The predecessor degree is transported by its actual integer equality. -/
def integerDegreeNatIso (q r : ℤ) (h : q = r) : integerStablePiFunctor.{u, v} q ≅
    integerStablePiFunctor r := eqToIso (congrArg integerStablePiFunctor h)

/-- The predecessor degree retains the complete original integer equality transport. -/
def predecessorDegreeNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    integerStablePiFunctor ((q - 1) + 1) :=
  integerDegreeNatIso q ((q - 1) + 1) (by omega)

/-- The actual integer connecting map has source degree q and original target degree q-1. -/
def connecting (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (integerStablePiFunctor q).obj (cofiber.obj F) ⟶
      (integerStablePiFunctor (q - 1)).obj F.left :=
  (predecessorDegreeNatIso q).hom.app (cofiber.obj F) ≫ connectingPlusOne (q - 1) F

/-- Every canonical connecting component retains the complete predecessor and boundary family. -/
theorem connecting_formula (q : ℤ) (F : Arrow Carrier.{u, v}) :
    connecting q F = (predecessorDegreeNatIso q).hom.app (cofiber.obj F) ≫
      connectingPlusOne (q - 1) F := rfl

/-- The canonical all-integer connecting family retains both original Arrow components. -/
def connectingNatTrans (q : ℤ) : cofiber.{u, v} ⋙ integerStablePiFunctor q ⟶
    Arrow.leftFunc ⋙ integerStablePiFunctor (q - 1) :=
  Functor.whiskerLeft cofiber (predecessorDegreeNatIso q).hom ≫
    connectingPlusOneNatTrans (q - 1)

/-- The canonical natural family acts by the same entire chosen-boundary connecting map. -/
theorem connectingNatTrans_app (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (connectingNatTrans q).app F = connecting q F := rfl

/-- Every actual all-integer connecting square retains its original whole-arrow map. -/
theorem connecting_naturality (q : ℤ) {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (integerStablePiFunctor q).map (cofiber.map m) ≫ connecting q G =
      connecting q F ≫ (integerStablePiFunctor (q - 1)).map m.left :=
  (connectingNatTrans q).naturality m

/-- Desuspending and resuspending the entire connecting family recovers the original boundary. -/
theorem connectingPlusOneNatTrans_resuspension (q : ℤ) :
    connectingPlusOneNatTrans.{u, v} q ≫
        Functor.whiskerLeft Arrow.leftFunc (integerISuspensionPiNatIso q).hom =
      Functor.whiskerRight originalBoundaryNatTrans (integerStablePiFunctor (q + 1)) ≫
        (Functor.associator Arrow.leftFunc originalISuspensionQFunctor
          (integerStablePiFunctor (q + 1))).hom := by
  rw [connectingPlusOneNatTrans_formula]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.comp_id]

/-- The original source/inclusion composite factors through the same actual original I cone. -/
theorem originalSourceInclusion_factors_cone (F : Arrow Carrier.{u, v}) :
    Q.map F.hom ≫ inclusion F =
      ι.app (Q.obj F.left) ≫ (c (Q.mapArrow.obj F)).inl :=
  (c (Q.mapArrow.obj F)).condition.symm

/-- The chosen cofiber maps to the original I cone of its unchanged Q target. -/
def cofiberConeComparison (F : Arrow Carrier.{u, v}) :
    cofiber.obj F ⟶ cone.obj (Q.obj F.right) :=
  OrdinaryHoChosenPuppe.coneComparison cone ι c hc (Q.mapArrow.obj F)

/-- The actual cofiber-to-cone comparison retains its full original cone leg. -/
theorem cofiberConeComparison_cone (F : Arrow Carrier.{u, v}) :
    cofiberConeLeg F ≫ cofiberConeComparison F = cone.map (Q.map F.hom) :=
  OrdinaryHoChosenPuppe.coneComparison_cone cone ι c hc (Q.mapArrow.obj F)

/-- The same cofiber-to-cone comparison retains its full original target leg. -/
theorem cofiberConeComparison_target (F : Arrow Carrier.{u, v}) :
    inclusion F ≫ cofiberConeComparison F = ι.app (Q.obj F.right) :=
  OrdinaryHoChosenPuppe.coneComparison_target cone ι c hc (Q.mapArrow.obj F)

/-- Every entire Arrow square retains both original legs of the actual cofiber-to-cone map. -/
theorem cofiberConeComparison_naturality {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    cofiber.map m ≫ cofiberConeComparison G =
      cofiberConeComparison F ≫ cone.map (Q.map m.right) := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Q.mapArrow.obj F))
  · change cofiberConeLeg F ≫ (cofiber.map m ≫ cofiberConeComparison G) =
      cofiberConeLeg F ≫ (cofiberConeComparison F ≫ cone.map (Q.map m.right))
    rw [← Category.assoc, cofiberMap_cone]
    rw [Category.assoc, cofiberConeComparison_cone, ← Category.assoc,
      cofiberConeComparison_cone, ← cone.map_comp, ← cone.map_comp]
    exact cone.congr_map (Q.mapArrow.map m).w
  · change inclusion F ≫ (cofiber.map m ≫ cofiberConeComparison G) =
      inclusion F ≫ (cofiberConeComparison F ≫ cone.map (Q.map m.right))
    rw [← Category.assoc, ← inclusion_naturality, Category.assoc,
      cofiberConeComparison_target, ← Category.assoc, cofiberConeComparison_target]
    exact ι.naturality (Q.map m.right)

/-- The original boundary/source-suspension composite factors through the actual target I cone. -/
theorem originalBoundarySuspension_factors_cone (F : Arrow Carrier.{u, v}) :
    boundary F ≫ originalISuspensionQFunctor.map F.hom =
      cofiberConeComparison F ≫ (suspensionCocone (Q.obj F.right)).inl :=
  OrdinaryHoChosenPuppe.boundary_suspension_factors_cone
    cone ι c hc Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q.mapArrow.obj F)

/-- Both integer functions of Root's original Q Ho Iso agree with the original Q counit Iso. -/
theorem qCounitHoIso_integerIso (q : ℤ) (X : Carrier.{u, v}) :
    (integerStablePiHoFunctor q).mapIso (qCounitHoIso X) =
      (qCounitIntegerNatIso q).app X := by
  apply Iso.ext
  change (integerStablePiHoFunctor q).map (H.map (ε.app X)) =
    (qCounitIntegerNatIso q).hom.app X
  rw [integerStablePiHoFunctor_map, qCounitIntegerNatIso_hom_app]

/-- The original Q inverse used in the cofiber inclusion is the same integer quotient inverse. -/
theorem qCounitHoIso_integer_inverse (q : ℤ) (X : Carrier.{u, v}) :
    (integerStablePiHoFunctor q).map (qCounitHoIso X).inv =
      (qCounitIntegerNatIso q).inv.app X :=
  congrArg (fun e => e.inv) (qCounitHoIso_integerIso q X)

/-- The whole source-map family keeps the original Arrow itself on every integer group. -/
def sourceIntegerNatTrans (q : ℤ) : Arrow.leftFunc ⋙ integerStablePiFunctor.{u, v} q ⟶
    Arrow.rightFunc ⋙ integerStablePiFunctor q :=
  Functor.whiskerRight Arrow.leftToRight (integerStablePiFunctor q)

/-- The whole target-inclusion family keeps its original Q inverse and chosen cofiber leg. -/
def inclusionIntegerNatTrans (q : ℤ) :
    Arrow.rightFunc ⋙ integerStablePiFunctor.{u, v} q ⟶ cofiber ⋙ integerStablePiFunctor q where
  app F := inclusionInteger q F
  naturality _ _ m := inclusionInteger_naturality q m

/-- Every inclusion family component is the same complete original Q/inclusion function. -/
theorem inclusionIntegerNatTrans_app (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (inclusionIntegerNatTrans q).app F = inclusionInteger q F := rfl

/-- Every original source class has trivial image through the Q source and actual inclusion. -/
theorem qSource_inclusion_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj (Q.obj F.left)) :
    ((integerStablePiFunctor q).map (inclusion F)).hom
      (((integerStablePiFunctor q).map (Q.map F.hom)).hom a) = 1 := by
  change ((integerStablePiFunctor q).map (Q.map F.hom) ≫
    (integerStablePiFunctor q).map (inclusion F)).hom a = 1
  rw [← Functor.map_comp, originalSourceInclusion_factors_cone]
  exact integerMap_through_original_cone_apply q _ _ a

/-- The full original source/inclusion composite is null on every original integer class. -/
theorem source_inclusion_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj F.left) :
    (inclusionInteger q F).hom (((integerStablePiFunctor q).map F.hom).hom a) = 1 := by
  rw [inclusionInteger_formula, qCounitHoIso_integer_inverse]
  change ((integerStablePiFunctor q).map (inclusion F)).hom
    (((qCounitIntegerNatIso q).inv.app F.right).hom
      (((integerStablePiFunctor q).map F.hom).hom a)) = 1
  have h := ConcreteCategory.congr_hom ((qCounitIntegerNatIso q).inv.naturality F.hom) a
  change ((qCounitIntegerNatIso q).inv.app F.right).hom
      (((integerStablePiFunctor q).map F.hom).hom a) =
    ((integerStablePiFunctor q).map (Q.map F.hom)).hom
      (((qCounitIntegerNatIso q).inv.app F.left).hom a) at h
  rw [h]
  exact qSource_inclusion_null q F _

/-- The full inclusion/boundary composite is null through the same original native zero. -/
theorem inclusion_connectingPlusOne_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor (q + 1)).obj F.right) :
    (connectingPlusOne q F).hom (((inclusionIntegerNatTrans (q + 1)).app F).hom a) = 1 := by
  rw [connectingPlusOne_apply, inclusionIntegerNatTrans_app,
    inclusionInteger_formula, qCounitHoIso_integer_inverse]
  let b : (integerStablePiFunctor (q + 1)).obj (Q.obj F.right) :=
    ((qCounitIntegerNatIso (q + 1)).inv.app F.right).hom a
  have h : ((integerStablePiFunctor (q + 1)).map (boundary F)).hom
      (((integerStablePiFunctor (q + 1)).map (inclusion F)).hom b) = 1 := by
    change ((integerStablePiFunctor (q + 1)).map (inclusion F) ≫
      (integerStablePiFunctor (q + 1)).map (boundary F)).hom b = 1
    rw [← Functor.map_comp, originalInclusionBoundary]
    exact integerMap_through_zero_apply (q + 1)
      (Diagrams.toZero (Q.obj F.right)) (suspensionZeroLeg F.left) b
  change ((integerISuspensionPiNatIso q).inv.app F.left).hom
    (((integerStablePiFunctor (q + 1)).map (boundary F)).hom
      (((integerStablePiFunctor (q + 1)).map (inclusion F)).hom b)) = 1
  rw [h]
  exact map_one _

/-- The actual boundary/source-suspension map is null on every original integer class. -/
theorem originalBoundarySuspension_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj (cofiber.obj F)) :
    ((integerStablePiFunctor q).map (originalISuspensionQFunctor.map F.hom)).hom
      (((integerStablePiFunctor q).map (boundary F)).hom a) = 1 := by
  change ((integerStablePiFunctor q).map (boundary F) ≫
    (integerStablePiFunctor q).map (originalISuspensionQFunctor.map F.hom)).hom a = 1
  rw [← Functor.map_comp, originalBoundarySuspension_factors_cone]
  exact integerMap_through_original_cone_apply q _ _ a

/-- The original connecting/source composite is null with no extra condition on the spectrum. -/
theorem connectingPlusOne_source_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F)) :
    ((integerStablePiFunctor q).map F.hom).hom ((connectingPlusOne q F).hom a) = 1 := by
  rw [connectingPlusOne_apply]
  have h := ConcreteCategory.congr_hom
    (integerISuspensionPiNatIso_inv_naturality q F.hom)
    (((integerStablePiFunctor (q + 1)).map (boundary F)).hom a)
  change ((integerISuspensionPiNatIso q).inv.app F.right).hom
      (((integerStablePiFunctor (q + 1)).map
        (originalISuspensionQFunctor.map F.hom)).hom
          (((integerStablePiFunctor (q + 1)).map (boundary F)).hom a)) =
    ((integerStablePiFunctor q).map F.hom).hom
      (((integerISuspensionPiNatIso q).inv.app F.left).hom
        (((integerStablePiFunctor (q + 1)).map (boundary F)).hom a)) at h
  rw [← h, originalBoundarySuspension_null]
  exact map_one _

/-- All actual inclusion functions preserve every literal integer-equality transport. -/
theorem integerDegree_inclusion_naturality (q r : ℤ) (h : q = r) :
    inclusionIntegerNatTrans.{u, v} q ≫
        Functor.whiskerLeft cofiber (integerDegreeNatIso q r h).hom =
      Functor.whiskerLeft Arrow.rightFunc (integerDegreeNatIso q r h).hom ≫
        inclusionIntegerNatTrans r := by
  cases h
  change inclusionIntegerNatTrans q ≫
      Functor.whiskerLeft cofiber (𝟙 (integerStablePiFunctor q)) =
    Functor.whiskerLeft Arrow.rightFunc (𝟙 (integerStablePiFunctor q)) ≫
      inclusionIntegerNatTrans q
  rw [Functor.whiskerLeft_id', Functor.whiskerLeft_id',
    Category.comp_id, Category.id_comp]

/-- The canonical inclusion/connecting composite is null in every original integer degree. -/
theorem inclusion_connecting_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj F.right) :
    (connecting q F).hom (((inclusionIntegerNatTrans q).app F).hom a) = 1 := by
  have h := ConcreteCategory.congr_hom (congr_app
    (integerDegree_inclusion_naturality q ((q - 1) + 1) (by omega)) F) a
  change ((predecessorDegreeNatIso q).hom.app (cofiber.obj F)).hom
      (((inclusionIntegerNatTrans q).app F).hom a) =
    ((inclusionIntegerNatTrans ((q - 1) + 1)).app F).hom
      (((predecessorDegreeNatIso q).hom.app F.right).hom a) at h
  change (connectingPlusOne (q - 1) F).hom
    (((predecessorDegreeNatIso q).hom.app (cofiber.obj F)).hom
      (((inclusionIntegerNatTrans q).app F).hom a)) = 1
  rw [h]
  exact inclusion_connectingPlusOne_null (q - 1) F _

/-- The canonical connecting/source composite is null with its full predecessor degree map. -/
theorem connecting_source_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj (cofiber.obj F)) :
    ((integerStablePiFunctor (q - 1)).map F.hom).hom ((connecting q F).hom a) = 1 := by
  change ((integerStablePiFunctor (q - 1)).map F.hom).hom
    ((connectingPlusOne (q - 1) F).hom
      (((predecessorDegreeNatIso q).hom.app (cofiber.obj F)).hom a)) = 1
  exact connectingPlusOne_source_null (q - 1) F _

/-- The actual group null function is the constant group unit, with no commutativity condition. -/
def trivialGroupMap (G K : GrpCat.{v}) : G ⟶ K :=
  GrpCat.ofHom
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => (one_mul (1 : K)).symm }

/-- The entire original source/inclusion morphism is the actual trivial group morphism. -/
theorem source_inclusion_null_map (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (sourceIntegerNatTrans q ≫ inclusionIntegerNatTrans q).app F =
      trivialGroupMap ((Arrow.leftFunc ⋙ integerStablePiFunctor q).obj F)
        ((cofiber ⋙ integerStablePiFunctor q).obj F) := by
  apply GrpCat.hom_ext
  ext a
  exact source_inclusion_null q F a

/-- The entire canonical inclusion/connecting morphism is the same actual group null function. -/
theorem inclusion_connecting_null_map (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (inclusionIntegerNatTrans q ≫ connectingNatTrans q).app F =
      trivialGroupMap ((Arrow.rightFunc ⋙ integerStablePiFunctor q).obj F)
        ((Arrow.leftFunc ⋙ integerStablePiFunctor (q - 1)).obj F) := by
  apply GrpCat.hom_ext
  ext a
  exact inclusion_connecting_null q F a

/-- The entire canonical connecting/source morphism retains its actual group null function. -/
theorem connecting_source_null_map (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (connectingNatTrans q ≫ sourceIntegerNatTrans (q - 1)).app F =
      trivialGroupMap ((cofiber ⋙ integerStablePiFunctor q).obj F)
        ((Arrow.rightFunc ⋙ integerStablePiFunctor (q - 1)).obj F) := by
  apply GrpCat.hom_ext
  ext a
  exact connecting_source_null q F a


section CallerCofiber

open HomotopicalAlgebra.EnrichedProjective.Native.OriginalISuspensionCofibrantComparison

variable (cc : ∀ F : Arrow Carrier.{u, v},
    PushoutCocone (ι.app (Q.obj F.left)) (Q.map F.hom))
  (hcc : ∀ F, IsColimit (cc F))

/-- Every caller cofiber map is the actual desc of the same entire original Q span. -/
def callerCofiberMap {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (cc F).pt ⟶ (cc G).pt :=
  PushoutCocone.IsColimit.desc (hcc F)
    (cone.map (Q.map m.left) ≫ (cc G).inl) (Q.map m.right ≫ (cc G).inr) (by
      rw [← Category.assoc, ← ι.naturality (Q.map m.left),
        Category.assoc, (cc G).condition, ← Category.assoc]
      change (Q.map m.left ≫ Q.map G.hom) ≫ (cc G).inr =
        Q.map F.hom ≫ Q.map m.right ≫ (cc G).inr
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ (cc G).inr) (Q.mapArrow.map m).w)

/-- The complete caller cone leg keeps the original Q left component and I-cone map. -/
theorem callerCofiberMap_cone {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (cc F).inl ≫ callerCofiberMap cc hcc m =
      cone.map (Q.map m.left) ≫ (cc G).inl :=
  PushoutCocone.IsColimit.inl_desc (hcc F) _ _ _

/-- The complete caller target leg keeps the original Q right component. -/
theorem callerCofiberMap_target {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (cc F).inr ≫ callerCofiberMap cc hcc m = Q.map m.right ≫ (cc G).inr :=
  PushoutCocone.IsColimit.inr_desc (hcc F) _ _ _

/-- Every identity is retained through both actual caller cofiber desc legs. -/
theorem callerCofiberMap_id (F : Arrow Carrier.{u, v}) :
    callerCofiberMap cc hcc (𝟙 F) = 𝟙 (cc F).pt := by
  apply PushoutCocone.IsColimit.hom_ext (hcc F)
  · rw [callerCofiberMap_cone]
    change cone.map (Q.map (𝟙 F.left)) ≫ (cc F).inl = (cc F).inl ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
  · rw [callerCofiberMap_target]
    change Q.map (𝟙 F.right) ≫ (cc F).inr = (cc F).inr ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Every composite retains both complete original Arrow components under the same Q map. -/
theorem callerCofiberMap_comp {F G J : Arrow Carrier.{u, v}}
    (m : F ⟶ G) (n : G ⟶ J) :
    callerCofiberMap cc hcc (m ≫ n) =
      callerCofiberMap cc hcc m ≫ callerCofiberMap cc hcc n := by
  apply PushoutCocone.IsColimit.hom_ext (hcc F)
  · rw [callerCofiberMap_cone, ← Category.assoc, callerCofiberMap_cone,
      Category.assoc, callerCofiberMap_cone]
    change cone.map (Q.map (m.left ≫ n.left)) ≫ (cc J).inl =
      cone.map (Q.map m.left) ≫ cone.map (Q.map n.left) ≫ (cc J).inl
    rw [Functor.map_comp, Functor.map_comp, Category.assoc]
  · rw [callerCofiberMap_target, ← Category.assoc, callerCofiberMap_target,
      Category.assoc, callerCofiberMap_target]
    change Q.map (m.right ≫ n.right) ≫ (cc J).inr =
      Q.map m.right ≫ Q.map n.right ≫ (cc J).inr
    rw [Functor.map_comp, Category.assoc]

/-- Independent caller cofiber choices form a functor on the full original Arrow category. -/
def callerCofiberFunctor : Arrow Carrier.{u, v} ⥤ Carrier.{u, v} where
  obj F := (cc F).pt
  map := callerCofiberMap cc hcc
  map_id := callerCofiberMap_id cc hcc
  map_comp := callerCofiberMap_comp cc hcc

/-- Actual colimit uniqueness compares the same original Q cofiber with the caller choice. -/
def callerCofiberIso (F : Arrow Carrier.{u, v}) : cofiber.obj F ≅ (cc F).pt :=
  (hc (Q.mapArrow.obj F)).coconePointUniqueUpToIso (hcc F)

/-- The actual forward choice map retains the entire original cofiber cone leg. -/
theorem callerCofiberIso_hom_cone (F : Arrow Carrier.{u, v}) :
    cofiberConeLeg F ≫ (callerCofiberIso cc hcc F).hom = (cc F).inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (hc (Q.mapArrow.obj F)) (hcc F) WalkingSpan.left

/-- The actual forward choice map retains the entire original cofiber target leg. -/
theorem callerCofiberIso_hom_target (F : Arrow Carrier.{u, v}) :
    inclusion F ≫ (callerCofiberIso cc hcc F).hom = (cc F).inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (hc (Q.mapArrow.obj F)) (hcc F) WalkingSpan.right

/-- The actual inverse choice map retains the same complete cone leg. -/
theorem callerCofiberIso_inv_cone (F : Arrow Carrier.{u, v}) :
    (cc F).inl ≫ (callerCofiberIso cc hcc F).inv = cofiberConeLeg F :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (hc (Q.mapArrow.obj F)) (hcc F) WalkingSpan.left

/-- The actual inverse choice map retains the same complete target inclusion. -/
theorem callerCofiberIso_inv_target (F : Arrow Carrier.{u, v}) :
    (cc F).inr ≫ (callerCofiberIso cc hcc F).inv = inclusion F :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (hc (Q.mapArrow.obj F)) (hcc F) WalkingSpan.right

/-- Both actual choice functions retain every complete original Arrow square. -/
def callerCofiberNatIso : cofiber.{u, v} ≅ callerCofiberFunctor cc hcc :=
  NatIso.ofComponents (callerCofiberIso cc hcc) (by
    intro F G m
    change cofiber.map m ≫ (callerCofiberIso cc hcc G).hom =
      (callerCofiberIso cc hcc F).hom ≫ callerCofiberMap cc hcc m
    apply PushoutCocone.IsColimit.hom_ext (hc (Q.mapArrow.obj F))
    · change cofiberConeLeg F ≫ (cofiber.map m ≫ (callerCofiberIso cc hcc G).hom) =
        cofiberConeLeg F ≫ ((callerCofiberIso cc hcc F).hom ≫ callerCofiberMap cc hcc m)
      rw [← Category.assoc, cofiberMap_cone]
      rw [Category.assoc, callerCofiberIso_hom_cone, ← Category.assoc,
        callerCofiberIso_hom_cone, callerCofiberMap_cone]
    · change inclusion F ≫ (cofiber.map m ≫ (callerCofiberIso cc hcc G).hom) =
        inclusion F ≫ ((callerCofiberIso cc hcc F).hom ≫ callerCofiberMap cc hcc m)
      rw [← Category.assoc, ← inclusion_naturality, Category.assoc,
        callerCofiberIso_hom_target, ← Category.assoc, callerCofiberIso_hom_target,
        callerCofiberMap_target])

/-- Every full original Arrow map retains the forward caller-choice square. -/
theorem callerCofiberIso_hom_naturality {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    cofiber.map m ≫ (callerCofiberIso cc hcc G).hom =
      (callerCofiberIso cc hcc F).hom ≫ (callerCofiberFunctor cc hcc).map m :=
  (callerCofiberNatIso cc hcc).hom.naturality m

/-- Every full original Arrow map retains the inverse caller-choice square. -/
theorem callerCofiberIso_inv_naturality {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (callerCofiberFunctor cc hcc).map m ≫ (callerCofiberIso cc hcc G).inv =
      (callerCofiberIso cc hcc F).inv ≫ cofiber.map m :=
  (callerCofiberNatIso cc hcc).inv.naturality m

/-- Every degree transports both actual colimit-choice functions on the original integer groups. -/
def callerCofiberIntegerNatIso (q : ℤ) :
    cofiber.{u, v} ⋙ integerStablePiFunctor q ≅
      callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q :=
  Functor.isoWhiskerRight (callerCofiberNatIso cc hcc) (integerStablePiFunctor q)

/-- The whole forward caller integer function is the original map of the actual choice Iso. -/
theorem callerCofiberIntegerNatIso_hom_app (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (callerCofiberIntegerNatIso cc hcc q).hom.app F =
      (integerStablePiFunctor q).map (callerCofiberIso cc hcc F).hom := rfl

/-- The whole inverse caller integer function uses the actual original choice inverse. -/
theorem callerCofiberIntegerNatIso_inv_app (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (callerCofiberIntegerNatIso cc hcc q).inv.app F =
      (integerStablePiFunctor q).map (callerCofiberIso cc hcc F).inv := rfl

/-- The caller inclusion retains the same original Q inverse and the chosen complete target leg. -/
def callerInclusionHo (F : Arrow Carrier.{u, v}) :
    H.obj F.right ⟶ H.obj ((cc F).pt) :=
  (qCounitHoIso F.right).inv ≫ H.map (cc F).inr

/-- The original integer quotient acts on the entire actual caller inclusion. -/
def callerInclusionInteger (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (integerStablePiHoFunctor q).obj (H.obj F.right) ⟶
      (integerStablePiHoFunctor q).obj (H.obj ((cc F).pt)) :=
  (integerStablePiHoFunctor q).map (callerInclusionHo cc F)

/-- The exact chosen target-inclusion map is transported through the actual cofiber choice. -/
theorem callerInclusionHo_original (F : Arrow Carrier.{u, v}) :
    inclusionHo F ≫ H.map (callerCofiberIso cc hcc F).hom = callerInclusionHo cc F := by
  rw [inclusionHo, callerInclusionHo, Category.assoc,
    ← Functor.map_comp, callerCofiberIso_hom_target]

/-- The complete caller inclusion integer function keeps the same Q inverse and original class. -/
theorem callerInclusionInteger_original (q : ℤ) (F : Arrow Carrier.{u, v}) :
    inclusionInteger q F ≫ (callerCofiberIntegerNatIso cc hcc q).hom.app F =
      callerInclusionInteger cc q F := by
  rw [callerCofiberIntegerNatIso_hom_app]
  change (integerStablePiHoFunctor q).map (inclusionHo F) ≫
    (integerStablePiHoFunctor q).map (H.map (callerCofiberIso cc hcc F).hom) = _
  rw [← Functor.map_comp, callerInclusionHo_original]
  rfl

/-- The caller target inclusion is a natural family on every original whole Arrow. -/
def callerInclusionIntegerNatTrans (q : ℤ) :
    Arrow.rightFunc ⋙ integerStablePiFunctor.{u, v} q ⟶
      callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q :=
  inclusionIntegerNatTrans q ≫ (callerCofiberIntegerNatIso cc hcc q).hom

/-- Each caller inclusion component is its same whole original Q/colimit map. -/
theorem callerInclusionIntegerNatTrans_app (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (callerInclusionIntegerNatTrans cc hcc q).app F = callerInclusionInteger cc q F :=
  callerInclusionInteger_original cc hcc q F

variable (s : ∀ X : Carrier.{u, v},
    PushoutCocone (ι.app X) (Diagrams.toZero X))
  (hs : ∀ X, IsColimit (s X))

/-- The caller's forward Q choice keeps the entire actual original suspension cone leg. -/
theorem callerSuspensionIso_Q_cone (X : Carrier.{u, v}) :
    suspensionConeLeg X ≫ (callerSuspensionIso s hs (Q.obj X)).hom = (s (Q.obj X)).inl :=
  callerSuspensionIso_hom_cone s hs (Q.obj X)

/-- The caller's forward Q choice keeps the entire actual original suspension zero leg. -/
theorem callerSuspensionIso_Q_zero (X : Carrier.{u, v}) :
    suspensionZeroLeg X ≫ (callerSuspensionIso s hs (Q.obj X)).hom = (s (Q.obj X)).inr :=
  callerSuspensionIso_hom_zero s hs (Q.obj X)

/-- The caller boundary is the actual desc to the independently chosen original suspension span. -/
def callerBoundary (F : Arrow Carrier.{u, v}) :
    (cc F).pt ⟶ (s (Q.obj F.left)).pt :=
  PushoutCocone.IsColimit.desc (hcc F)
    (s (Q.obj F.left)).inl
    (Diagrams.toZero (Q.obj F.right) ≫ (s (Q.obj F.left)).inr) (by
      rw [(s (Q.obj F.left)).condition, ← Category.assoc, Diagrams.toZero_naturality]
      rfl)

/-- The full caller boundary cone leg is its unchanged original suspension cone leg. -/
theorem callerBoundary_cone (F : Arrow Carrier.{u, v}) :
    (cc F).inl ≫ callerBoundary cc hcc s F = (s (Q.obj F.left)).inl :=
  PushoutCocone.IsColimit.inl_desc (hcc F) _ _ _

/-- The full caller boundary target leg factors through the same actual native zero. -/
theorem callerBoundary_target (F : Arrow Carrier.{u, v}) :
    (cc F).inr ≫ callerBoundary cc hcc s F =
      Diagrams.toZero (Q.obj F.right) ≫ (s (Q.obj F.left)).inr :=
  PushoutCocone.IsColimit.inr_desc (hcc F) _ _ _

/-- Both complete original Arrow components retain the actual caller boundary square. -/
theorem callerBoundary_naturality {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (callerCofiberFunctor cc hcc).map m ≫ callerBoundary cc hcc s G =
      callerBoundary cc hcc s F ≫ (callerISuspensionQFunctor s hs).map m.left := by
  change callerCofiberMap cc hcc m ≫ callerBoundary cc hcc s G =
    callerBoundary cc hcc s F ≫ callerSuspensionMap s hs (Q.map m.left)
  apply PushoutCocone.IsColimit.hom_ext (hcc F)
  · rw [← Category.assoc, callerCofiberMap_cone, Category.assoc,
      callerBoundary_cone, ← Category.assoc, callerBoundary_cone,
      callerSuspensionMap_cone]
  · rw [← Category.assoc, callerCofiberMap_target, Category.assoc,
      callerBoundary_target, ← Category.assoc, Diagrams.toZero_naturality,
      ← Category.assoc, callerBoundary_target, Category.assoc, callerSuspensionMap_zero]

/-- The complete caller boundary family retains its original Q source map and both choice legs. -/
def callerBoundaryNatTrans :
    callerCofiberFunctor cc hcc ⟶ Arrow.leftFunc ⋙ callerISuspensionQFunctor s hs where
  app F := callerBoundary cc hcc s F
  naturality _ _ m := callerBoundary_naturality cc hcc s hs m

/-- Actual colimit uniqueness compares the entire original boundary with both caller choices. -/
theorem callerBoundary_original_square (F : Arrow Carrier.{u, v}) :
    boundary F ≫ (callerSuspensionIso s hs (Q.obj F.left)).hom =
      (callerCofiberIso cc hcc F).hom ≫ callerBoundary cc hcc s F := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Q.mapArrow.obj F))
  · change cofiberConeLeg F ≫
      (boundary F ≫ (callerSuspensionIso s hs (Q.obj F.left)).hom) =
        cofiberConeLeg F ≫ ((callerCofiberIso cc hcc F).hom ≫ callerBoundary cc hcc s F)
    rw [← Category.assoc, cofiberConeLeg_boundary, callerSuspensionIso_Q_cone,
      ← Category.assoc, callerCofiberIso_hom_cone, callerBoundary_cone]
  · change inclusion F ≫
      (boundary F ≫ (callerSuspensionIso s hs (Q.obj F.left)).hom) =
        inclusion F ≫ ((callerCofiberIso cc hcc F).hom ≫ callerBoundary cc hcc s F)
    rw [← Category.assoc, originalInclusionBoundary, Category.assoc,
      callerSuspensionIso_Q_zero, ← Category.assoc, callerCofiberIso_hom_target,
      callerBoundary_target]

/-- The actual caller-boundary word normalizes to the same entire original chosen boundary. -/
theorem callerBoundary_original_normalization (F : Arrow Carrier.{u, v}) :
    (callerCofiberIso cc hcc F).hom ≫ callerBoundary cc hcc s F ≫
      (callerSuspensionIso s hs (Q.obj F.left)).inv = boundary F := by
  rw [← Category.assoc, ← callerBoundary_original_square,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The two actual choice functions normalize the entire boundary integer family. -/
theorem callerBoundaryInteger_original_normalization (q : ℤ) :
    (callerCofiberIntegerNatIso cc hcc q).hom ≫
        Functor.whiskerRight (callerBoundaryNatTrans cc hcc s hs) (integerStablePiFunctor q) ≫
          (Functor.associator Arrow.leftFunc (callerISuspensionQFunctor s hs)
            (integerStablePiFunctor q)).hom ≫
              Functor.whiskerLeft Arrow.leftFunc (callerIQIntegerChoiceNatIso s hs q).inv =
      Functor.whiskerRight originalBoundaryNatTrans (integerStablePiFunctor q) ≫
        (Functor.associator Arrow.leftFunc originalISuspensionQFunctor
          (integerStablePiFunctor q)).hom := by
  apply NatTrans.ext
  funext F
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [callerCofiberIntegerNatIso_hom_app, callerIQIntegerChoiceNatIso_inv_app]
  change (integerStablePiFunctor q).map (callerCofiberIso cc hcc F).hom ≫
      (integerStablePiFunctor q).map (callerBoundary cc hcc s F) ≫
        𝟙 _ ≫ (integerStablePiFunctor q).map
          (callerSuspensionIso s hs (Q.obj F.left)).inv =
    (integerStablePiFunctor q).map (boundary F) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp,
    callerBoundary_original_normalization]

/-- Caller connecting maps use the same chosen boundary and proved full I-Q inverse. -/
def callerConnectingPlusOneNatTrans (q : ℤ) :
    callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor (q + 1) ⟶
      Arrow.leftFunc ⋙ integerStablePiFunctor q :=
  Functor.whiskerRight (callerBoundaryNatTrans cc hcc s hs) (integerStablePiFunctor (q + 1)) ≫
    (Functor.associator Arrow.leftFunc (callerISuspensionQFunctor s hs)
      (integerStablePiFunctor (q + 1))).hom ≫
        Functor.whiskerLeft Arrow.leftFunc (integerCallerISuspensionPiNatIso s hs q).inv

/-- Every actual caller component is its complete original chosen-boundary connecting function. -/
def callerConnectingPlusOne (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor (q + 1)).obj F ⟶
      (integerStablePiFunctor q).obj F.left :=
  (callerConnectingPlusOneNatTrans cc hcc s hs q).app F

/-- Every class retains the complete caller boundary and its proved original I-Q inverse. -/
theorem callerConnectingPlusOne_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor (q + 1)).obj F) :
    (callerConnectingPlusOne cc hcc s hs q F).hom a =
      ((integerCallerISuspensionPiNatIso s hs q).inv.app F.left).hom
        (((integerStablePiFunctor (q + 1)).map (callerBoundary cc hcc s F)).hom a) := by
  dsimp only [callerConnectingPlusOne, callerConnectingPlusOneNatTrans, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, callerBoundaryNatTrans,
    Functor.associator]
  rfl

/-- The forward cofiber choice recovers the entire original connecting family. -/
theorem callerConnectingPlusOne_original (q : ℤ) :
    (callerCofiberIntegerNatIso cc hcc (q + 1)).hom ≫
        callerConnectingPlusOneNatTrans cc hcc s hs q = connectingPlusOneNatTrans q := by
  dsimp only [callerConnectingPlusOneNatTrans]
  rw [integerCallerISuspensionPiNatIso_inv, Functor.whiskerLeft_comp]
  have h := callerBoundaryInteger_original_normalization cc hcc s hs (q + 1)
  dsimp only [connectingPlusOneNatTrans]
  simp only [← Category.assoc] at h ⊢
  rw [h]

/-- The inverse cofiber choice retains the entire original connecting family
in the other direction. -/
theorem callerConnectingPlusOne_inverse_original (q : ℤ) :
    callerConnectingPlusOneNatTrans cc hcc s hs q =
      (callerCofiberIntegerNatIso cc hcc (q + 1)).inv ≫ connectingPlusOneNatTrans q := by
  rw [← callerConnectingPlusOne_original cc hcc s hs q,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- All independent caller choices preserve the exact class of the original connecting map. -/
theorem callerConnectingPlusOne_original_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F)) :
    (callerConnectingPlusOne cc hcc s hs q F).hom
        (((callerCofiberIntegerNatIso cc hcc (q + 1)).hom.app F).hom a) =
      (connectingPlusOne q F).hom a :=
  ConcreteCategory.congr_hom (congr_app
    (callerConnectingPlusOne_original cc hcc s hs q) F) a

/-- The original whole cofiber choice commutes with the complete predecessor degree transport. -/
theorem callerCofiberInteger_degree_naturality (q : ℤ) :
    (callerCofiberIntegerNatIso cc hcc q).hom ≫
        Functor.whiskerLeft (callerCofiberFunctor cc hcc) (predecessorDegreeNatIso q).hom =
      Functor.whiskerLeft cofiber (predecessorDegreeNatIso q).hom ≫
        (callerCofiberIntegerNatIso cc hcc ((q - 1) + 1)).hom :=
  (Functor.whiskerLeft_comp_whiskerRight (callerCofiberNatIso cc hcc).hom
    (predecessorDegreeNatIso q).hom).symm

/-- The caller's full canonical connecting family retains its actual integer predecessor
transport. -/
def callerConnectingNatTrans (q : ℤ) :
    callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q ⟶
      Arrow.leftFunc ⋙ integerStablePiFunctor (q - 1) :=
  Functor.whiskerLeft (callerCofiberFunctor cc hcc) (predecessorDegreeNatIso q).hom ≫
    callerConnectingPlusOneNatTrans cc hcc s hs (q - 1)

/-- The actual canonical caller component retains its entire boundary,
inverse and degree maps. -/
def callerConnecting (q : ℤ) (F : Arrow Carrier.{u, v}) :
    (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q).obj F ⟶
      (integerStablePiFunctor (q - 1)).obj F.left :=
  (callerConnectingNatTrans cc hcc s hs q).app F

/-- The complete original Arrow square retains both caller boundary endpoints in every degree. -/
theorem callerConnecting_naturality (q : ℤ) {F G : Arrow Carrier.{u, v}} (m : F ⟶ G) :
    (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q).map m ≫
        callerConnecting cc hcc s hs q G =
      callerConnecting cc hcc s hs q F ≫ (integerStablePiFunctor (q - 1)).map m.left :=
  (callerConnectingNatTrans cc hcc s hs q).naturality m

/-- Forward caller transport preserves the entire original all-integer connecting map. -/
theorem callerConnecting_original (q : ℤ) :
    (callerCofiberIntegerNatIso cc hcc q).hom ≫
        callerConnectingNatTrans cc hcc s hs q = connectingNatTrans q := by
  dsimp only [callerConnectingNatTrans]
  rw [← Category.assoc, callerCofiberInteger_degree_naturality,
    Category.assoc, callerConnectingPlusOne_original]
  rfl

/-- Inverse caller transport preserves the same all-integer connecting map and source Arrow. -/
theorem callerConnecting_inverse_original (q : ℤ) :
    callerConnectingNatTrans cc hcc s hs q =
      (callerCofiberIntegerNatIso cc hcc q).inv ≫ connectingNatTrans q := by
  rw [← callerConnecting_original cc hcc s hs q, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Every raw original class is sent by the same canonical connecting map through both choices. -/
theorem callerConnecting_original_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj (cofiber.obj F)) :
    (callerConnecting cc hcc s hs q F).hom
        (((callerCofiberIntegerNatIso cc hcc q).hom.app F).hom a) =
      (connecting q F).hom a :=
  ConcreteCategory.congr_hom (congr_app (callerConnecting_original cc hcc s hs q) F) a

/-- Every actual caller class retains the original connecting map
through the full choice inverse. -/
theorem callerConnecting_inverse_original_apply (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q).obj F) :
    (callerConnecting cc hcc s hs q F).hom a =
      (connecting q F).hom (((callerCofiberIntegerNatIso cc hcc q).inv.app F).hom a) :=
  ConcreteCategory.congr_hom (congr_app
    (callerConnecting_inverse_original cc hcc s hs q) F) a

/-- The complete caller source/inclusion composite is the original actual group null function. -/
theorem caller_source_inclusion_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj F.left) :
    (callerInclusionInteger cc q F).hom (((integerStablePiFunctor q).map F.hom).hom a) = 1 := by
  rw [callerInclusionInteger, callerInclusionHo, Functor.map_comp,
    integerStablePiHoFunctor_map, qCounitHoIso_integer_inverse]
  change ((integerStablePiFunctor q).map (cc F).inr).hom
    (((qCounitIntegerNatIso q).inv.app F.right).hom
      (((integerStablePiFunctor q).map F.hom).hom a)) = 1
  have h := ConcreteCategory.congr_hom ((qCounitIntegerNatIso q).inv.naturality F.hom) a
  change ((qCounitIntegerNatIso q).inv.app F.right).hom
      (((integerStablePiFunctor q).map F.hom).hom a) =
    ((integerStablePiFunctor q).map (Q.map F.hom)).hom
      (((qCounitIntegerNatIso q).inv.app F.left).hom a) at h
  rw [h]
  change ((integerStablePiFunctor q).map (Q.map F.hom) ≫
    (integerStablePiFunctor q).map (cc F).inr).hom
      (((qCounitIntegerNatIso q).inv.app F.left).hom a) = 1
  rw [← Functor.map_comp, ← (cc F).condition]
  exact integerMap_through_original_cone_apply q _ _ _

/-- The caller inclusion/connecting composite is null in every literal integer degree. -/
theorem caller_inclusion_connecting_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj F.right) :
    (callerConnecting cc hcc s hs q F).hom
      (((callerInclusionIntegerNatTrans cc hcc q).app F).hom a) = 1 := by
  change (callerConnecting cc hcc s hs q F).hom
    (((callerCofiberIntegerNatIso cc hcc q).hom.app F).hom
      (((inclusionIntegerNatTrans q).app F).hom a)) = 1
  rw [callerConnecting_original_apply]
  exact inclusion_connecting_null q F a

/-- The caller connecting/source composite retains the full original null class and Q inverse. -/
theorem caller_connecting_source_null (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q).obj F) :
    ((integerStablePiFunctor (q - 1)).map F.hom).hom
      ((callerConnecting cc hcc s hs q F).hom a) = 1 := by
  rw [callerConnecting_inverse_original_apply]
  exact connecting_source_null q F _

end CallerCofiber

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberConnectingIntegerPiGeometry
