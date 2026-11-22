/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenCofiberHom

/-!
# Full caller cofiber Puppe sequences and original boundary transport

Every caller cofiber family and its colimit witnesses supply their actual
entire Puppe stage functors. All original Q suspension sources, scalar
target shifts and Puppe stages are unbounded. The original restriction,
source and target functions are exact before any stable model is built.
The original boundary and both selected suspension endpoints retain the
same full cofiber choice isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ChosenCofiberSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ShiftedHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenCofiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev cone := OriginalICone.cone (B := B) (I := O.{u, v})
private abbrev inclusion := OriginalICone.inclusion (B := B) (I := O.{u, v})
private abbrev canonicalCone := OriginalISuspension.cocone (B := B) (I := O.{u, v})
private abbrev canonicalLimit := OriginalISuspension.coconeIsColimit (B := B) (I := O.{u, v})
private abbrev canonicalSuspension := OriginalISuspension.suspension (B := B) (I := O.{u, v})
private abbrev sourceSuspension (s : ℕ) :=
  NativeK.FiberHomTests.originalQSuspensionIterate (B := B) (I := O.{u, v}) s

variable (d : ∀ F : Arrow C.{u, v}, PushoutCocone (inclusion.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

/-- Every whole original Q suspension Arrow and each caller's chosen
Puppe stage retain their unchanged native source functions. -/
def stage (s n : ℕ) : Arrow C.{u, v} ⥤ Arrow C.{u, v} :=
  (sourceSuspension s).mapArrow ⋙
    OrdinaryHoChosenPuppeHomSequence.stageFunctor cone inclusion d hd n

/-- The full original carrier at each caller's selected stage is retained. -/
def term (s n : ℕ) : Arrow C.{u, v} ⥤ C.{u, v} := stage d hd s n ⋙ Arrow.leftFunc

/-- Each source suspension, caller stage and scalar target shift uses
the actual ordinary level homotopy Hom set. -/
abbrev homTerm (r s n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :=
  H.obj ((term d hd s n).obj F) ⟶ H.obj ((loopTarget r).obj E)

/-- Each complete restriction is the original caller's Puppe map. -/
def restriction (r s n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    homTerm d hd r s (n + 1) F E → homTerm d hd r s n F E :=
  OrdinaryHoChosenPuppeHomSequence.restriction cone inclusion d hd n
    ((sourceSuspension s).mapArrow.obj F) ((loopTarget r).obj E)

/-- The entire original native Arrow map acts by the actual source
suspension and unchanged caller's Puppe transformation. -/
def sourceAction (r s n : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G) (E : C.{u, v}) :
    homTerm d hd r s n G E → homTerm d hd r s n F E :=
  OrdinaryHoChosenPuppeHomSequence.sourceAction cone inclusion d hd n
    ((sourceSuspension s).mapArrow.map q) ((loopTarget r).obj E)

/-- Every whole target map retains the same actual scalar loop shift. -/
def targetAction (r s n : ℕ) (F : Arrow C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E') :
    homTerm d hd r s n F E → homTerm d hd r s n F E' :=
  OrdinaryHoChosenPuppeHomSequence.targetAction cone inclusion d hd n
    ((sourceSuspension s).mapArrow.obj F) ((loopTarget r).map t)

/-- Every original full source transformation commutes with every
chosen restriction in all source and target shifts. -/
theorem restriction_source (r s n : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G) (E : C.{u, v}) :
    restriction d hd r s n F E ∘ sourceAction d hd r s (n + 1) q E =
      sourceAction d hd r s n q E ∘ restriction d hd r s n G E :=
  OrdinaryHoChosenPuppeHomSequence.restriction_source cone inclusion d hd n
    ((sourceSuspension s).mapArrow.map q) ((loopTarget r).obj E)

/-- Every whole scalar-shifted target map commutes with the original
chosen Puppe restriction functions. -/
theorem restriction_target (r s n : ℕ) (F : Arrow C.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') :
    restriction d hd r s n F E' ∘ targetAction d hd r s (n + 1) F t =
      targetAction d hd r s n F t ∘ restriction d hd r s n F E :=
  OrdinaryHoChosenPuppeHomSequence.restriction_target cone inclusion d hd n
    ((sourceSuspension s).mapArrow.obj F) ((loopTarget r).map t)

private theorem coneCollapse_weak (X : C.{u, v}) :
    weakEquivalences C.{u, v}
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

/-- The actual chosen Puppe sequence is exact at every stage, for every
original Q suspension source and full scalar-shifted target. -/
theorem exact_at (r s n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : homTerm d hd r s (n + 1) F E) :
    (∃ h : homTerm d hd r s (n + 2) F E, restriction d hd r s (n + 1) F E h = g) ↔
      restriction d hd r s n F E g =
        OrdinaryHoCofiberKernel.nullHom ((term d hd s n).obj F) ((loopTarget r).obj E) := by
  let _ : IsCofibrant ((sourceSuspension s).mapArrow.obj F).left :=
    NativeK.FiberHomTests.originalQSuspensionIterate_obj_cofibrant (B := B) s F.left
  let _ : IsCofibrant ((sourceSuspension s).mapArrow.obj F).right :=
    NativeK.FiberHomTests.originalQSuspensionIterate_obj_cofibrant (B := B) s F.right
  let _ : IsFibrant ((loopTarget r).obj E) := allObjectsFibrant _
  exact OrdinaryHoChosenPuppeHomSequence.exact_at
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone inclusion d hd
    (fun X _ => OriginalICone.inclusion_cofibration X) (fun X _ => coneCollapse_weak X)
      n ((sourceSuspension s).mapArrow.obj F) ((loopTarget r).obj E) g

/-- The caller's chosen cofiber family gives the actual original
suspension on the same unchanged zero-arrow sources. -/
def chosenSuspension : C.{u, v} ⥤ C.{u, v} :=
  OrdinaryHoChosenPuppe.suspensionFunctor cone inclusion d hd
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero

/-- Both complete original suspension endpoint maps retain every
native source and the same cofiber choice functions. -/
def suspensionChoiceIso : canonicalSuspension ≅ chosenSuspension d hd :=
  OrdinaryHoChosenFiberCofiberComparison.suspensionChoiceNatIso
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone inclusion
      canonicalCone canonicalLimit d hd

/-- The entire original caller boundary retains the same chosen
cofiber and suspension endpoints at each original source suspension. -/
def boundary (s : ℕ) (F : Arrow C.{u, v}) :
    (chosenCofiber d hd s).obj F ⟶ (chosenSuspension d hd).obj ((sourceSuspension s).obj F.left) :=
  OrdinaryHoChosenPuppe.boundary cone inclusion d hd
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((sourceSuspension s).mapArrow.obj F)

/-- Every entire original native Arrow square retains the same caller's
cofiber and suspension boundary maps. -/
theorem boundary_naturality (s : ℕ) {F G : Arrow C.{u, v}} (q : F ⟶ G) :
    (chosenCofiber d hd s).map q ≫ boundary d hd s G =
      boundary d hd s F ≫ (chosenSuspension d hd).map ((sourceSuspension s).map q.left) :=
  OrdinaryHoChosenPuppe.boundary_naturality cone inclusion d hd
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((sourceSuspension s).mapArrow.map q)

/-- The complete actual caller's boundary is one whole natural
transformation on the unchanged original native Arrow category. -/
def boundaryNatTrans (s : ℕ) : chosenCofiber d hd s ⟶
    Arrow.leftFunc ⋙ sourceSuspension s ⋙ chosenSuspension d hd where
  app F := boundary d hd s F
  naturality {_F _G} q := boundary_naturality d hd s q

/-- The full canonical and caller boundaries retain both original
choice maps at the entire source and target endpoints. -/
theorem boundary_choice (s : ℕ) (F : Arrow C.{u, v}) :
    (chosenCofiberIso d hd s).hom.app F ≫ boundary d hd s F =
      OrdinaryHoChosenPuppe.boundary cone inclusion canonicalCone canonicalLimit
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((sourceSuspension s).mapArrow.obj F) ≫
          (suspensionChoiceIso d hd).hom.app ((sourceSuspension s).obj F.left) :=
  OrdinaryHoChosenFiberCofiberComparison.boundary_cofiberChoice
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero cone inclusion
      canonicalCone canonicalLimit d hd ((sourceSuspension s).mapArrow.obj F)

/-- Both entire boundary arrows are transported by the original full
choice isomorphisms, rather than by a replacement of either caller cone. -/
def boundaryArrowIso (s : ℕ) (F : Arrow C.{u, v}) :
    Arrow.mk (OrdinaryHoChosenPuppe.boundary cone inclusion canonicalCone canonicalLimit
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((sourceSuspension s).mapArrow.obj F)) ≅
      Arrow.mk (boundary d hd s F) :=
  Arrow.isoMk ((chosenCofiberIso d hd s).app F)
    ((suspensionChoiceIso d hd).app ((sourceSuspension s).obj F.left)) (boundary_choice d hd s F)

/-- Both entire inverse boundary endpoint maps retain the same original
canonical boundary in the opposite direction. -/
theorem boundary_choice_inv (s : ℕ) (F : Arrow C.{u, v}) :
    (chosenCofiberIso d hd s).inv.app F ≫
        OrdinaryHoChosenPuppe.boundary cone inclusion canonicalCone canonicalLimit
          Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((sourceSuspension s).mapArrow.obj F) =
      boundary d hd s F ≫
        (suspensionChoiceIso d hd).inv.app ((sourceSuspension s).obj F.left) :=
  (boundaryArrowIso d hd s F).inv.w

/-- Both full original chosen-suspension endpoint functions induce the
actual shifted Hom comparison. -/
def suspensionHomChoiceEquiv (r : ℕ) (X E : C.{u, v}) :
    (H.obj ((chosenSuspension d hd).obj X) ⟶ H.obj ((loopTarget r).obj E)) ≃
      (H.obj (canonicalSuspension.obj X) ⟶ H.obj ((loopTarget r).obj E)) :=
  Iso.homCongr ((H.mapIso ((suspensionChoiceIso d hd).app X)).symm) (Iso.refl _)

/-- The complete forward shifted Hom function is the original
chosen-suspension comparison map. -/
theorem suspensionHomChoiceEquiv_apply (r : ℕ) (X E : C.{u, v})
    (g : H.obj ((chosenSuspension d hd).obj X) ⟶ H.obj ((loopTarget r).obj E)) :
    suspensionHomChoiceEquiv d hd r X E g = H.map ((suspensionChoiceIso d hd).hom.app X) ≫ g := by
  simp only [suspensionHomChoiceEquiv, Iso.homCongr_apply, Iso.symm_inv, Functor.mapIso_hom,
    Iso.app_hom, Iso.refl_hom, Category.comp_id]

/-- The actual original boundary restriction retains both entire
choice comparison functions on every shifted Hom test. -/
theorem boundaryHom_choice (r s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : H.obj ((chosenSuspension d hd).obj ((sourceSuspension s).obj F.left)) ⟶
      H.obj ((loopTarget r).obj E)) :
    chosenHomEquiv d hd r s F E (H.map (boundary d hd s F) ≫ g) =
      H.map (OrdinaryHoChosenPuppe.boundary cone inclusion canonicalCone canonicalLimit
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero ((sourceSuspension s).mapArrow.obj F)) ≫
          suspensionHomChoiceEquiv d hd r ((sourceSuspension s).obj F.left) E g := by
  rw [chosenHomEquiv_apply, suspensionHomChoiceEquiv_apply, ← Category.assoc,
    ← H.map_comp, boundary_choice, H.map_comp, Category.assoc]

end PointedCGWH.Spectra.Orthogonal.ChosenCofiberSequence
