/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerTargets
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenCofiberSequence

/-!
# Original orthogonal Puppe tests in every integer target degree

Every caller's actual cofiber and suspension use its original colimit
witnesses. All original Q suspension sources and Puppe stages retain
their complete native maps. The three original source, cofiber-target and
boundary/suspension restriction functions are exact at every integer
target. The full original weak tests make every caller cofiber term null
in all these degrees. No fiber comparison or stable model is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ShiftedPuppeExactness

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev cone := OriginalICone.cone (B := B) (I := O.{u, v})
private abbrev inclusion := OriginalICone.inclusion (B := B) (I := O.{u, v})
private abbrev sourceSuspension (s : ℕ) :=
  NativeK.FiberHomTests.originalQSuspensionIterate (B := B) (I := O.{u, v}) s
private abbrev sourceArrow (s : ℕ) (F : Arrow C.{u, v}) := (sourceSuspension s).mapArrow.obj F

variable (d : ∀ F : Arrow C.{u, v}, PushoutCocone (inclusion.app F.left) F.hom)
  (hd : ∀ F, IsColimit (d F))

/-- Every caller Puppe stage has its actual full Hom test in every integer target degree. -/
abbrev testTerm (q : ℤ) (s n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :=
  H.obj ((ChosenCofiberSequence.term d hd s n).obj F) ⟶ H.obj ((integerTarget q).obj E)

/-- The original caller restriction retains the unchanged entire native Puppe arrow. -/
def restriction (q : ℤ) (s n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    testTerm d hd q s (n + 1) F E → testTerm d hd q s n F E :=
  ChosenCofiberSequence.restriction d hd 0 s n F ((integerTarget q).obj E)

/-- Every whole original Arrow square retains its original Q suspension and caller stage action. -/
def sourceAction (q : ℤ) (s n : ℕ) {F G : Arrow C.{u, v}} (a : F ⟶ G) (E : C.{u, v}) :
    testTerm d hd q s n G E → testTerm d hd q s n F E :=
  ChosenCofiberSequence.sourceAction d hd 0 s n a ((integerTarget q).obj E)

/-- Every full original target map acts through its actual integer target functor. -/
def targetAction (q : ℤ) (s n : ℕ) (F : Arrow C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E') :
    testTerm d hd q s n F E → testTerm d hd q s n F E' :=
  ChosenCofiberSequence.targetAction d hd 0 s n F ((integerTarget q).map t)

/-- Every complete original source action commutes with every integer restriction map. -/
theorem restriction_source (q : ℤ) (s n : ℕ) {F G : Arrow C.{u, v}}
    (a : F ⟶ G) (E : C.{u, v}) :
    restriction d hd q s n F E ∘ sourceAction d hd q s (n + 1) a E =
      sourceAction d hd q s n a E ∘ restriction d hd q s n G E :=
  ChosenCofiberSequence.restriction_source d hd 0 s n a ((integerTarget q).obj E)

/-- Every original integer target action retains the complete caller restriction square. -/
theorem restriction_target (q : ℤ) (s n : ℕ) (F : Arrow C.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') :
    restriction d hd q s n F E' ∘ targetAction d hd q s (n + 1) F t =
      targetAction d hd q s n F t ∘ restriction d hd q s n F E :=
  ChosenCofiberSequence.restriction_target d hd 0 s n F ((integerTarget q).map t)

/-- Every actual caller Puppe stage is exact in every original integer target degree. -/
theorem exact_at (q : ℤ) (s n : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : testTerm d hd q s (n + 1) F E) :
    (∃ h : testTerm d hd q s (n + 2) F E, restriction d hd q s (n + 1) F E h = g) ↔
      restriction d hd q s n F E g =
        OrdinaryHoCofiberKernel.nullHom ((ChosenCofiberSequence.term d hd s n).obj F)
          ((integerTarget q).obj E) :=
  ChosenCofiberSequence.exact_at d hd 0 s n F ((integerTarget q).obj E) g

/-- Every actual cofiber term retains the caller's unchanged original carrier. -/
abbrev cofiberTerm (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :=
  H.obj ((ChosenCofiberHom.chosenCofiber d hd s).obj F) ⟶ H.obj ((integerTarget q).obj E)

/-- The original source restriction is the original full Q-suspension map of the caller arrow. -/
def sourceRestriction (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    (H.obj (sourceArrow s F).right ⟶ H.obj ((integerTarget q).obj E)) →
      (H.obj (sourceArrow s F).left ⟶ H.obj ((integerTarget q).obj E)) :=
  fun g => H.map (sourceArrow s F).hom ≫ g

/-- The cofiber target restriction retains the actual caller's original target leg. -/
def targetRestriction (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    cofiberTerm d hd q s F E →
      (H.obj (sourceArrow s F).right ⟶ H.obj ((integerTarget q).obj E)) :=
  fun g => H.map (d (sourceArrow s F)).inr ≫ g

/-- Every original chosen suspension Hom term uses the same caller's actual suspension carrier. -/
abbrev suspensionTerm (q : ℤ) (s : ℕ) (X E : C.{u, v}) :=
  H.obj ((ChosenCofiberSequence.chosenSuspension d hd).obj ((sourceSuspension s).obj X)) ⟶
    H.obj ((integerTarget q).obj E)

/-- The complete connecting restriction is the actual original caller boundary. -/
def boundaryRestriction (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    suspensionTerm d hd q s F.left E → cofiberTerm d hd q s F E :=
  fun g => H.map (ChosenCofiberSequence.boundary d hd s F) ≫ g

/-- The original unsigned suspension restriction retains the full native Q source map. -/
def suspensionRestriction (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    suspensionTerm d hd q s F.right E → suspensionTerm d hd q s F.left E :=
  fun g => H.map ((ChosenCofiberSequence.chosenSuspension d hd).map
    ((sourceSuspension s).map F.hom)) ≫ g

private theorem sourceCofibrant (s : ℕ) (X : C.{u, v}) :
    IsCofibrant ((sourceSuspension s).obj X) :=
  NativeK.FiberHomTests.originalQSuspensionIterate_obj_cofibrant (B := B) s X

private theorem coneCofibration (X : C.{u, v}) : Cofibration (inclusion.app X) :=
  (HomotopicalAlgebra.cofibration_iff (inclusion.app X)).mpr
    (OriginalICone.inclusion_cofibration X)

private theorem nativeFibrant (X : C.{u, v}) : IsFibrant X := allObjectsFibrant X

attribute [local instance] sourceCofibrant coneCofibration nativeFibrant

private theorem coneCollapse_weak (X : C.{u, v}) :
    weakEquivalences C.{u, v}
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

/-- The original cofiber-target image equals the original source null kernel in every degree. -/
theorem first_exact (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : H.obj (sourceArrow s F).right ⟶ H.obj ((integerTarget q).obj E)) :
    (∃ h : cofiberTerm d hd q s F E, targetRestriction d hd q s F E h = g) ↔
      sourceRestriction q s F E g =
        OrdinaryHoCofiberKernel.nullHom (sourceArrow s F).left ((integerTarget q).obj E) := by
  let _ : IsCofibrant (sourceArrow s F).left := sourceCofibrant s F.left
  let _ : IsCofibrant (sourceArrow s F).right := sourceCofibrant s F.right
  exact OrdinaryHoChosenPuppe.first_exact Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
    cone inclusion d hd (sourceArrow s F) ((integerTarget q).obj E)
      (coneCollapse_weak (sourceArrow s F).left) g

/-- The actual boundary image equals the same caller's target-restriction null kernel. -/
theorem second_exact (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : cofiberTerm d hd q s F E) :
    (∃ h : suspensionTerm d hd q s F.left E, boundaryRestriction d hd q s F E h = g) ↔
      targetRestriction d hd q s F E g =
        OrdinaryHoCofiberKernel.nullHom (sourceArrow s F).right ((integerTarget q).obj E) := by
  let _ : IsCofibrant (sourceArrow s F).right := sourceCofibrant s F.right
  exact OrdinaryHoChosenPuppe.second_exact Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
    cone inclusion d hd (sourceArrow s F) ((integerTarget q).obj E) g

/-- The same original unsigned suspension image equals the actual boundary null kernel. -/
theorem third_exact (q : ℤ) (s : ℕ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : suspensionTerm d hd q s F.left E) :
    (∃ h : suspensionTerm d hd q s F.right E, suspensionRestriction d hd q s F E h = g) ↔
      boundaryRestriction d hd q s F E g =
        OrdinaryHoCofiberKernel.nullHom ((ChosenCofiberHom.chosenCofiber d hd s).obj F)
          ((integerTarget q).obj E) := by
  let _ : IsCofibrant (sourceArrow s F).right := sourceCofibrant s F.right
  exact OrdinaryHoChosenPuppeHomSequence.third_exact
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
    cone inclusion d hd (sourceArrow s F) ((integerTarget q).obj E)
      (coneCollapse_weak (sourceArrow s F).right) g

/-- Every integer target test of the same original caller cofiber is its actual null class. -/
theorem cofiberHom_eq_null {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests orthogonalFamily f) (q : ℤ) (s : ℕ)
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberTerm d hd q s (Arrow.mk f) E) :
    g = OrdinaryHoCofiberKernel.nullHom
      ((ChosenCofiberHom.chosenCofiber d hd s).obj (Arrow.mk f)) ((integerTarget q).obj E) :=
  ChosenCofiberHom.chosenHom_eq_null d hd f hf 0 s ((integerTarget q).obj E)
    (integerTarget_isOmega q E hE) g

end PointedCGWH.Spectra.Orthogonal.ShiftedPuppeExactness
