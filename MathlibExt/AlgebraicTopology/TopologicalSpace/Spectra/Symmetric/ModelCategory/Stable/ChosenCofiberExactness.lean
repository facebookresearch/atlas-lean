/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.Stable.ShiftedPuppeExactness
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison

/-!
# All chosen symmetric Q-cofibers retain the original shifted Hom sequence

The caller supplies actual pushout cocones for the original I-cone
inclusions and a colimit proof for every cocone. Both original legs
construct the cofiber comparison. Its two functions retain all original
Arrow maps. The caller's boundary is transported through the actual
suspension-cofiber comparison, so the scalar and delta shift functions
continue to use the original suspension.

The full integer sequence, all three exactness positions and cofiber
nullity are transported to these unchanged caller objects and maps.
Exactness, nullity and a stable model are conclusions of their respective
proofs, rather than fields of a supplied result dictionary.

This is the chosen-cofiber part of MMSS, *Model categories of diagram
spectra*, December 30, 1999 manuscript, Theorem 8.12(vi), pages 27–28.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open OrdinaryHoChosenFiberCofiberComparison
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.Stable.ChosenCofiberTests

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev Index := PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant


variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B)
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev ISusp := OriginalISuspension.suspension (B := B)
  (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev QF (F : Arrow C.{u, v}) := Q.mapArrow.obj F
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B)
  (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev qIso (X : C.{u, v}) :=
  NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X

local notation "cone" => OriginalICone.cone (B := B)
  (I := Index)
local notation "ι" => OriginalICone.inclusion (B := B)
  (I := Index)
local notation "c" => OriginalISuspension.cocone (B := B)
  (I := Index)
local notation "hc" => OriginalISuspension.coconeIsColimit (B := B)
  (I := Index)

private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

private abbrev CofiberChoices :=
  ∀ F : Arrow C.{u, v}, PushoutCocone ((ι).app F.left) F.hom

/-- The whole original Q arrow enters the caller's same chosen cofiber functor. -/
def chosenCofiber
    (chosen : ∀ F : Arrow C.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := Index)).app F.left) F.hom)
    (chosenIsColimit : ∀ F, IsColimit (chosen F)) : Arrow C.{u, v} ⥤ C.{u, v} :=
  Q.mapArrow ⋙ OrdinaryHoChosenPuppe.cofiberFunctor
    (OriginalICone.cone (B := B) (I := Index))
    (OriginalICone.inclusion (B := B) (I := Index)) chosen chosenIsColimit

/-- The output is the caller's unchanged cofiber point of the whole original Q arrow. -/
theorem chosenCofiber_obj
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    (chosenCofiber (B := B) d hd).obj F = (d (QF F)).pt := rfl

/-- Every output map is the caller's original chosen-cofiber universal map. -/
theorem chosenCofiber_map
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) {F G : Arrow C.{u, v}} (φ : F ⟶ G) :
    (chosenCofiber (B := B) d hd).map φ =
      OrdinaryHoChosenPuppe.cofiberMap cone ι d hd (Q.mapArrow.map φ) := rfl

/-- Both actual colimit proofs construct the complete original-to-chosen cofiber isomorphism. -/
def choiceNatIso
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) :
    CQ.{u, v} ≅ chosenCofiber (B := B) d hd :=
  Functor.isoWhiskerLeft Q.mapArrow (cofiberChoiceNatIso cone ι c hc d hd)

/-- The forward comparison retains the caller's entire original cone leg. -/
theorem choiceNatIso_hom_cone
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    (c (QF F)).inl ≫ (choiceNatIso (B := B) d hd).hom.app F = (d (QF F)).inl :=
  cofiberChoiceIso_hom_cone cone ι c hc d hd (QF F)

/-- The forward comparison retains the caller's entire original target leg. -/
theorem choiceNatIso_hom_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    (c (QF F)).inr ≫ (choiceNatIso (B := B) d hd).hom.app F = (d (QF F)).inr :=
  cofiberChoiceIso_hom_target cone ι c hc d hd (QF F)

/-- The inverse comparison recovers the same complete original cone leg. -/
theorem choiceNatIso_inv_cone
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    (d (QF F)).inl ≫ (choiceNatIso (B := B) d hd).inv.app F = (c (QF F)).inl :=
  cofiberChoiceIso_inv_cone cone ι c hc d hd (QF F)

/-- The inverse comparison recovers the same complete original target leg. -/
theorem choiceNatIso_inv_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    (d (QF F)).inr ≫ (choiceNatIso (B := B) d hd).inv.app F = (c (QF F)).inr :=
  cofiberChoiceIso_inv_target cone ι c hc d hd (QF F)

/-- Every whole original Arrow square retains the complete caller's cofiber map. -/
theorem choiceNatIso_naturality
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) {F G : Arrow C.{u, v}} (φ : F ⟶ G) :
    CQ.map φ ≫ (choiceNatIso (B := B) d hd).hom.app G =
      (choiceNatIso (B := B) d hd).hom.app F ≫ (chosenCofiber (B := B) d hd).map φ :=
  (choiceNatIso (B := B) d hd).hom.naturality φ

/-- The actual original target leg enters the caller cofiber through the same Q inverse. -/
def targetLegHo
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    H.{u, v}.obj F.right ⟶ H.{u, v}.obj ((chosenCofiber (B := B) d hd).obj F) :=
  (qIso F.right).inv ≫ H.{u, v}.map (d (QF F)).inr

/-- The whole chosen suspension is compared using its original cone and zero legs. -/
def suspensionChoiceHoIso
    (chosen : ∀ F : Arrow C.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := Index)).app F.left) F.hom)
    (chosenIsColimit : ∀ F, IsColimit (chosen F)) (X : C.{u, v}) :
    H.{u, v}.obj (ISusp.obj (Q.obj X)) ≅
      H.{u, v}.obj
        (chosen (Arrow.mk (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram
          Diagrams.zeroDiagram_isZero (Q.obj X)))).pt :=
  H.{u, v}.mapIso (cofiberChoiceIso cone ι c hc chosen chosenIsColimit
    (Arrow.mk (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero (Q.obj X))))

/-- The caller's original boundary maps to the original suspension through that same comparison. -/
def boundaryHo
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    H.{u, v}.obj ((chosenCofiber (B := B) d hd).obj F) ⟶
      H.{u, v}.obj (ISusp.obj (Q.obj F.left)) :=
  H.{u, v}.map (OrdinaryHoChosenPuppe.boundary cone ι d hd
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (QF F)) ≫
      (suspensionChoiceHoIso (B := B) d hd F.left).inv

/-- Both original cofiber and suspension choices retain the entire actual boundary equation. -/
theorem choice_boundaryHo
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) ≫
        boundaryHo (B := B) d hd F = ShiftedPuppeTests.boundaryHo (B := B) F := by
  have h := boundary_cofiberChoice Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
    cone ι c hc d hd (QF F)
  have hHo := H.{u, v}.congr_map h
  simp only [Functor.map_comp] at hHo
  change H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) ≫
      H.{u, v}.map (OrdinaryHoChosenPuppe.boundary cone ι d hd
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (QF F)) =
    ShiftedPuppeTests.boundaryHo (B := B) F ≫
      (suspensionChoiceHoIso (B := B) d hd F.left).hom at hHo
  change H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) ≫
    (H.{u, v}.map (OrdinaryHoChosenPuppe.boundary cone ι d hd
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (QF F)) ≫
      (suspensionChoiceHoIso (B := B) d hd F.left).inv) = _
  rw [← Category.assoc, hHo]
  change (_ ≫ (suspensionChoiceHoIso (B := B) d hd F.left).hom) ≫
    (suspensionChoiceHoIso (B := B) d hd F.left).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The whole original target-leg comparison retains the caller's actual target map. -/
theorem choice_targetLegHo
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) (F : Arrow C.{u, v}) :
    ShiftedPuppeTests.targetLegHo (B := B) F ≫
        H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) =
      targetLegHo (B := B) d hd F := by
  change ((qIso F.right).inv ≫ H.{u, v}.map (c (QF F)).inr) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp, choiceNatIso_hom_target]
  rfl

/-- The complete chosen-cofiber Hom equivalence uses the actual comparison in both directions. -/
def testHomEquiv
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E ≃
      ShiftedHom.test (B := B) q (CQ.obj F) E :=
  Iso.homCongr (H.{u, v}.mapIso ((choiceNatIso (B := B) d hd).app F)).symm (Iso.refl _)

/-- The complete forward function is original comparison precomposition. -/
theorem testHomEquiv_apply
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E) :
    testHomEquiv (B := B) d hd q F E g =
      H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) ≫ g := by
  simp only [testHomEquiv, Iso.homCongr_apply, Iso.symm_inv,
    Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
  rfl

/-- The complete inverse function is original inverse-comparison precomposition. -/
theorem testHomEquiv_symm_apply
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q (CQ.obj F) E) :
    (testHomEquiv (B := B) d hd q F E).symm g =
      H.{u, v}.map ((choiceNatIso (B := B) d hd).inv.app F) ≫ g := by
  simp only [testHomEquiv, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.symm_hom, Functor.mapIso_inv, Iso.refl_inv, Category.comp_id]
  rfl

/-- The actual chosen null class maps to the same original null class. -/
theorem testHomEquiv_null
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    testHomEquiv (B := B) d hd q F E
        (OrdinaryHoCofiberKernel.nullHom ((chosenCofiber (B := B) d hd).obj F)
          ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F) ((ShiftedTargets.target q).obj E) := by
  rw [testHomEquiv_apply, OrdinaryHoCofiberKernel.precomp_nullHom]

/-- Every original Arrow square acts on both full chosen-cofiber Hom comparison functions. -/
theorem testHomEquiv_source
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj G) E) :
    testHomEquiv (B := B) d hd q F E
        (H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) ≫ g) =
      H.{u, v}.map (CQ.map φ) ≫ testHomEquiv (B := B) d hd q G E g := by
  rw [testHomEquiv_apply, testHomEquiv_apply]
  have h := H.{u, v}.congr_map (choiceNatIso_naturality (B := B) d hd φ)
  simp only [Functor.map_comp] at h
  rw [← Category.assoc, ← h, Category.assoc]

/-- The entire inverse cofiber Hom function retains the same original Arrow source action. -/
theorem testHomEquiv_symm_source
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G)
    (E : C.{u, v}) (g : ShiftedHom.test (B := B) q (CQ.obj G) E) :
    (testHomEquiv (B := B) d hd q F E).symm (H.{u, v}.map (CQ.map φ) ≫ g) =
      H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) ≫
        (testHomEquiv (B := B) d hd q G E).symm g := by
  apply (testHomEquiv (B := B) d hd q F E).injective
  rw [Equiv.apply_symm_apply, testHomEquiv_source, Equiv.apply_symm_apply]

/-- Every full original target transformation acts on the whole cofiber Hom comparison. -/
theorem testHomEquiv_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E) :
    testHomEquiv (B := B) d hd q F E'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      testHomEquiv (B := B) d hd q F E g ≫
        H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  rw [testHomEquiv_apply, testHomEquiv_apply, Category.assoc]

/-- Every full target transformation retains the original inverse Hom comparison function. -/
theorem testHomEquiv_symm_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}}
    (t : E ⟶ E') (g : ShiftedHom.test (B := B) q (CQ.obj F) E) :
    (testHomEquiv (B := B) d hd q F E').symm
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      (testHomEquiv (B := B) d hd q F E).symm g ≫
        H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  apply (testHomEquiv (B := B) d hd q F E').injective
  rw [Equiv.apply_symm_apply, testHomEquiv_target, Equiv.apply_symm_apply]

/-- Every original Arrow retains both caller target legs in its complete naturality square. -/
theorem targetLegHo_naturality
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) {F G : Arrow C.{u, v}} (φ : F ⟶ G) :
    H.{u, v}.map φ.right ≫ targetLegHo (B := B) d hd G =
      targetLegHo (B := B) d hd F ≫ H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) := by
  have hQ : H.{u, v}.map φ.right ≫ (qIso G.right).inv =
      (qIso F.right).inv ≫ H.{u, v}.map (Q.map φ.right) :=
    NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso_inv_naturality (B := B) φ.right
  have hTarget := OrdinaryHoChosenPuppe.cofiberMap_target cone ι d hd (Q.mapArrow.map φ)
  have hTargetHo : H.{u, v}.map (d (QF F)).inr ≫
      H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) =
    H.{u, v}.map (Q.map φ.right) ≫ H.{u, v}.map (d (QF G)).inr := by
    have h := H.{u, v}.congr_map hTarget
    simp only [Functor.map_comp] at h
    change H.{u, v}.map (d (QF F)).inr ≫
        H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) =
      H.{u, v}.map (Q.map φ.right) ≫ H.{u, v}.map (d (QF G)).inr at h
    exact h
  change H.{u, v}.map φ.right ≫ ((qIso G.right).inv ≫ _) =
    ((qIso F.right).inv ≫ _) ≫ _
  rw [← Category.assoc, hQ, Category.assoc, ← hTargetHo, ← Category.assoc]

/-- Both caller cofiber maps and original Q suspension maps retain full boundary naturality. -/
theorem boundaryHo_naturality
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) {F G : Arrow C.{u, v}} (φ : F ⟶ G) :
    H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) ≫ boundaryHo (B := B) d hd G =
      boundaryHo (B := B) d hd F ≫ H.{u, v}.map (ISusp.map (Q.map φ.left)) := by
  let eF := H.{u, v}.mapIso ((choiceNatIso (B := B) d hd).app F)
  apply (cancel_epi eF.hom).mp
  change H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) ≫
      (H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) ≫ boundaryHo (B := B) d hd G) =
    H.{u, v}.map ((choiceNatIso (B := B) d hd).hom.app F) ≫
      (boundaryHo (B := B) d hd F ≫ H.{u, v}.map (ISusp.map (Q.map φ.left)))
  rw [← Category.assoc, ← Functor.map_comp, ← choiceNatIso_naturality,
    Functor.map_comp, Category.assoc, choice_boundaryHo]
  rw [← Category.assoc, choice_boundaryHo]
  exact ShiftedPuppeTests.boundaryHo_naturality (B := B) φ

/-- The target restriction is the caller's actual original target leg on every integer test. -/
def targetRestriction
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v}) :
    ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E →
      ShiftedHom.test (B := B) q F.right E := fun g => targetLegHo (B := B) d hd F ≫ g

/-- The caller's connecting function keeps its complete chosen boundary and the original shift. -/
def connecting
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) (q + 1) F.left E →
      ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E :=
  fun g => boundaryHo (B := B) d hd F ≫
    (ShiftedHom.suspensionHomEquiv (B := B) q F.left E hE).symm g

/-- The full chosen-cofiber Hom equivalence preserves the entire original target restriction. -/
theorem testHomEquiv_targetRestriction
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E) :
    ShiftedPuppeTests.targetRestriction (B := B) q F E
        (testHomEquiv (B := B) d hd q F E g) = targetRestriction (B := B) d hd q F E g := by
  rw [testHomEquiv_apply]
  change _ ≫ (_ ≫ g) = _
  rw [← Category.assoc, choice_targetLegHo]
  rfl

/-- The same whole Hom equivalence preserves the actual degree-changing connecting function. -/
theorem testHomEquiv_connecting
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : ShiftedHom.test (B := B) (q + 1) F.left E) :
    testHomEquiv (B := B) d hd q F E (connecting (B := B) d hd q F E hE g) =
      ShiftedPuppeTests.connecting (B := B) q F E hE g := by
  rw [testHomEquiv_apply]
  change _ ≫ (boundaryHo (B := B) d hd F ≫ _) = _
  rw [← Category.assoc, choice_boundaryHo]
  rfl

/-- Every entire caller Arrow square commutes with the full degree-changing connecting function. -/
theorem connecting_source
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G)
    (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) G.left E) :
    connecting (B := B) d hd q F E hE (H.{u, v}.map φ.left ≫ g) =
      H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) ≫
        connecting (B := B) d hd q G E hE g := by
  unfold connecting
  rw [ShiftedHom.suspensionHomEquiv_symm_source (B := B) q φ.left E hE, ← Category.assoc,
    ← boundaryHo_naturality, Category.assoc]

/-- Every Omega target map retains the caller's complete original connecting function. -/
theorem connecting_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E')
    (g : ShiftedHom.test (B := B) (q + 1) F.left E) :
    connecting (B := B) d hd q F E' hE'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target (q + 1)).map t)) =
      connecting (B := B) d hd q F E hE g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  unfold connecting
  rw [ShiftedHom.suspensionHomEquiv_symm_target (B := B) q F.left hE hE' t,
    Category.assoc]

/-- Both components of every caller Arrow square commute with its actual target restriction. -/
theorem targetRestriction_source
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) {F G : Arrow C.{u, v}} (φ : F ⟶ G)
    (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj G) E) :
    targetRestriction (B := B) d hd q F E
        (H.{u, v}.map ((chosenCofiber (B := B) d hd).map φ) ≫ g) =
      H.{u, v}.map φ.right ≫ targetRestriction (B := B) d hd q G E g := by
  unfold targetRestriction
  rw [← Category.assoc, ← targetLegHo_naturality, Category.assoc]

/-- Every full target transformation commutes with the caller's original target restriction. -/
theorem targetRestriction_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) {E E' : C.{u, v}}
    (t : E ⟶ E')
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E) :
    targetRestriction (B := B) d hd q F E'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      targetRestriction (B := B) d hd q F E g ≫
        H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  unfold targetRestriction
  exact (Category.assoc _ _ _).symm

/-- Exactness at the original target retains every caller-chosen cofiber object. -/
theorem exact_at_target
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (g : ShiftedHom.test (B := B) q F.right E) :
    (∃ h : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E,
      targetRestriction (B := B) d hd q F E h = g) ↔
      ShiftedPuppeTests.sourceRestriction (B := B) q F E g =
        OrdinaryHoCofiberKernel.nullHom F.left ((ShiftedTargets.target q).obj E) := by
  constructor
  · rintro ⟨h, hh⟩
    exact (ShiftedPuppeTests.exact_at_target (B := B) q F E g).mp
      ⟨testHomEquiv (B := B) d hd q F E h,
        (testHomEquiv_targetRestriction (B := B) d hd q F E h).trans hh⟩
  · intro h
    obtain ⟨k, hk⟩ := (ShiftedPuppeTests.exact_at_target (B := B) q F E g).mpr h
    refine ⟨(testHomEquiv (B := B) d hd q F E).symm k, ?_⟩
    rw [← testHomEquiv_targetRestriction, Equiv.apply_symm_apply]
    exact hk

/-- Exactness at the caller's actual Q-cofiber retains its two original comparison directions. -/
theorem exact_at_cofiber
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj F) E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.left E,
      connecting (B := B) d hd q F E hE h = g) ↔
      targetRestriction (B := B) d hd q F E g =
        OrdinaryHoCofiberKernel.nullHom F.right ((ShiftedTargets.target q).obj E) := by
  have hExact := ShiftedPuppeTests.exact_at_cofiber (B := B) q F E hE
    (testHomEquiv (B := B) d hd q F E g)
  constructor
  · rintro ⟨h, hh⟩
    rw [← testHomEquiv_targetRestriction]
    apply hExact.mp
    refine ⟨h, ?_⟩
    rw [← testHomEquiv_connecting, hh]
  · intro h
    rw [← testHomEquiv_targetRestriction] at h
    obtain ⟨k, hk⟩ := hExact.mpr h
    refine ⟨k, ?_⟩
    apply (testHomEquiv (B := B) d hd q F E).injective
    rw [testHomEquiv_connecting]
    exact hk

/-- Exactness at the shifted source keeps the caller's entire connecting map
 and actual null class. -/
theorem exact_at_shifted_source
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : Arrow C.{u, v}) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : ShiftedHom.test (B := B) (q + 1) F.left E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.right E,
      ShiftedPuppeTests.sourceRestriction (B := B) (q + 1) F E h = g) ↔
      connecting (B := B) d hd q F E hE g =
        OrdinaryHoCofiberKernel.nullHom ((chosenCofiber (B := B) d hd).obj F)
          ((ShiftedTargets.target q).obj E) := by
  have hTransport : connecting (B := B) d hd q F E hE g =
      OrdinaryHoCofiberKernel.nullHom ((chosenCofiber (B := B) d hd).obj F)
        ((ShiftedTargets.target q).obj E) ↔
    ShiftedPuppeTests.connecting (B := B) q F E hE g =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F) ((ShiftedTargets.target q).obj E) := by
    constructor
    · intro h
      have h' := congrArg (testHomEquiv (B := B) d hd q F E) h
      rw [testHomEquiv_connecting, testHomEquiv_null] at h'
      exact h'
    · intro h
      apply (testHomEquiv (B := B) d hd q F E).injective
      rw [testHomEquiv_connecting, testHomEquiv_null]
      exact h
  exact (ShiftedPuppeTests.exact_at_shifted_source (B := B) q F E hE g).trans hTransport.symm

/-- An original Omega-test weak map makes every caller cofiber Hom class null in every integer. -/
theorem chosenCofiberHom_eq_null
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests Actual.symmetricFamily f) (q : ℤ) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q ((chosenCofiber (B := B) d hd).obj (Arrow.mk f)) E) :
    g = OrdinaryHoCofiberKernel.nullHom ((chosenCofiber (B := B) d hd).obj (Arrow.mk f))
      ((ShiftedTargets.target q).obj E) := by
  apply (testHomEquiv (B := B) d hd q (Arrow.mk f) E).injective
  rw [testHomEquiv_null]
  exact NativeK.CofiberNullity.cofiberQHom_eq_null (B := B) Actual.symmetricFamily f hf
    ((ShiftedTargets.target q).obj E) (ShiftedTargets.target_isOmega (B := B) q E hE) _

/-- Every caller-chosen Q-cofiber collapse passes the original all-target Omega tests. -/
theorem chosenCofiberCollapse_omegaTests
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) {X Y : C.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests Actual.symmetricFamily f) :
    NativeK.omegaTests Actual.symmetricFamily
      (Diagrams.toZero ((chosenCofiber (B := B) d hd).obj (Arrow.mk f))) := by
  let e := (choiceNatIso (B := B) d hd).app (Arrow.mk f)
  let eArrow : Arrow.mk ((NativeK.CofiberNullity.collapse (B := B)).app (Arrow.mk f)) ≅
      Arrow.mk (Diagrams.toZero ((chosenCofiber (B := B) d hd).obj (Arrow.mk f))) :=
    Arrow.isoMk e (Iso.refl Diagrams.zeroDiagram)
      (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)
  exact ((NativeK.omegaTests Actual.symmetricFamily).arrow_mk_iso_iff eArrow).mp
    (NativeK.CofiberNullity.collapse_omegaTests (B := B) Actual.symmetricFamily f hf)

/-- The full collapse Arrow functor retains every caller-cofiber map and the original zero arrow. -/
def chosenCollapseArrowFunctor
    (chosen : ∀ F : Arrow C.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := Index)).app F.left) F.hom)
    (chosenIsColimit : ∀ F, IsColimit (chosen F)) : Arrow C.{u, v} ⥤ Arrow C.{u, v} :=
  chosenCofiber (B := B) chosen chosenIsColimit ⋙ Diagrams.toZeroArrow

/-- Both full collapse Arrow functors compare through the same original two cofiber functions. -/
def chosenCollapseArrowNatIso
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F)) : CQ.{u, v} ⋙ Diagrams.toZeroArrow ≅
    chosenCollapseArrowFunctor (B := B) d hd :=
  Functor.isoWhiskerRight (choiceNatIso (B := B) d hd) Diagrams.toZeroArrow

end PointedCGWH.Spectra.Symmetric.Stable.ChosenCofiberTests
