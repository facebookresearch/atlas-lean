/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeEvaluation
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.Presentation
import MathlibExt.CategoryTheory.Monoidal.Mod.FreeAdjunctTransport
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Complete source maps between symmetric free spectra

The source correspondence covers every map between arbitrary free objects,
including different finite indices and coefficient objects. Its two inverse
maps use the original whole carrier functors and the same free comparison
isomorphisms. Evaluation, all level components, and the original correlated
stabilization generators are preserved simultaneously.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricSpectrum.CorrelatedFreeSource

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := sphereSequence.{u, v}
private abbrev A := sphereSequenceCommMon.{u, v}
private abbrev E := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj

section CarrierMaps
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

private def carrierArrow (e : C ≌ D) {P Q : C} {X Y : D}
    (p : P ≅ e.inverse.obj X) (q : Q ≅ e.inverse.obj Y) (f : Y ⟶ X) : Q ⟶ P :=
  q.hom ≫ e.inverse.map f ≫ p.inv

private def carrierComparison (e : C ≌ D) {P : C} {X : D}
    (p : P ≅ e.inverse.obj X) : e.functor.obj P ≅ X :=
  e.functor.mapIso p ≪≫ e.counitIso.app X

private theorem carrierArrow_id (e : C ≌ D) {P : C} {X : D}
    (p : P ≅ e.inverse.obj X) : carrierArrow e p p (𝟙 X) = 𝟙 P := by
  unfold carrierArrow
  rw [e.inverse.map_id, Category.id_comp, p.hom_inv_id]

private theorem carrierArrow_operator (e : C ≌ D) {P Q : C} {X Y : D}
    (p : P ≅ e.inverse.obj X) (q : Q ≅ e.inverse.obj Y) (f : Y ⟶ X) :
    e.functor.map (carrierArrow e p q f) ≫ (carrierComparison e p).hom =
      (carrierComparison e q).hom ≫ f := by
  dsimp only [carrierArrow, carrierComparison]
  simp only [Iso.trans_hom, Functor.mapIso_hom, e.functor.map_comp, Category.assoc]
  have hp : e.functor.map p.inv ≫ e.functor.map p.hom = 𝟙 _ := by
    rw [← e.functor.map_comp, p.inv_hom_id, e.functor.map_id]
  rw [reassoc_of% hp]
  exact congrArg (fun z => e.functor.map q.hom ≫ z) (e.counitIso.hom.naturality f)

end CarrierMaps

/-- The entire original HSS free object, retained as a source presentation. -/
abbrev originalFree (r : I) (M : V.{u, v}) := (Mod.dayFreeAt S.{u, v} r).obj M

/-- The exact two-way correspondence of all native free maps with original module maps. -/
def arrowEquiv (r s : I) (M N : V.{u, v}) :
    ((freeAt s).obj N ⟶ (freeAt r).obj M) ≃ (originalFree s N ⟶ originalFree r M) :=
  E.{u, v}.fullyFaithfulInverse.homEquiv.trans
    (Iso.homCongr ((freeModuleComparison s).app N).symm
      ((freeModuleComparison r).app M).symm)

/-- Every entire native source arrow has its original sphere-module representative. -/
def sourceArrow {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) : originalFree s N ⟶ originalFree r M :=
  arrowEquiv r s M N f

/-- Every entire original module source arrow has its genuine native representative. -/
def nativeArrow {r s : I} {M N : V.{u, v}}
    (f : originalFree s N ⟶ originalFree r M) : (freeAt s).obj N ⟶ (freeAt r).obj M :=
  (arrowEquiv r s M N).symm f

/-- The source map uses both unchanged whole free isomorphisms and the actual inverse carrier. -/
theorem sourceArrow_formula {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    sourceArrow f = (freeModuleComparison s).hom.app N ≫ toModule.map f ≫
      (freeModuleComparison r).inv.app M := rfl

/-- The inverse uses the same two actual free isomorphisms and original carrier counit maps. -/
theorem nativeArrow_formula {r s : I} {M N : V.{u, v}}
    (f : originalFree s N ⟶ originalFree r M) :
    nativeArrow f = E.counitIso.inv.app ((freeAt s).obj N) ≫
      ofModule.map ((freeModuleComparison s).inv.app N ≫ f ≫
        (freeModuleComparison r).hom.app M) ≫ E.counitIso.hom.app ((freeAt r).obj M) := rfl

/-- Native source recovery is an equality of the complete enriched transformation. -/
@[simp]
theorem nativeArrow_sourceArrow {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) : nativeArrow (sourceArrow f) = f :=
  (arrowEquiv r s M N).symm_apply_apply f

/-- Original source recovery is an equality of the complete sphere-module map. -/
@[simp]
theorem sourceArrow_nativeArrow {r s : I} {M N : V.{u, v}}
    (f : originalFree s N ⟶ originalFree r M) : sourceArrow (nativeArrow f) = f :=
  (arrowEquiv r s M N).apply_symm_apply f

/-- The entire original source map preserves the free-object identity. -/
@[simp]
theorem sourceArrow_id (r : I) (M : V.{u, v}) :
    sourceArrow (𝟙 ((freeAt r).obj M)) = 𝟙 (originalFree r M) :=
  carrierArrow_id E.{u, v} ((freeModuleComparison r).app M)

/-- Both actual source maps keep their full composite and correlated intermediate free object. -/
@[simp]
theorem sourceArrow_comp {r s t : I} {M N P : V.{u, v}}
    (f : (freeAt t).obj P ⟶ (freeAt s).obj N)
    (g : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    sourceArrow (f ≫ g) = sourceArrow f ≫ sourceArrow g := by
  simp only [sourceArrow_formula, toModule.map_comp, Category.assoc,
    (freeModuleComparison s).inv_hom_id_app_assoc]

/-- The same original identity returns the entire native free identity. -/
@[simp]
theorem nativeArrow_id (r : I) (M : V.{u, v}) :
    nativeArrow (𝟙 (originalFree r M)) = 𝟙 ((freeAt r).obj M) := by
  apply (arrowEquiv r r M M).injective
  change sourceArrow (nativeArrow (𝟙 (originalFree r M))) =
    sourceArrow (𝟙 ((freeAt r).obj M))
  rw [sourceArrow_nativeArrow, sourceArrow_id]

/-- The native inverse preserves every original complete free-source composite. -/
theorem nativeArrow_comp {r s t : I} {M N P : V.{u, v}}
    (f : originalFree t P ⟶ originalFree s N) (g : originalFree s N ⟶ originalFree r M) :
    nativeArrow (f ≫ g) = nativeArrow f ≫ nativeArrow g := by
  apply (arrowEquiv r t M P).injective
  change sourceArrow (nativeArrow (f ≫ g)) = sourceArrow (nativeArrow f ≫ nativeArrow g)
  rw [sourceArrow_nativeArrow, sourceArrow_comp, sourceArrow_nativeArrow, sourceArrow_nativeArrow]

private theorem sourceArrow_carrier {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    carrierArrow E.{u, v} ((freeModuleComparison r).app M)
      ((freeModuleComparison s).app N) f = sourceArrow f := rfl

private theorem operatorComparison_eq (r : I) (M : V.{u, v}) :
    carrierComparison E.{u, v} ((freeModuleComparison r).app M) =
      (originalFreeComparison r).app M :=
  NativeOmegaRecovery.ModuleFreeAdjunctTransport.operatorComparison_eq A.{u, v} E.{u, v}
    (symmetricOperatorObj.{u, v} r) (Mod.dayFreeAt S.{u, v} r)
    (Mod.dayEvaluation S.{u, v} r) (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso r) M

/-- Every entire source arrow commutes with both original native free comparisons. -/
theorem sourceArrow_operator {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    ofModule.map (sourceArrow f) ≫ (originalFreeComparison r).hom.app M =
      (originalFreeComparison s).hom.app N ≫ f := by
  have h := carrierArrow_operator E.{u, v}
    ((freeModuleComparison r).app M) ((freeModuleComparison s).app N) f
  rw [operatorComparison_eq, operatorComparison_eq, sourceArrow_carrier] at h
  exact h

/-- The inverse free comparisons retain the same original whole source arrow. -/
theorem sourceArrow_operator_inv {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    (originalFreeComparison s).inv.app N ≫ ofModule.map (sourceArrow f) =
      f ≫ (originalFreeComparison r).inv.app M := by
  apply (cancel_mono ((originalFreeComparison r).hom.app M)).1
  simp only [Category.assoc, (originalFreeComparison r).inv_hom_id_app, Category.comp_id]
  rw [sourceArrow_operator]
  simp only [← Category.assoc, (originalFreeComparison s).inv_hom_id_app, Category.id_comp]

/-- The whole original Arrow isomorphism has both actual original free endpoints. -/
def sourceArrowIso {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    Arrow.mk (ofModule.map (sourceArrow f)) ≅ Arrow.mk f :=
  Arrow.isoMk ((originalFreeComparison s).app N) ((originalFreeComparison r).app M)
    (sourceArrow_operator f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The source arrow's complete evaluated adjunct retains its actual original source comparison. -/
theorem sourceArrow_adjunct {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) :
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} s).homEquiv N (originalFree r M)
        (sourceArrow f) =
      EnrichedFunctorCat.Free.evaluate (symmetricOperatorObj.{u, v} s) N
        ((freeAt r).obj M) f ≫
          EnrichedFunctorCat.component ((originalFreeComparison r).inv.app M)
            (symmetricOperatorObj.{u, v} s) := by
  have h := NativeOmegaRecovery.ModuleFreeAdjunctTransport.source_point A.{u, v} E.{u, v}
    (symmetricOperatorObj.{u, v} r) (symmetricOperatorObj.{u, v} s)
    (Mod.dayFreeAt S.{u, v} r) (Mod.dayEvaluation S.{u, v} r)
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso r)
    (Mod.dayFreeAt S.{u, v} s) (Mod.dayEvaluation S.{u, v} s)
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} s)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso s) M N f
  change _ ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, EnrichedFunctorCat.Free.evaluate_postcomp] at h
  exact h

/-- All evaluated source levels are conjugated by the original unchanged free-level isomorphisms. -/
theorem sourceArrow_level {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) (n : I) :
    (sourceArrow f).hom.natTrans.app n =
      ((freeModuleComparison s).hom.app N).hom.natTrans.app n ≫
        EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} n) ≫
          ((freeModuleComparison r).inv.app M).hom.natTrans.app n := by
  rw [sourceArrow_formula]
  change _ ≫ ((toModule.map f).hom.natTrans.app n ≫ _) = _
  simp only [toModule_hom, hom_app]
  all_goals rfl

/-- The original complete sphere action square is retained for every correlated source arrow. -/
theorem sourceArrow_action {r s : I} {M N : V.{u, v}}
    (f : (freeAt s).obj N ⟶ (freeAt r).obj M) (a n k : I) (g : a ⊗ n ⟶ k) :
    SymmetricModulePresentation.arrowAction (originalFree s N) a n k g ≫
        (sourceArrow f).hom.natTrans.app k =
      (sphereSequence.{u, v}.functor.obj a ◁ (sourceArrow f).hom.natTrans.app n) ≫
        SymmetricModulePresentation.arrowAction (originalFree r M) a n k g :=
  SymmetricModulePresentation.arrowAction_morphism (sourceArrow f) a n k g


end PointedCGWH.SymmetricSpectrum.CorrelatedFreeSource
