/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StrictFiber
import MathlibExt.CategoryTheory.Enriched.PointwiseFiniteInstances
import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso

/-!
# The original orthogonal chosen fiber under the full sequential restriction

The restriction is the genuine enriched functor induced by the original
sequential to orthogonal operator map. Its entire Hom actions and all
ordinary transformation components remain the original ones. In particular,
restriction preserves the caller's actual chosen pullback, rather than
replacing its carrier by a newly selected fiber.

The original orthogonal zero restricts to a zero diagram. Its canonical
comparison with the original sequential zero is retained in both directions.
The resulting fiber comparison keeps the original total projection,
collapse, arbitrary Arrow square and arbitrary chosen cone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v uJ vJ

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.ChosenFiberTransport

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
  OrthogonalIntegerHomotopy
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open CategoryTheory.Spectra.SpectrumIndexMaps

private abbrev Seq := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev N := PointedCGWH.Spectra.Sequential.Index.{u, v}

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

section LimitConstruction

variable {J : Type uJ} [Category.{vJ} J] {K : J ⥤ Seq.{u, v}}

private def liftFromEvaluatedLimits (c : Cone K)
    (hc : ∀ a : N.{u, v}, IsLimit ((evaluation a).mapCone c)) (q : Cone K) : q.pt ⟶ c.pt :=
  GradedNatTrans.unitOfComponents
    (fun a => (hc a).lift ((evaluation a).mapCone q)) (by
      intro a b
      apply (hc b).hom_ext
      intro j
      let H := a ⟶[PointedCGWH.{u, v}] b
      let ca := component (c.π.app j) a
      let cb := component (c.π.app j) b
      let qa := component (q.π.app j) a
      let qb := component (q.π.app j) b
      let la := (hc a).lift ((evaluation a).mapCone q)
      let lb := (hc b).lift ((evaluation b).mapCone q)
      let ac := MonoidalClosed.uncurry (c.pt.toEnrichedFunctor.map a b)
      let aq := MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b)
      let aj := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      have hca : ac ≫ cb = (ca ▷ H) ≫ aj := by
        simpa only [ac, aj, ca, cb, H, component, CategoryTheory.Functor.const_obj_obj,
          tensorHom_id] using
          (c.π.app j).uncurriedNaturality a b
      have hqa : aq ≫ qb = (qa ▷ H) ≫ aj := by
        simpa only [aq, aj, qa, qb, H, component, CategoryTheory.Functor.const_obj_obj,
          tensorHom_id] using
          (q.π.app j).uncurriedNaturality a b
      have hla : la ≫ ca = qa := (hc a).fac ((evaluation a).mapCone q) j
      have hlb : lb ≫ cb = qb := (hc b).fac ((evaluation b).mapCone q) j
      change (aq ≫ lb) ≫ cb = ((la ⊗ₘ 𝟙 H) ≫ ac) ≫ cb
      rw [tensorHom_id]
      calc
        _ = aq ≫ qb := by rw [Category.assoc, hlb]
        _ = (qa ▷ H) ≫ aj := hqa
        _ = (la ▷ H) ≫ (ca ▷ H) ≫ aj := by
          rw [← hla, comp_whiskerRight, Category.assoc]
        _ = _ := by rw [← hca, Category.assoc])

private theorem liftFromEvaluatedLimits_component (c : Cone K)
    (hc : ∀ a : N.{u, v}, IsLimit ((evaluation a).mapCone c)) (q : Cone K) (a : N.{u, v}) :
    component (liftFromEvaluatedLimits c hc q) a = (hc a).lift ((evaluation a).mapCone q) :=
  GradedNatTrans.unitOfComponents_component _ _ a

private def sequentialLimitOfEvaluations (c : Cone K)
    (hc : ∀ a : N.{u, v}, IsLimit ((evaluation a).mapCone c)) : IsLimit c where
  lift := liftFromEvaluatedLimits c hc
  fac q j := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [component_comp, liftFromEvaluatedLimits_component]
    exact (hc a).fac ((evaluation a).mapCone q) j
  uniq q m hm := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [liftFromEvaluatedLimits_component]
    apply (hc a).hom_ext
    intro j
    have h := congrArg (fun f => component f a) (hm j)
    rw [component_comp] at h
    exact h.trans ((hc a).fac ((evaluation a).mapCone q) j).symm

end LimitConstruction

/-- The original full restriction followed by evaluation is the actual
orthogonal evaluation at the original embedded index. -/
theorem underlying_evaluation_eq (a : N.{u, v}) :
    underlyingSequential.{u, v} ⋙ evaluation a =
      evaluation (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj a) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  change component (restrictionMap sequentialOrthogonalOperatorIndexFunctor f) a =
    𝟙 _ ≫ component f (sequentialOrthogonalOperatorIndexFunctor.obj a) ≫ 𝟙 _
  rw [restrictionMap_component, Category.id_comp, Category.comp_id]

section PreservedLimits

variable {J : Type uJ} [Category.{vJ} J] [HasLimitsOfShape J PointedCGWH.{u, v}]
  (K : J ⥤ OrthogonalCarrier.{u, v})

/-- Every actual chosen orthogonal cone retains its full limit property
under the original enriched restriction. -/
def underlyingConeIsLimit (c : Cone K) (hc : IsLimit c) :
    IsLimit (underlyingSequential.mapCone c) := by
  apply sequentialLimitOfEvaluations
  intro a
  change IsLimit ((underlyingSequential ⋙ evaluation a).mapCone c)
  rw [underlying_evaluation_eq]
  exact isLimitOfPreserves (evaluation (sequentialOrthogonalOperatorIndexFunctor.obj a)) hc

/-- The original restriction preserves each original pointed diagram
shape whose base limits exist. -/
theorem underlying_preservesLimit : PreservesLimit K underlyingSequential.{u, v} :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit K)
    (underlyingConeIsLimit K (limit.cone K) (limit.isLimit K))

instance underlyingPreservesLimitsOfShape :
    PreservesLimitsOfShape J underlyingSequential.{u, v} where
  preservesLimit := fun {K} => underlying_preservesLimit K

end PreservedLimits

/-- The unchanged original orthogonal zero remains zero on its full
sequential restriction, including all enriched actions. -/
theorem underlyingZero_isZero :
    IsZero (underlyingSequential.{u, v}.obj (Diagrams.zeroDiagram (A := O.{u, v}))) :=
  CategoryTheory.EnrichedZeroCompletion.diagram_isZero_of_obj_isZero _
    (fun a => Diagrams.initialDiagram_component_isZero
      (sequentialOrthogonalOperatorIndexFunctor.obj a))

/-- Both directions are determined by the original zero universal properties. -/
def underlyingZeroIso :
    underlyingSequential.{u, v}.obj (Diagrams.zeroDiagram (A := O.{u, v})) ≅
      Diagrams.zeroDiagram (A := N.{u, v}) :=
  underlyingZero_isZero.iso Diagrams.zeroDiagram_isZero

/-- The entire restricted original zero-to-target arrow keeps the
forward zero comparison. -/
theorem underlyingZeroIso_hom_zeroTo (Y : OrthogonalCarrier.{u, v}) :
    underlyingZeroIso.{u, v}.hom ≫ Diagrams.zeroTo (underlyingSequential.obj Y) =
      underlyingSequential.map (Diagrams.zeroTo Y) :=
  underlyingZero_isZero.isInitial.hom_ext _ _

/-- Its inverse keeps the same original zero-to-target arrow. -/
theorem underlyingZeroIso_inv_zeroTo (Y : OrthogonalCarrier.{u, v}) :
    underlyingZeroIso.{u, v}.inv ≫ underlyingSequential.map (Diagrams.zeroTo Y) =
      Diagrams.zeroTo (underlyingSequential.obj Y) :=
  Diagrams.zeroDiagramIsInitial.hom_ext _ _

/-- The complete restricted original collapse retains the same zero comparison. -/
theorem underlying_toZero (X : OrthogonalCarrier.{u, v}) :
    underlyingSequential.map (Diagrams.toZero X) ≫ underlyingZeroIso.{u, v}.hom =
      Diagrams.toZero (underlyingSequential.obj X) :=
  Diagrams.zeroDiagramIsTerminal.hom_ext _ _

variable {X Y : OrthogonalCarrier.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (Diagrams.zeroTo Y))

/-- The caller's unchanged fiber carrier and first projection restrict
literally; the original collapse uses the full zero isomorphism. -/
def underlyingChosenCone :
    PullbackCone (underlyingSequential.map p)
      (Diagrams.zeroTo (underlyingSequential.obj Y)) :=
  PullbackCone.mk (underlyingSequential.map c.fst)
    (underlyingSequential.map c.snd ≫ underlyingZeroIso.hom) (by
      rw [Category.assoc, underlyingZeroIso_hom_zeroTo]
      exact (underlyingSequential.map_comp c.fst p).symm.trans
        ((underlyingSequential.congr_map c.condition).trans
          (underlyingSequential.map_comp c.snd (Diagrams.zeroTo Y))))

/-- The original total projection is retained as the entire restricted map. -/
theorem underlyingChosenCone_fst :
    (underlyingChosenCone p c).fst = underlyingSequential.map c.fst := rfl

/-- The original collapse is retained together with its original zero comparison. -/
theorem underlyingChosenCone_snd :
    (underlyingChosenCone p c).snd =
      underlyingSequential.map c.snd ≫ underlyingZeroIso.hom := rfl

private def mappedChosenConeIsLimit (hc : IsLimit c) :
    IsLimit (c.map underlyingSequential) :=
  (PullbackCone.isLimitMapConeEquiv c underlyingSequential).1
    (isLimitOfPreserves underlyingSequential hc)

/-- The same original chosen carrier is the limiting fiber on restriction,
with both actual projections and the original zero comparison retained. -/
def underlyingChosenConeIsLimit (hc : IsLimit c) : IsLimit (underlyingChosenCone p c) := by
  have h : IsPullback (underlyingSequential.map c.fst)
      (underlyingSequential.map c.snd ≫ underlyingZeroIso.hom)
      (underlyingSequential.map p) (Diagrams.zeroTo (underlyingSequential.obj Y)) :=
    (IsPullback.of_isLimit (mappedChosenConeIsLimit p c hc)).of_iso
    (Iso.refl _) (Iso.refl _) underlyingZeroIso (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      PullbackCone.map, PullbackCone.mk_fst])
    (by simp only [Iso.refl_hom, Category.id_comp, PullbackCone.map, PullbackCone.mk_snd])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by
      simp only [Iso.refl_hom, Category.comp_id]
      exact (underlyingZeroIso_hom_zeroTo Y).symm)
  exact h.isLimit

/-- This is the full comparison from the restricted caller's fiber to the
original selected sequential fiber of the entire restricted Arrow. -/
def underlyingChosenFiberIso (hc : IsLimit c) :
    underlyingSequential.obj c.pt ≅ fiber (underlyingSequential.map p) :=
  chosenFiberIso (underlyingSequential.map p) (underlyingChosenCone p c)
    (underlyingChosenConeIsLimit p c hc)

/-- Its forward function retains the complete original total projection. -/
theorem underlyingChosenFiberIso_hom_fst (hc : IsLimit c) :
    (underlyingChosenFiberIso p c hc).hom ≫ fiberToTotal (underlyingSequential.map p) =
      underlyingSequential.map c.fst :=
  chosenFiberIso_hom_fst _ _ _

/-- Its forward zero leg is the original collapse and original zero Iso. -/
theorem underlyingChosenFiberIso_hom_snd (hc : IsLimit c) :
    (underlyingChosenFiberIso p c hc).hom ≫ fiberToZero (underlyingSequential.map p) =
      underlyingSequential.map c.snd ≫ underlyingZeroIso.hom :=
  chosenFiberIso_hom_snd _ _ _

/-- The inverse recovers the complete original first projection. -/
theorem underlyingChosenFiberIso_inv_fst (hc : IsLimit c) :
    (underlyingChosenFiberIso p c hc).inv ≫ underlyingSequential.map c.fst =
      fiberToTotal (underlyingSequential.map p) :=
  chosenFiberIso_inv_fst _ _ _

/-- The inverse recovers the complete collapse after its actual zero comparison. -/
theorem underlyingChosenFiberIso_inv_snd (hc : IsLimit c) :
    (underlyingChosenFiberIso p c hc).inv ≫
        (underlyingSequential.map c.snd ≫ underlyingZeroIso.hom) =
      fiberToZero (underlyingSequential.map p) :=
  chosenFiberIso_inv_snd _ _ _

/-- Both legs of the entire original collapse Arrow participate in transport. -/
def underlyingCollapseArrowIso (hc : IsLimit c) :
    Arrow.mk (underlyingSequential.map c.snd) ≅
      Arrow.mk (fiberToZero (underlyingSequential.map p)) :=
  Arrow.isoMk (underlyingChosenFiberIso p c hc) underlyingZeroIso
    (underlyingChosenFiberIso_hom_snd p c hc)

/-- The entire total-projection Arrow uses the same full fiber comparison. -/
def underlyingTotalArrowIso (hc : IsLimit c) :
    Arrow.mk (underlyingSequential.map c.fst) ≅
      Arrow.mk (fiberToTotal (underlyingSequential.map p)) :=
  Arrow.isoMk (underlyingChosenFiberIso p c hc) (Iso.refl _) (by
    change (underlyingChosenFiberIso p c hc).hom ≫
      fiberToTotal (underlyingSequential.map p) = underlyingSequential.map c.fst ≫ 𝟙 _
    rw [Category.comp_id]
    exact underlyingChosenFiberIso_hom_fst p c hc)

section Naturality

variable {X' Y' : OrthogonalCarrier.{u, v}} {p' : X' ⟶ Y'}
  (d : PullbackCone p' (Diagrams.zeroTo Y')) (hd : IsLimit d)

/-- Every whole orthogonal Arrow square restricts to the exact chosen-fiber
map, with no replacement of either original chosen carrier. -/
theorem underlyingChosenFiberMap_eq (q : Arrow.mk p ⟶ Arrow.mk p') :
    underlyingSequential.map (chosenFiberMap q c d hd) =
      chosenFiberMap (underlyingSequential.mapArrow.map q)
        (underlyingChosenCone p c) (underlyingChosenCone p' d)
          (underlyingChosenConeIsLimit p' d hd) := by
  apply PullbackCone.IsLimit.hom_ext (underlyingChosenConeIsLimit p' d hd)
  · change underlyingSequential.map (chosenFiberMap q c d hd) ≫
        underlyingSequential.map d.fst = _
    rw [← underlyingSequential.map_comp, chosenFiberMap_fst,
      underlyingSequential.map_comp, chosenFiberMap_fst]
    rfl
  · change underlyingSequential.map (chosenFiberMap q c d hd) ≫
        (underlyingSequential.map d.snd ≫ underlyingZeroIso.hom) = _
    rw [← Category.assoc, ← underlyingSequential.map_comp, chosenFiberMap_snd,
      chosenFiberMap_snd]
    rfl

/-- Every original source and target component is retained by the complete
fiber comparison's naturality square. -/
theorem underlyingChosenFiberIso_naturality (hc : IsLimit c)
    (q : Arrow.mk p ⟶ Arrow.mk p') :
    underlyingSequential.map (chosenFiberMap q c d hd) ≫
        (underlyingChosenFiberIso p' d hd).hom =
      (underlyingChosenFiberIso p c hc).hom ≫
        fiberMap (underlyingSequential.mapArrow.map q) := by
  rw [underlyingChosenFiberMap_eq]
  exact chosenFiberIso_naturality (underlyingSequential.mapArrow.map q)
    (underlyingChosenCone p c) (underlyingChosenConeIsLimit p c hc)
    (underlyingChosenCone p' d) (underlyingChosenConeIsLimit p' d hd)

/-- The actual inverse of the same whole fiber comparison retains the
complete original Arrow naturality in the opposite direction. -/
theorem underlyingChosenFiberIso_inv_naturality (hc : IsLimit c)
    (q : Arrow.mk p ⟶ Arrow.mk p') :
    fiberMap (underlyingSequential.mapArrow.map q) ≫
        (underlyingChosenFiberIso p' d hd).inv =
      (underlyingChosenFiberIso p c hc).inv ≫
        underlyingSequential.map (chosenFiberMap q c d hd) := by
  apply (cancel_epi (underlyingChosenFiberIso p c hc).hom).mp
  rw [← Category.assoc, ← underlyingChosenFiberIso_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end Naturality

section Families

variable (a : ∀ F : Arrow OrthogonalCarrier.{u, v},
    PullbackCone F.hom (Diagrams.zeroTo F.right)) (ha : ∀ F, IsLimit (a F))

/-- All chosen orthogonal fibers and all complete Arrow maps have one
natural comparison with the original sequential chosen fiber functor. -/
def underlyingChosenFiberNatIso :
    chosenFiberFunctor a ha ⋙ underlyingSequential ≅
      underlyingSequential.mapArrow ⋙ fiberFunctor (A := N.{u, v}) :=
  NatIso.ofComponents (fun F => underlyingChosenFiberIso F.hom (a F) (ha F))
    (fun q => underlyingChosenFiberIso_naturality _ _ _ _ _ q)

/-- Every original source projection is retained by that entire natural Iso. -/
theorem underlyingChosenFiberNatIso_hom_fst (F : Arrow OrthogonalCarrier.{u, v}) :
    (underlyingChosenFiberNatIso a ha).hom.app F ≫
        fiberToTotal (underlyingSequential.map F.hom) =
      underlyingSequential.map (a F).fst :=
  underlyingChosenFiberIso_hom_fst F.hom (a F) (ha F)

/-- Every original collapse and every original zero comparison is retained
by the same natural Iso. -/
theorem underlyingChosenFiberNatIso_hom_snd (F : Arrow OrthogonalCarrier.{u, v}) :
    (underlyingChosenFiberNatIso a ha).hom.app F ≫
        fiberToZero (underlyingSequential.map F.hom) =
      underlyingSequential.map (a F).snd ≫ underlyingZeroIso.hom :=
  underlyingChosenFiberIso_hom_snd F.hom (a F) (ha F)

end Families

end PointedCGWH.Spectra.Orthogonal.ChosenFiberTransport
