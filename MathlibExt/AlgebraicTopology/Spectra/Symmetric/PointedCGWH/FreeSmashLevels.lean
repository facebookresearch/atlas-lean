/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean.Elab.Tactic
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeLevels
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.CorrelatedFreeSource
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Native
import MathlibExt.CategoryTheory.Monoidal.Mod.FreeRelativeTensorCarrier
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijRepresentableTensor

/-!
# Native free symmetric spectra smashed with an arbitrary target

Every map starts with the original balanced relative tensor. The complete carrier
counit, unchanged free comparison, free-unit contraction and original Day
component maps supply its level formula. The target is arbitrary.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped MonoidalClosed CategoryTheory.MonObj CGWH.limits

namespace PointedCGWH.SymmetricSpectrum

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev C := SymmetricSequence.{u, v}
private abbrev S := sphereSequence.{u, v}
private abbrev A : CommMon C.{u, v} where
  X := sphereSequence.{u, v}
  mon := sphereSequenceMonObj.{u, v}
  comm := sphereSequenceIsCommMonObj.{u, v}

/-- The complete selected sphere coefficient record is the unchanged original record. -/
private theorem A_eq_originalCoefficientRecord : A.{u, v} = sphereSequenceCommMon.{u, v} := rfl
private abbrev E : Mod C.{u, v} S.{u, v} ≌ SymmetricSpectrum.{u, v} where
  functor := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor
  inverse := toModule.{u, v}
  unitIso := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.unitIso
  counitIso := SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.counitIso
  functor_unitIso_comp M :=
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor_unitIso_comp M

/-- Both entire carrier functors, units, counits and triangles have the original record value. -/
private theorem E_eq_originalCarrierRecord :
    E.{u, v} = SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} := rfl


/-- The original scalar free diagram keeps every finite-bijection label. -/
abbrev freeDiagram (r : I) (M : V.{u, v}) : C.{u, v} :=
  (representedDiagram r).obj M

section OriginalWholeSmashComparison
universe uC vC uD vD
variable {C₀ : Type uC} [Category.{vC} C₀] [MonoidalCategory C₀]
  [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀] [HasEqualizers C₀]
  {D₀ : Type uD} [Category.{vD} D₀]

/-- The complete relative tensor source is transported through the original two carrier functors. -/
private def originalWholeSourceTransport (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀) :
    Mod C₀ A₀.X ⥤ (D₀ ⥤ D₀) where
  obj P := E₀.inverse ⋙ (Mod.relativeTensor A₀).obj P ⋙ E₀.functor
  map f := Functor.whiskerLeft E₀.inverse
    (Functor.whiskerRight ((Mod.relativeTensor A₀).map f) E₀.functor)
  map_id P := by
    let F := Mod.relativeTensor A₀ ⋙
      (Functor.whiskeringRight (Mod C₀ A₀.X) (Mod C₀ A₀.X) D₀).obj E₀.functor ⋙
        (Functor.whiskeringLeft D₀ (Mod C₀ A₀.X) D₀).obj E₀.inverse
    exact F.map_id P
  map_comp f g := by
    let F := Mod.relativeTensor A₀ ⋙
      (Functor.whiskeringRight (Mod C₀ A₀.X) (Mod C₀ A₀.X) D₀).obj E₀.functor ⋙
        (Functor.whiskeringLeft D₀ (Mod C₀ A₀.X) D₀).obj E₀.inverse
    exact F.map_comp f g

omit [HasEqualizers C₀] in
/-- Every complete module source has the unchanged transported functor value. -/
private theorem originalWholeSourceTransport_obj (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) (P : Mod C₀ A₀.X) :
    (originalWholeSourceTransport A₀ E₀).obj P =
      E₀.inverse ⋙ (Mod.relativeTensor A₀).obj P ⋙ E₀.functor := rfl

omit [HasEqualizers C₀] in
/-- Every original source arrow is carried by the same complete balanced smash map. -/
private theorem originalWholeSourceTransport_map (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) {X Y : D₀} (f : X ⟶ Y) :
    (originalWholeSourceTransport A₀ E₀).map (E₀.inverse.map f) =
      CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap A₀ E₀ f := rfl

/-- The entire original carrier functors transport both full source-comparison maps
as a natural isomorphism on every target object and target arrow. -/
private def originalWholeSmashComparison (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀)
    (P : Mod C₀ A₀.X) (X : D₀) (p : P ≅ E₀.inverse.obj X) :
    CategoryTheory.Mod.EquivalenceFunctionTransport.smashFunctor A₀ E₀ X ≅
      E₀.inverse ⋙ (Mod.relativeTensor A₀).obj P ⋙ E₀.functor :=
  (originalWholeSourceTransport A₀ E₀).mapIso p.symm

omit [HasEqualizers C₀] in
/-- Both full comparison maps are the original transported module isomorphism. -/
private theorem originalWholeSourceTransport_iso (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) (P : Mod C₀ A₀.X) (X : D₀)
    (p : P ≅ E₀.inverse.obj X) :
    (originalWholeSourceTransport A₀ E₀).mapIso p.symm =
      originalWholeSmashComparison A₀ E₀ P X p := by
  apply Iso.ext
  rfl

end OriginalWholeSmashComparison

/-- Both complete original free-module maps are stored at the original
full source and target types. -/
private def wholeOriginalFreeModuleIso (r : I) (M : V.{u, v}) :
    (Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M) ≅
      toModule.{u, v}.obj ((freeAt.{u, v} r).obj M) where
  hom := (freeModuleComparison r).hom.app M
  inv := (freeModuleComparison r).inv.app M
  hom_inv_id := (freeModuleComparison r).hom_inv_id_app M
  inv_hom_id := (freeModuleComparison r).inv_hom_id_app M

/-- The entire typed record has exactly the unchanged original free-module comparison value. -/
private theorem wholeOriginalFreeModuleIso_original (r : I) (M : V.{u, v}) :
    Eq (α := (Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M) ≅
      toModule.{u, v}.obj ((freeAt.{u, v} r).obj M))
      (wholeOriginalFreeModuleIso r M) ((freeModuleComparison r).app M) := by
  apply Iso.ext
  rfl


/-- The actual balanced smash with the complete native free source. -/
def freeSmash (r : I) (M : V.{u, v}) : SymmetricSpectrum.{u, v} ⥤ SymmetricSpectrum.{u, v} :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.smashFunctor sphereSequenceCommMon.{u, v}
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    ((freeAt.{u, v} r).obj M)

/-- The native smash has the same original relative tensor presentation,
using the actual whole free-module comparison. -/
def freeSmashModuleIso (r : I) (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) :
    (freeSmash r M).obj Y ≅
      E.{u, v}.functor.obj
        (((Mod.relativeTensor A.{u, v}).obj ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))).obj
          (toModule.{u, v}.obj Y)) := by
  let N := toModule.{u, v}.obj Y
  let p : (Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M) ≅
      toModule.{u, v}.obj ((freeAt.{u, v} r).obj M) :=
    wholeOriginalFreeModuleIso r M
  exact E.{u, v}.functor.mapIso (((Mod.relativeTensor A.{u, v}).mapIso p.symm).app N)

/-- The original carrier counit compares every entire native level with
its exact relative tensor module level. -/
def moduleNativeLevelIso (r : I) (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) (q : I) :
    ((freeSmash r M).obj Y).X.functor.obj q ≅
      ((((Mod.relativeTensor A.{u, v}).obj ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))).obj
        (toModule.{u, v}.obj Y)).X.functor.obj q) :=
  (evaluation q).mapIso (freeSmashModuleIso r M Y) ≪≫
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso q).app
      (((Mod.relativeTensor A.{u, v}).obj
        ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))).obj (toModule.{u, v}.obj Y))

/-- The whole balanced free smash level has the actual target-first Day
carrier contraction and the original free-diagram coefficient. -/
def freeSmashDayLevelIso (r : I) (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) (q : I) :
    ((freeSmash r M).obj Y).X.functor.obj q ≅
      (Y.X ⊗ freeDiagram.{u, v} r M).functor.obj q :=
  moduleNativeLevelIso r M Y q ≪≫
    ((DayFunctor.equiv I V.{u, v}).functor.mapIso
      (Mod.FreeRelativeTensorCarrier.carrierIso A
        (freeDiagram.{u, v} r M) (toModule.{u, v}.obj Y))).app q

/-- Every complete native free smash level is the unchanged original
complement-decomposition colimit for the arbitrary target. -/
def freeSmashDecompositionIso (r : I) (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) (q : I) :
    ((freeSmash r M).obj Y).X.functor.obj q ≅
      (dayFreeAtComponentFunctor Y.X r q).obj M :=
  freeSmashDayLevelIso r M Y q ≪≫ representedTensorComponentIso Y.X r q M

/-- Every upper-degree free smash level retains the full original
complement-action orbit quotient, with no monoid hypothesis on the target. -/
def freeSmashCardInducedIso {r q : ℕ} (h : r ≤ q)
    (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) :
    ((freeSmash (card r) M).obj Y).X.functor.obj (card q) ≅
      (nativeCardInducedFunctor Y.X h).obj M :=
  freeSmashDecompositionIso (card r) M Y (card q) ≪≫
    (Mod.cardComponentInducedIso Y.X h).app M ≪≫ (cardInducedNativeIso Y.X h).app M

/-- Below its generating degree, every complete native free smash level is initial. -/
def freeSmashCardBelowIsInitial {r q : ℕ} (h : q < r)
    (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) :
    IsInitial (((freeSmash (card r) M).obj Y).X.functor.obj (card q)) :=
  (representedTensorBelowIsInitial Y.X h M).ofIso
    (freeSmashDayLevelIso (card r) M Y (card q)).symm


/-- An actual equivariant coefficient isomorphism induces the full
isomorphism of the original balanced smash quotients. -/
private def nativeBalancedCoefficientIso
    (H G : Type) [Monoid H] [Group G]
    (Z Z' : V.{u, v}) (ρ : H →* End Z) (ρ' : H →* End Z') (ι : H →* G)
    (e : Z ≅ Z') (he : ∀ h, (ρ h).asHom ≫ e.hom = e.hom ≫ (ρ' h).asHom) :
    nativeBalancedSmash.{u, v, 0, 0} H G Z ρ ι ≅
      nativeBalancedSmash.{u, v, 0, 0} H G Z' ρ' ι := by
  have he' : ∀ h, (ρ' h).asHom ≫ e.inv = e.inv ≫ (ρ h).asHom := by
    intro h
    apply (cancel_mono e.hom).1
    have hc : e.inv ≫ (ρ h).asHom ≫ e.hom = (ρ' h).asHom :=
      (congrArg (fun f => e.inv ≫ f) (he h)).trans
        (by rw [← Category.assoc, e.inv_hom_id, Category.id_comp])
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hc.symm
  let f := nativeBalancedMap.{u, v, 0, 0} H G Z ρ ι Z' ρ' e.hom he
  let g := nativeBalancedMap.{u, v, 0, 0} H G Z' ρ' ι Z ρ e.inv he'
  refine ⟨f, g, ?_, ?_⟩
  · apply nativeBalanced_hom_ext.{u, v, 0, 0} H G Z ρ ι
    intro h
    rw [← Category.assoc, nativeBalancedMap_generator, Category.assoc,
      nativeBalancedMap_generator, ← Category.assoc, e.hom_inv_id,
      Category.id_comp, Category.comp_id]
  · apply nativeBalanced_hom_ext.{u, v, 0, 0} H G Z' ρ' ι
    intro h
    rw [← Category.assoc, nativeBalancedMap_generator, Category.assoc,
      nativeBalancedMap_generator, ← Category.assoc, e.inv_hom_id,
      Category.id_comp, Category.comp_id]


/-- The complement group acts only on the target factor in the
coefficient-first source formula. -/
def freeSmashComplementAction (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) (c : I) :
    Aut c →* End (M ⊗ Y.X.functor.obj c) :=
  (Functor.mapEnd c (Y.X.functor ⋙ tensorLeft M)).comp (Aut.toEnd (X := c))

/-- The real value braid converts the original target-first complement
action to the coefficient-first formula, retaining every group element. -/
theorem freeSmashComplement_braid (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) (c : I)
    (a : Aut c) :
    (blockCoefficientAction Y.X c M a).asHom ≫ (β_ (Y.X.functor.obj c) M).hom =
      (β_ (Y.X.functor.obj c) M).hom ≫ (freeSmashComplementAction M Y c a).asHom := by
  rw [blockCoefficientAction_apply, tensorHom_id]
  change (Y.X.functor.map a.asIso.hom ▷ M) ≫ (β_ (Y.X.functor.obj c) M).hom =
    (β_ (Y.X.functor.obj c) M).hom ≫ (M ◁ Y.X.functor.map a.asIso.hom)
  exact braiding_naturality_left (Y.X.functor.map a.asIso.hom) M

/-- The full complement action quotient retains the original coefficient-first
sphere smash convention through the actual value braid. -/
def freeSmashCardCoefficientOrderIso {r q : ℕ} (h : r ≤ q)
    (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) :
    (nativeCardInducedFunctor Y.X h).obj M ≅
      nativeBalancedSmash.{u, v, 0, 0}
        (Aut (card (q - r))) (Aut (card q)) (M ⊗ Y.X.functor.obj (card (q - r)))
        (freeSmashComplementAction M Y (card (q - r)))
        (blockAutHom (card (q - r)) (card r) (card q)
          (cardBlockSumIso (Nat.sub_add_cancel h))) :=
  nativeBalancedCoefficientIso
    (Aut (card (q - r))) (Aut (card q))
    (Y.X.functor.obj (card (q - r)) ⊗ M) (M ⊗ Y.X.functor.obj (card (q - r)))
    (blockCoefficientAction Y.X (card (q - r)) M)
    (freeSmashComplementAction M Y (card (q - r)))
    (blockAutHom (card (q - r)) (card r) (card q)
      (cardBlockSumIso (Nat.sub_add_cancel h)))
    (β_ (Y.X.functor.obj (card (q - r))) M)
    (freeSmashComplement_braid M Y (card (q - r)))

/-- The actual native upper-degree free smash has the whole coefficient-first
orbit formula with complement action only on the original target spectrum. -/
def freeSmashCardOrbitIso {r q : ℕ} (h : r ≤ q)
    (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) :
    ((freeSmash (card r) M).obj Y).X.functor.obj (card q) ≅
      nativeBalancedSmash.{u, v, 0, 0}
        (Aut (card (q - r))) (Aut (card q)) (M ⊗ Y.X.functor.obj (card (q - r)))
        (freeSmashComplementAction M Y (card (q - r)))
        (blockAutHom (card (q - r)) (card r) (card q)
          (cardBlockSumIso (Nat.sub_add_cancel h))) :=
  freeSmashCardInducedIso h M Y ≪≫ freeSmashCardCoefficientOrderIso h M Y


/-- At its generating degree, the whole arbitrary-target free smash has
its original trivial-complement discrete orbit description. -/
def freeSmashCardDiagonalIso (r : ℕ) (M : V.{u, v}) (Y : SymmetricSpectrum.{u, v}) :
    ((freeSmash (card r) M).obj Y).X.functor.obj (card r) ≅
      discreteSmashObj.{u, v, 0} (Aut (card r))
        (Y.X.functor.obj (card (r - r)) ⊗ M) :=
  freeSmashCardInducedIso (Nat.le_refl r) M Y ≪≫ nativeCardInducedDiagonalIso Y.X r M




/-- Every target-spectrum map acts on the complete native free smash
through the unchanged original module relative tensor map. -/
theorem freeSmash_map (r : I) (M : V.{u, v})
    {Y Z : SymmetricSpectrum.{u, v}} (f : Y ⟶ Z) :
    (freeSmash r M).map f = E.{u, v}.functor.map
      (((Mod.relativeTensor A.{u, v}).obj (toModule.{u, v}.obj ((freeAt r).obj M))).map
        (toModule.{u, v}.map f)) :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.smashFunctor_map A.{u, v} E.{u, v}
    ((freeAt r).obj M) f

/-- The complete original source comparison is a natural isomorphism
before evaluating or normalizing any orbit. -/
def freeSmashModuleNatIso (r : I) (M : V.{u, v}) :
    freeSmash r M ≅
      toModule.{u, v} ⋙ ((Mod.relativeTensor sphereSequenceCommMon.{u, v}).obj
        (CorrelatedFreeSource.originalFree r M)) ⋙
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor :=
  originalWholeSmashComparison sphereSequenceCommMon.{u, v}
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    (CorrelatedFreeSource.originalFree r M) ((freeAt.{u, v} r).obj M)
    ((freeModuleComparison.{u, v} r).app M)


/-- The original balanced smash module functor retains every target
spectrum with the same actual source/free comparison. -/
def freeSmashSourceFunctor (r : I) (M : V.{u, v}) :
    SymmetricSpectrum.{u, v} ⥤ Mod C.{u, v} S.{u, v} :=
  toModule.{u, v} ⋙ (Mod.relativeTensor sphereSequenceCommMon.{u, v}).obj
    (CorrelatedFreeSource.originalFree r M)

/-- Elaborate the explicitly supplied complete native level data and submit
its entire declared isomorphism type to the ordinary kernel. -/
local elab (name := exactWholeTypedNativeLevelDataApplication)
    "exact_whole_native_level_data " suppliedData:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let value ← Lean.Elab.Term.elabTerm suppliedData none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let value ← Lean.instantiateMVars value
    unless !value.hasMVar && !value.hasLevelMVar && !value.hasSorry do
      throwError "The supplied complete native level isomorphism data is unresolved"
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Every evaluated source comparison is the complete original natural
isomorphism on the arbitrary target spectrum variable. -/
def freeSmashModuleLevelNatIso (r : I) (M : V.{u, v}) (q : I) :
    freeSmash r M ⋙ evaluation q ≅
      freeSmashSourceFunctor r M ⋙ Mod.dayEvaluation S.{u, v} q := by
  exact_whole_native_level_data
    ((fun (C₀ : Type _) [Category.{v} C₀] [MonoidalCategory C₀]
      [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀]
      (D₀ : Type _) [Category.{v} D₀] (W₀ : Type _) [Category.{v} W₀]
      (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀)
      (P : Mod C₀ A₀.X) (X : D₀) (p : P ≅ E₀.inverse.obj X)
      (L : D₀ ⥤ W₀) (G : Mod C₀ A₀.X ⥤ W₀) (e : E₀.functor ⋙ L ≅ G) =>
    Functor.isoWhiskerRight (originalWholeSmashComparison A₀ E₀ P X p) L ≪≫
      Functor.isoWhiskerLeft (E₀.inverse ⋙ (Mod.relativeTensor A₀).obj P) e)
    C.{u, v} SymmetricSpectrum.{u, v} V.{u, v} A.{u, v} E.{u, v}
    ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))
    ((freeAt.{u, v} r).obj M) (wholeOriginalFreeModuleIso r M)
    (evaluation q) (Mod.dayEvaluation S.{u, v} q)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso q))


/-- An arbitrary native free source arrow induces the same full original
balanced source map, retaining its two actual source isomorphisms. -/
def freeSmashSourceMap {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) : freeSmash s N ⟶ freeSmash r M :=
  CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap sphereSequenceCommMon.{u, v}
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} f

/-- The source module representative is exactly the entire original
correlated source map, with every coefficient and finite label unchanged. -/
theorem freeSmashSource_original {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) :
    CorrelatedFreeSource.sourceArrow f =
      (freeModuleComparison.{u, v} s).hom.app N ≫ toModule.{u, v}.map f ≫
        (freeModuleComparison.{u, v} r).inv.app M :=
  CorrelatedFreeSource.sourceArrow_formula f

section FunctorTransport
universe uC vC uD vD

private theorem functor_source_conjugation
    {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
    (F : D₁ ⥤ D₂) {P Q X Y : D₁} (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) :
    F.map f ≫ (F.mapIso q.symm).hom =
      (F.mapIso p.symm).hom ≫ F.map (p.hom ≫ f ≫ q.inv) := by
  simp only [Functor.mapIso_hom, Iso.symm_hom, ← F.map_comp, p.inv_hom_id_assoc]

private theorem functor_source_conjugation_inv
    {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
    (F : D₁ ⥤ D₂) {P Q X Y : D₁} (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) :
    (F.mapIso p.symm).inv ≫ F.map f =
      F.map (p.hom ≫ f ≫ q.inv) ≫ (F.mapIso q.symm).inv := by
  simp only [Functor.mapIso_inv, Iso.symm_inv, ← F.map_comp,
    Category.assoc, q.inv_hom_id, Category.comp_id]

private theorem functor_source_target_conjugation
    {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
    (F : D₁ ⥤ D₂ ⥤ D₂) {P Q X Y : D₁} (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y)
    {U V : D₂} (g : U ⟶ V) :
    (F.map f).app U ≫ (F.obj Y).map g ≫ (F.mapIso q.symm).hom.app V =
      (F.mapIso p.symm).hom.app U ≫
        (F.map (p.hom ≫ f ≫ q.inv)).app U ≫ (F.obj Q).map g := by
  have hs := NatTrans.congr_app (functor_source_conjugation F p q f) U
  have ht := (F.mapIso q.symm).hom.naturality g
  calc
    _ = (F.map f).app U ≫ ((F.mapIso q.symm).hom.app U ≫ (F.obj Q).map g) :=
      congrArg (fun k => (F.map f).app U ≫ k) ht
    _ = ((F.map f).app U ≫ (F.mapIso q.symm).hom.app U) ≫ (F.obj Q).map g :=
      (Category.assoc _ _ _).symm
    _ = ((F.mapIso p.symm).hom.app U ≫
        (F.map (p.hom ≫ f ≫ q.inv)).app U) ≫ (F.obj Q).map g :=
      congrArg (fun k => k ≫ _) hs
    _ = _ := Category.assoc _ _ _

/-- Both complete original source maps conjugate the full functor map. -/
private theorem functor_source_conjugation_map
    {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
    (F : D₁ ⥤ D₂) {P Q X Y : D₁} (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) :
    F.map f ≫ F.map q.inv = F.map p.inv ≫ F.map (p.hom ≫ f ≫ q.inv) := by
  simp only [← F.map_comp, p.inv_hom_id_assoc]

/-- The other complete original source maps retain the full inverse conjugation. -/
private theorem functor_source_conjugation_map_inv
    {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
    (F : D₁ ⥤ D₂) {P Q X Y : D₁} (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) :
    F.map p.hom ≫ F.map f = F.map (p.hom ≫ f ≫ q.inv) ≫ F.map q.hom := by
  simp only [← F.map_comp, Category.assoc, q.inv_hom_id, Category.comp_id]

/-- Both complete functor variables retain the original simultaneous map conjugation. -/
private theorem functor_source_target_conjugation_map
    {D₁ : Type uC} [Category.{vC} D₁] {D₂ : Type uD} [Category.{vD} D₂]
    (F : D₁ ⥤ D₂ ⥤ D₂) {P Q X Y : D₁} (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y)
    {U V : D₂} (g : U ⟶ V) :
    (F.map f).app U ≫ (F.obj Y).map g ≫ (F.map q.inv).app V =
      (F.map p.inv).app U ≫
        (F.map (p.hom ≫ f ≫ q.inv)).app U ≫ (F.obj Q).map g := by
  have hs := NatTrans.congr_app (functor_source_conjugation_map F p q f) U
  have ht := (F.map q.inv).naturality g
  calc
    _ = (F.map f).app U ≫ ((F.map q.inv).app U ≫ (F.obj Q).map g) :=
      congrArg (fun k => (F.map f).app U ≫ k) ht
    _ = ((F.map f).app U ≫ (F.map q.inv).app U) ≫ (F.obj Q).map g :=
      (Category.assoc _ _ _).symm
    _ = ((F.map p.inv).app U ≫
        (F.map (p.hom ≫ f ≫ q.inv)).app U) ≫ (F.obj Q).map g :=
      congrArg (fun k => k ≫ _) hs
    _ = _ := Category.assoc _ _ _

end FunctorTransport

section WholeModuleSourceTransport
universe uC vC uD vD
variable {C₀ : Type uC} [Category.{vC} C₀] [MonoidalCategory C₀]
  [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀]
  {D₀ : Type uD} [Category.{vD} D₀]

/-- Both original functor variables give the full carrier map of the relative tensor pair. -/
private theorem originalWholeSourceTransport_pair (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) {P Q : Mod C₀ A₀.X} (f : P ⟶ Q)
    {U V : D₀} (g : U ⟶ V) :
    ((originalWholeSourceTransport A₀ E₀).map f).app U ≫
        ((originalWholeSourceTransport A₀ E₀).obj Q).map g =
      E₀.functor.map (Mod.relativeTensorMap A₀ f (E₀.inverse.map g)) :=
  (E₀.functor.map_comp _ _).symm

/-- The entire source comparison uses both original module maps and the actual source formula. -/
private theorem wholeModuleSource_conjugation (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) {P Q X Y : Mod C₀ A₀.X}
    (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) (g : P ⟶ Q)
    (hg : g = p.hom ≫ f ≫ q.inv) :
    (originalWholeSourceTransport A₀ E₀).map f ≫
        ((originalWholeSourceTransport A₀ E₀).mapIso q.symm).hom =
      ((originalWholeSourceTransport A₀ E₀).mapIso p.symm).hom ≫
        Functor.whiskerLeft E₀.inverse
          (Functor.whiskerRight ((Mod.relativeTensor A₀).map g) E₀.functor) := by
  have h := functor_source_conjugation (originalWholeSourceTransport A₀ E₀) p q f
  rw [← hg] at h
  exact h

/-- The inverse entire source comparison retains both original full module maps. -/
private theorem wholeModuleSource_conjugation_inv (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) {P Q X Y : Mod C₀ A₀.X}
    (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) (g : P ⟶ Q)
    (hg : g = p.hom ≫ f ≫ q.inv) :
    ((originalWholeSourceTransport A₀ E₀).mapIso p.symm).inv ≫
        (originalWholeSourceTransport A₀ E₀).map f =
      Functor.whiskerLeft E₀.inverse
        (Functor.whiskerRight ((Mod.relativeTensor A₀).map g) E₀.functor) ≫
          ((originalWholeSourceTransport A₀ E₀).mapIso q.symm).inv := by
  have h := functor_source_conjugation_inv (originalWholeSourceTransport A₀ E₀) p q f
  rw [← hg] at h
  exact h

/-- Both full functor variables retain the actual original relative tensor pair under comparison. -/
private theorem wholeModuleSource_target_conjugation (A₀ : CommMon C₀)
    (E₀ : Mod C₀ A₀.X ≌ D₀) {P Q X Y : Mod C₀ A₀.X}
    (p : P ≅ X) (q : Q ≅ Y) (f : X ⟶ Y) (g : P ⟶ Q)
    (hg : g = p.hom ≫ f ≫ q.inv) {U V : D₀} (k : U ⟶ V) :
    ((originalWholeSourceTransport A₀ E₀).map f).app U ≫
        ((originalWholeSourceTransport A₀ E₀).obj Y).map k ≫
        ((originalWholeSourceTransport A₀ E₀).mapIso q.symm).hom.app V =
      ((originalWholeSourceTransport A₀ E₀).mapIso p.symm).hom.app U ≫
        E₀.functor.map (Mod.relativeTensorMap A₀ g (E₀.inverse.map k)) := by
  have h := functor_source_target_conjugation (originalWholeSourceTransport A₀ E₀) p q f k
  rw [← hg, originalWholeSourceTransport_pair] at h
  exact h

end WholeModuleSourceTransport

private def freeSmashSourceTransport :
    Mod C.{u, v} S.{u, v} ⥤ (SymmetricSpectrum.{u, v} ⥤ SymmetricSpectrum.{u, v}) :=
  originalWholeSourceTransport sphereSequenceCommMon.{u, v}
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

private theorem freeSmashSourceTransport_free (r : I) (M : V.{u, v}) :
    freeSmashSourceTransport.{u, v}.obj ((freeAt r ⋙ toModule.{u, v}).obj M) =
      freeSmash r M := rfl

private theorem freeSmashSourceTransport_original (r : I) (M : V.{u, v}) :
    freeSmashSourceTransport.{u, v}.obj ((Mod.dayFreeAt sphereSequence.{u, v} r).obj M) =
      toModule.{u, v} ⋙ ((Mod.relativeTensor A.{u, v}).obj
        ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))) ⋙ E.{u, v}.functor := by
  dsimp only [Mod.dayFreeAt, freeDiagram, representedDiagram,
    Functor.comp_obj, Equivalence.symm_functor]
  exact originalWholeSourceTransport_obj A.{u, v} E.{u, v} _

private theorem freeSmashSourceTransport_map {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) :
    (fun (C₀ : Type _) [Category.{v} C₀] [MonoidalCategory C₀]
      [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀]
      (D₀ : Type _) [Category.{v} D₀]
      (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀) (X Y : D₀) (h : X ⟶ Y) =>
      Eq (α := (originalWholeSourceTransport A₀ E₀).obj (E₀.inverse.obj X) ⟶
        (originalWholeSourceTransport A₀ E₀).obj (E₀.inverse.obj Y))
        ((originalWholeSourceTransport A₀ E₀).map (E₀.inverse.map h))
        (CategoryTheory.Mod.EquivalenceFunctionTransport.sourceSmashMap A₀ E₀ h))
      C.{u, v} SymmetricSpectrum.{u, v} sphereSequenceCommMon.{u, v}
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
      ((freeAt.{u, v} s).obj N) ((freeAt.{u, v} r).obj M) f :=
  originalWholeSourceTransport_map (C₀ := C.{u, v}) (D₀ := SymmetricSpectrum.{u, v})
    sphereSequenceCommMon.{u, v} SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    (X := (freeAt.{u, v} s).obj N) (Y := (freeAt.{u, v} r).obj M) f

private theorem freeSmashSourceTransport_iso (r : I) (M : V.{u, v}) :
    Eq (α := freeSmash r M ≅
      toModule.{u, v} ⋙ ((Mod.relativeTensor sphereSequenceCommMon.{u, v}).obj
        (CorrelatedFreeSource.originalFree r M)) ⋙
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor)
      (freeSmashSourceTransport.{u, v}.mapIso ((freeModuleComparison r).app M).symm)
      (freeSmashModuleNatIso r M) := rfl

/-- The entire forward transformation is the same original relative-tensor carrier map. -/
private theorem freeSmashSourceTransport_iso_hom (r : I) (M : V.{u, v}) :
    Eq (α := freeSmash r M ⟶
      toModule.{u, v} ⋙ ((Mod.relativeTensor sphereSequenceCommMon.{u, v}).obj
        (CorrelatedFreeSource.originalFree r M)) ⋙
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor)
      (freeSmashSourceTransport.{u, v}.map (((freeModuleComparison r).app M).inv))
      (freeSmashModuleNatIso r M).hom := rfl

/-- The entire inverse retains the other original carrier map and both full endpoints. -/
private theorem freeSmashSourceTransport_iso_inv (r : I) (M : V.{u, v}) :
    Eq (α := (toModule.{u, v} ⋙ ((Mod.relativeTensor sphereSequenceCommMon.{u, v}).obj
        (CorrelatedFreeSource.originalFree r M)) ⋙
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor) ⟶ freeSmash r M)
      (freeSmashSourceTransport.{u, v}.map (((freeModuleComparison r).app M).hom))
      (freeSmashModuleNatIso r M).inv := rfl

private theorem freeSmashSourceTransport_source_map {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) :
    (fun (C₀ : Type _) [Category.{v} C₀] [MonoidalCategory C₀]
      [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀]
      (D₀ : Type _) [Category.{v} D₀]
      (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀) (P Q : Mod C₀ A₀.X) (h : P ⟶ Q) =>
      Eq (α := (originalWholeSourceTransport A₀ E₀).obj P ⟶
        (originalWholeSourceTransport A₀ E₀).obj Q)
        ((originalWholeSourceTransport A₀ E₀).map h)
        (Functor.whiskerLeft E₀.inverse
          (Functor.whiskerRight ((Mod.relativeTensor A₀).map h) E₀.functor)))
      C.{u, v} SymmetricSpectrum.{u, v} sphereSequenceCommMon.{u, v}
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
      (CorrelatedFreeSource.originalFree.{u, v} s N)
      (CorrelatedFreeSource.originalFree.{u, v} r M)
      (@CorrelatedFreeSource.sourceArrow.{u, v} r s M N f) :=
  (fun (C₀ : Type _) [Category.{v} C₀] [MonoidalCategory C₀]
      [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀]
      (D₀ : Type _) [Category.{v} D₀]
      (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀) (P Q : Mod C₀ A₀.X) (h : P ⟶ Q) =>
      (rfl : Eq (α := (originalWholeSourceTransport A₀ E₀).obj P ⟶
        (originalWholeSourceTransport A₀ E₀).obj Q)
        ((originalWholeSourceTransport A₀ E₀).map h)
        (Functor.whiskerLeft E₀.inverse
          (Functor.whiskerRight ((Mod.relativeTensor A₀).map h) E₀.functor))))
      C.{u, v} SymmetricSpectrum.{u, v} sphereSequenceCommMon.{u, v}
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
      (CorrelatedFreeSource.originalFree.{u, v} s N)
      (CorrelatedFreeSource.originalFree.{u, v} r M)
      (@CorrelatedFreeSource.sourceArrow.{u, v} r s M N f)

private theorem freeSmashSourceTransport_pair_map {P Q : Mod C.{u, v} S.{u, v}}
    (f : P ⟶ Q) {Y Z : SymmetricSpectrum.{u, v}} (g : Y ⟶ Z) :
    (fun (C₀ : Type _) [Category.{v} C₀] [MonoidalCategory C₀]
      [BraidedCategory C₀] [MonoidalClosed C₀] [HasCoequalizers C₀]
      (D₀ : Type _) [Category.{v} D₀]
      (A₀ : CommMon C₀) (E₀ : Mod C₀ A₀.X ≌ D₀) (P Q : Mod C₀ A₀.X) (h : P ⟶ Q)
      (U V : D₀) (k : U ⟶ V) =>
      Eq (α := ((originalWholeSourceTransport A₀ E₀).obj P).obj U ⟶
        ((originalWholeSourceTransport A₀ E₀).obj Q).obj V)
        (((originalWholeSourceTransport A₀ E₀).map h).app U ≫
          ((originalWholeSourceTransport A₀ E₀).obj Q).map k)
        (E₀.functor.map (Mod.relativeTensorMap A₀ h (E₀.inverse.map k))))
      C.{u, v} SymmetricSpectrum.{u, v} sphereSequenceCommMon.{u, v}
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} P Q f Y Z g :=
  originalWholeSourceTransport_pair (C₀ := C.{u, v}) (D₀ := SymmetricSpectrum.{u, v})
    sphereSequenceCommMon.{u, v} SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    (P := P) (Q := Q) f (U := Y) (V := Z) g

/-- The actual entire source arrow uses the original full source objects and both original maps. -/
private theorem wholeOriginalSourceArrow_formula {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) :
    Eq (α := (Mod.free S.{u, v}).obj (freeDiagram.{u, v} s N) ⟶
      (Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))
      (CorrelatedFreeSource.sourceArrow f)
      ((wholeOriginalFreeModuleIso s N).hom ≫ toModule.{u, v}.map f ≫
        (wholeOriginalFreeModuleIso r M).inv) := rfl

/-- `exact_whole_typed_source p` uses a completely elaborated proof term `p`.
It skips eager elaborator conversion to the goal. Lean's kernel checks the full
declared theorem type. The argument is supplied explicitly by the caller. -/
local elab (name := exactWholeTypedSourceApplication)
    "exact_whole_typed_source " typedProof:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let body ← Lean.Elab.Term.elabTerm typedProof none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let body ← Lean.instantiateMVars body
    unless !body.hasMVar && !body.hasLevelMVar && !body.hasSorry do
      throwError "The complete supplied typed proof is unresolved"
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign body
    Lean.Elab.Tactic.replaceMainGoal []

/-- Every arbitrary native free-source arrow commutes with both whole
balanced-smash comparisons, as an equality of natural transformations
on the entire target-spectrum category. -/
theorem freeSmashSource_comparison {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) :
    freeSmashSourceMap f ≫ (freeSmashModuleNatIso r M).hom =
      (freeSmashModuleNatIso s N).hom ≫
        Functor.whiskerLeft toModule.{u, v}
          (Functor.whiskerRight
            ((Mod.relativeTensor sphereSequenceCommMon.{u, v}).map
              (CorrelatedFreeSource.sourceArrow f))
            SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor) := by
  have he := @wholeModuleSource_conjugation
      C.{u, v} (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)
      SymmetricSpectrum.{u, v} (inferInstance) A.{u, v} E.{u, v}
      ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} s N))
      ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))
      (toModule.{u, v}.obj ((freeAt.{u, v} s).obj N))
      (toModule.{u, v}.obj ((freeAt.{u, v} r).obj M))
      (wholeOriginalFreeModuleIso s N) (wholeOriginalFreeModuleIso r M)
      (toModule.{u, v}.map f)
      (@CorrelatedFreeSource.sourceArrow.{u, v} r s M N f)
      (@wholeOriginalSourceArrow_formula.{u, v} r s M N f)
  exact_whole_typed_source he


/-- The inverse whole balanced-smash comparisons retain the same
arbitrary correlated source transformation on every target spectrum. -/
theorem freeSmashSource_comparison_inv {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M) :
    (freeSmashModuleNatIso s N).inv ≫ freeSmashSourceMap f =
      Functor.whiskerLeft toModule.{u, v}
        (Functor.whiskerRight
          ((Mod.relativeTensor sphereSequenceCommMon.{u, v}).map
              (CorrelatedFreeSource.sourceArrow f))
          SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor) ≫
          (freeSmashModuleNatIso r M).inv := by
  have he := @wholeModuleSource_conjugation_inv
      C.{u, v} (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)
      SymmetricSpectrum.{u, v} (inferInstance) A.{u, v} E.{u, v}
      ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} s N))
      ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))
      (toModule.{u, v}.obj ((freeAt.{u, v} s).obj N))
      (toModule.{u, v}.obj ((freeAt.{u, v} r).obj M))
      (wholeOriginalFreeModuleIso s N) (wholeOriginalFreeModuleIso r M)
      (toModule.{u, v}.map f)
      (@CorrelatedFreeSource.sourceArrow.{u, v} r s M N f)
      (@wholeOriginalSourceArrow_formula.{u, v} r s M N f)
  exact_whole_typed_source he


/-- An arbitrary entire free-source arrow and an arbitrary entire target
arrow commute simultaneously with the original balanced relative tensor
map under the whole free-smash comparisons. -/
theorem freeSmashSource_target_comparison {r s : I} {M N : V.{u, v}}
    (f : (freeAt.{u, v} s).obj N ⟶ (freeAt.{u, v} r).obj M)
    {Y Z : SymmetricSpectrum.{u, v}} (g : Y ⟶ Z) :
    (freeSmashSourceMap f).app Y ≫ (freeSmash r M).map g ≫
        (freeSmashModuleNatIso r M).hom.app Z =
      (freeSmashModuleNatIso s N).hom.app Y ≫
        SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor.map
          (Mod.relativeTensorMap sphereSequenceCommMon.{u, v} (CorrelatedFreeSource.sourceArrow f)
            (toModule.{u, v}.map g)) := by
  have he := @wholeModuleSource_target_conjugation
      C.{u, v} (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)
      SymmetricSpectrum.{u, v} (inferInstance) A.{u, v} E.{u, v}
      ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} s N))
      ((Mod.free S.{u, v}).obj (freeDiagram.{u, v} r M))
      (toModule.{u, v}.obj ((freeAt.{u, v} s).obj N))
      (toModule.{u, v}.obj ((freeAt.{u, v} r).obj M))
      (wholeOriginalFreeModuleIso s N) (wholeOriginalFreeModuleIso r M)
      (toModule.{u, v}.map f)
      (@CorrelatedFreeSource.sourceArrow.{u, v} r s M N f)
      (@wholeOriginalSourceArrow_formula.{u, v} r s M N f) Y Z g
  exact_whole_typed_source he


end PointedCGWH.SymmetricSpectrum
