/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceGEN
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientZeroUnit
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceData
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeSelectedUnitMate
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceGENSupport.OriginalCompleteGenericNativeSourceAction
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FixedFirstGEN.NativeSourceGENFirstDayReadbackHelper2
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.StabilizationAction
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.StabilizationTransformation
import Lean.Util.ShareCommon
import Lean.Elab.Command
import Lean.Elab.DeclarationRange
import Lean.Util.CollectLevelParams

/-!
# The original symmetric NativeSymmetricDelooping.firstIndex source and its native stabilization

The original free-source comparison, zero-unit mate, module precomposition and
balanced tensor action retain every native module and output index. Ordinary
source-transport laws identify the whole native coaugmentation with that action;
the original sphere-unit generator supplies its NativeSymmetricDelooping.firstIndex coefficient inverse.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uD vD

open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.WholeOriginalGEN


attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

attribute [local irreducible] Mod.internalHom

private abbrev A : CommMon PointedCGWH.SymmetricSequence.{u, v} where
  X := PointedCGWH.sphereSequence.{u, v}
  mon := PointedCGWH.sphereSequenceMonObj.{u, v}
  comm := PointedCGWH.sphereSequenceIsCommMonObj.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The complete original module/operator equivalence at one shared value getter. -/
abbrev originalCarrierEquivalence : NativeSymmetricFreeFunction.OriginalModule.{u, v} ≌
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} := E.{u, v}

open Lean Lean.Meta Lean.Elab Term
/-- Elaborate a complete source proof and share its subexpressions while retaining its original
type and term. -/
syntax (name := symmetricGenSharedProof) "symmetricGenSharedProof% " term:max : term
@[term_elab symmetricGenSharedProof]
private def elabSymmetricGenSharedProof : TermElab := fun stx expectedType? => do
  let some expectedType := expectedType? |
    throwError "The complete native source statement must be stated independently"
  let originalType ← instantiateMVars expectedType
  let originalProof ← instantiateMVars (← elabTerm stx[1] none)
  let shared := Lean.ShareCommon.shareCommon (originalType, originalProof)
  unless shared.1 == originalType && shared.2 == originalProof do
    throwError "Sharing changed the complete native statement or proof expression"
  return shared.2


/-- Elaborate a source proof against the shared expected type and retain the original statement
and proof expression. -/
syntax (name := symmetricGenSharedGoalProof) "symmetricGenSharedGoalProof% " term:max : term
@[term_elab symmetricGenSharedGoalProof]
private def elabSymmetricGenSharedGoalProof : TermElab := fun stx expectedType? => do
  let some expectedType := expectedType? |
    throwError "The complete native source statement must be stated independently"
  let originalType ← instantiateMVars expectedType
  let sharedType := Lean.ShareCommon.shareCommon originalType
  let originalProof ← instantiateMVars (← elabTerm stx[1] (some sharedType))
  let shared := Lean.ShareCommon.shareCommon (sharedType, originalProof)
  unless shared.1 == originalType && shared.2 == originalProof do
    throwError "Sharing changed the complete native statement or proof expression"
  return shared.2

open Lean.Elab.Command

/-- Declare a closed source theorem with shared expression storage and original source metadata. -/
syntax (name := symmetricGenSharedDeclaration) (docComment)?
  "symmetricGenSharedDeclaration% " ident " : " term " := " term : command

@[command_elab symmetricGenSharedDeclaration]
private def elabSymmetricGenSharedDeclaration : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[2].getId
  runTermElabM fun vars => do
    unless vars.isEmpty do
      throwError "This source-local sharing command requires a supplied closed statement"
    Term.withDeclName declName do
      let type ← Term.elabType stx[4]
      let proof ← Term.elabTermEnsuringType stx[6] type
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← Term.levelMVarToParam (← instantiateMVars type)
      let proof ← instantiateMVars proof
      let scopeLevels ← Term.getLevelNames
      let used := collectLevelParams (collectLevelParams {} type) proof |>.params
      let levelParams ← match sortDeclLevelParams scopeLevels [] used with
        | .ok levels => pure levels
        | .error message => throwError message
      let shared := Lean.ShareCommon.shareCommon (type, proof)
      unless Expr.equal type shared.1 && Expr.equal proof shared.2 do
        throwError "Sharing changed the supplied closed statement or proof"
      let declaration := Declaration.thmDecl {
        name := declName, levelParams := levelParams, type := shared.1, value := shared.2 }
      Term.ensureNoUnassignedMVars declaration
      addAndCompile declaration
      addDeclarationRangesFromSyntax declName stx stx[2]
      if stx[0].getNumArgs > 0 then
        addDocString declName stx[2] ⟨stx[0][0]⟩
      withSaveInfoContext do
        Term.addTermInfo' stx[2] (← mkConstWithLevelParams declName) (isBinder := true)

private theorem module_source_square_nat
    {V : Type uC} [Category.{vC} V] [MonoidalCategory V] [BraidedCategory V]
    [MonoidalClosed V] [HasCoequalizers V] [HasEqualizers V]
    (B : CommMon V) {D : Type uD} [Category.{vD} D] (e : Mod V B.X ≌ D)
    (M M' : Mod V B.X) (g : M' ⟶ M)
    (hS : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B e).obj (.op M) =
      e.inverse ⋙ Mod.internalHom B M ⋙ e.functor)
    (hS' : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B e).obj (.op M') =
      e.inverse ⋙ Mod.internalHom B M' ⋙ e.functor) :
    (eqToIso hS).inv ≫
        (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B e).map g.op ≫
        (eqToIso hS').hom =
      Functor.whiskerLeft e.inverse
        (Functor.whiskerRight (SourceImageWord.boundModulePre B M M' g) e.functor) := by
  have h := SourceImageWord.raw_source_square B e M M' g rfl rfl hS hS'
  simpa only [SourceImageWord.rawSourcePre, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp, Category.comp_id] using h


open NativeSymmetricFreeFunction
private abbrev NativeCarrier :=
  EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

set_option maxHeartbeats 500000 in
/-- The standard carrier-word identity on the exact original native category,
with arbitrary typed functors and the three ordinary unit, tail and pre-map laws. -/
theorem native_compose_source_image_word_nat
    {F G : OriginalModule.{u, v} ⥤ OriginalModule.{u, v}}
    {R R' S T : NativeCarrier.{u, v} ⥤ NativeCarrier.{u, v}}
    {e : F ≅ E.{u, v}.functor ⋙ R ⋙ E.{u, v}.inverse}
    {e' : G ≅ E.{u, v}.functor ⋙ R' ⋙ E.{u, v}.inverse}
    {u₀ : R ≅ 𝟭 NativeCarrier.{u, v}} {p : F ⟶ G}
    {w : S ≅ 𝟭 NativeCarrier.{u, v}}
    {s : S ≅ E.{u, v}.inverse ⋙ F ⋙ E.{u, v}.functor}
    {s' : T ≅ E.{u, v}.inverse ⋙ G ⋙ E.{u, v}.functor}
    {q : S ⟶ T} {c : T ≅ R'}
    (hu : ∀ N : OriginalModule.{u, v}, w.inv.app (E.{u, v}.functor.obj N) =
      E.{u, v}.functor.map (E.{u, v}.unitIso.hom.app N ≫
        E.{u, v}.inverse.map (u₀.inv.app (E.{u, v}.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.{u, v}.unitIso.hom.app N)) ≫
            s.inv.app (E.{u, v}.functor.obj N))
    (hc : ∀ N : OriginalModule.{u, v}, c.hom.app (E.{u, v}.functor.obj N) =
      s'.hom.app (E.{u, v}.functor.obj N) ≫
        E.{u, v}.functor.map (e'.hom.app (E.{u, v}.inverse.obj (E.{u, v}.functor.obj N))) ≫
          E.{u, v}.counitIso.hom.app
            (R'.obj (E.{u, v}.functor.obj (E.{u, v}.inverse.obj (E.{u, v}.functor.obj N)))) ≫
              R'.map (E.{u, v}.counitIso.hom.app (E.{u, v}.functor.obj N)))
    (hq : ∀ N : OriginalModule.{u, v}, s.inv.app (E.{u, v}.functor.obj N) ≫
      q.app (E.{u, v}.functor.obj N) ≫ s'.hom.app (E.{u, v}.functor.obj N) =
        E.{u, v}.functor.map (p.app (E.{u, v}.inverse.obj (E.{u, v}.functor.obj N)))) :
    Functor.whiskerLeft E.{u, v}.functor (w.inv ≫ q ≫ c.hom) =
      SourceImageWord.carrierWord E.{u, v} e e' u₀ p :=
  symmetricGenSharedProof% (SourceImageWord.compose_source_image_word_nat
    (E := E.{u, v}) (F := F) (G := G) (R := R) (R' := R') (S := S) (T := T)
    (e := e) (e' := e') (u := u₀) (p := p) (w := w) (s := s) (s' := s')
    (q := q) (c := c) hu hc hq)


private theorem moduleWord_of_whole_mate
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : C ≌ D) {F G : C ⥤ C} {R R' : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : G ≅ E.functor ⋙ R' ⋙ E.inverse) (u : R ≅ 𝟭 D) (p : F ⟶ G)
    (c : 𝟭 C ⟶ F)
    (h : c ≫ e.hom = E.unitIso.hom ≫
      Functor.whiskerLeft E.functor (Functor.whiskerRight u.inv E.inverse)) :
    SourceImageWord.moduleWord E e e' u p = c ≫ p ≫ e'.hom := by
  unfold SourceImageWord.moduleWord
  have hm : E.unitIso.hom ≫
      Functor.whiskerLeft E.functor (Functor.whiskerRight u.inv E.inverse) ≫ e.inv = c := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ e.inv) h.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => c ≫ t) e.hom_inv_id).trans (Category.comp_id c))))
  simpa only [Category.assoc] using congrArg (fun t => t ≫ p ≫ e'.hom) hm

private theorem cancel_original_source_word
    {C : Type uC} [Category.{vC} C] {A A' B B' Z Q : C}
    (e : A ≅ B) (e' : A' ≅ B') (p : B ⟶ B') (q : A ⟶ A')
    (u : B ≅ Z) (w : A ≅ Z) (c : A' ≅ Q)
    (hNat : e.hom ≫ p = q ≫ e'.hom) (hUnit : u.inv ≫ e.inv = w.inv) :
    (u.inv ≫ p) ≫ (e'.symm ≪≫ c).hom = w.inv ≫ q ≫ c.hom := by
  have hPre : p ≫ e'.inv = e.inv ≫ q := by
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, e'.inv_hom_id, Category.comp_id]
    rw [← hNat, e.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc p e'.inv, hPre]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ q ≫ c.hom) hUnit

private theorem contraction_pre_nat
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (A : CommMon C)
    (M M' : Mod C A.X) (f : M ⟶ M') (q : M' ⟶ Mod.regular A.X) :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A
    SelectedUnitTensorCompatibility.contractionCurrySource A M' q ≫ MonoidalClosed.pre f =
      SelectedUnitTensorCompatibility.contractionCurrySource A M (f ≫ q) := by
  let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  let _ : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A
  apply NatTrans.ext
  funext N
  exact (BalancedSourceAction.action_pre A f q N).symm

private theorem module_source_square_app
    {V : Type uC} [Category.{vC} V] [MonoidalCategory V] [BraidedCategory V]
    [MonoidalClosed V] [HasCoequalizers V] [HasEqualizers V]
    (A : CommMon V) {D : Type uD} [Category.{vD} D] (E : Mod V A.X ≌ D)
    (M M' : Mod V A.X) (g : M' ⟶ M)
    (hS : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).obj (.op M) =
      E.inverse ⋙ Mod.internalHom A M ⋙ E.functor)
    (hS' : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).obj (.op M') =
      E.inverse ⋙ Mod.internalHom A M' ⋙ E.functor) (X : D) :
    (eqToIso hS).inv.app X ≫
        ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map g.op).app X ≫
        (eqToIso hS').hom.app X =
      E.functor.map ((SourceImageWord.boundModulePre A M M' g).app (E.inverse.obj X)) := by
  have h := SourceImageWord.raw_source_square A E M M' g rfl rfl hS hS'
  have hX := NatTrans.congr_app h X
  simpa only [SourceImageWord.rawSourcePre,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using hX


/-- The tensor of modules over the commutative symmetric sphere sequence. -/
local instance originalModuleMonoidal : MonoidalCategory NativeSymmetricFreeFunction.OriginalModule.{u, v} :=
  Mod.instMonoidalCategory A.{u, v}
/-- The internal Hom structure on modules over the commutative symmetric sphere sequence. -/
local instance originalModuleClosed : MonoidalClosed NativeSymmetricFreeFunction.OriginalModule.{u, v} :=
  Mod.instMonoidalClosed A.{u, v}

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction NativeSymmetricFreeSource NativeSymmetricSourceMatch

/-- The whole original NativeSymmetricDelooping.firstIndex comparison is the native lambda followed by its original R
iso. -/
abbrev originalFirstComparison : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) ⟶
    PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex ⋙ cotensor PointedCGWH.sphereOne.{u,
      v} :=
  NativeSymmetricLambda.coaugmentation.{u, v} ≫ NativeSymmetricR.comparison.{u, v}.hom

/-- The complete NativeSymmetricDelooping.firstIndex module source keeps both original free-source isomorphisms. -/
abbrev originalFirstModuleSource :=
  FirstCoefficient.DayReadback.originalFirstModuleArrow.{u, v}

private abbrev moduleHom (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
  NativeSymmetricFreeFunction.OriginalModule.{u, v} ⥤ NativeSymmetricFreeFunction.OriginalModule.{u, v} :=
  Mod.internalHom A.{u, v} (freeModule.{u, v} r K)
private abbrev target (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :=
  PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor K

/-- The current module comparison has the same complete original free internal-Hom source. -/
private theorem moduleComparison_source (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
    NativeScalarCoefficient.originalComparisonSourceFunctor.{u, v} r K = moduleHom.{u, v} r K :=
  (actualSource_eq_recipe r K).trans (chosenHomSource_eq_recipe r K).symm

/-- Only the proved whole source equality changes in the actual module comparison. -/
private def moduleComparison (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
    moduleHom.{u, v} r K ≅ E.{u, v}.functor ⋙ target.{u, v} r K ⋙ E.{u, v}.inverse :=
  NativeSelectedUnitTransport.rebaseComparison (moduleComparisonNat.{u, v} r K)
    (moduleComparison_source r K)

private theorem sourceTransport_source (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r K =
      E.{u, v}.inverse ⋙ moduleHom.{u, v} r K ⋙ E.{u, v}.functor := by
  exact (ActualSourceFunctor.free_sourceFunctor_obj_original.{u, v} r K).trans
    (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj
      (C := PointedCGWH.SymmetricSequence.{u, v})
      (D := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
      A.{u, v} E.{u, v} (freeModule.{u, v} r K))

private def sourceTransport (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
    NativeOmegaPreparation.SymmetricFunction.functor.{u, v} r K ≅
      E.{u, v}.inverse ⋙ moduleHom.{u, v} r K ⋙ E.{u, v}.functor :=
  eqToIso (sourceTransport_source r K)

/-- The original carrier recovery is the ordinary complete module-counit tail. -/
private theorem comparison_eq_source_tail (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
    comparison.{u, v} r K = sourceTransport r K ≪≫
      SourceEquality.moduleTail E.{u, v} (moduleComparison r K) := by
  have hOld := comparison_eq_actualSourceTail.{u, v} r K
  dsimp only [actualCoefficientSourceTransport, actualComparisonTail,
    NativeScalarCoefficient.coefficientOperatorEquivalence, ModuleCoefficientData.carrierEquivalence] at hOld
  exact hOld.trans (SourceImageWord.sourceTail_rebase
    (C := NativeSymmetricFreeFunction.OriginalModule.{u, v}) (D := (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v})) (R := target.{u, v} r K) E.{u, v}
    (moduleComparisonNat.{u, v} r K) (moduleComparison_source r K)
    (nativeSource_eq_actualComparisonSource r K) (sourceTransport_source r K))

private def sourceUnit := OriginalCarrierZeroSourceUnit.sourceUnitFromModule E.{u, v}
  (moduleComparison (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) zeroScalarIndexUnit.{u, v}
  (sourceTransport (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))

private theorem sourceUnit_eq_original :
    comparisonSourceUnit.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}) zeroScalarIndexUnit.{u, v} =
      sourceUnit.{u, v} := by
  have h := NativeSelectedUnitTransport.sourceUnit_rebase E.{u, v}
    (moduleComparisonNat.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    zeroScalarIndexUnit.{u, v}
    (moduleComparison_source (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (nativeSource_eq_actualComparisonSource (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (sourceTransport_source (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
  unfold sourceUnit sourceTransport moduleComparison comparisonSourceUnit
  exact h

/-- Ordinary source naturality cancels the two native free-source prefixes as whole maps. -/
theorem original_firstSource_source_word :
    originalFirstComparison.{u, v} = sourceUnit.{u, v}.inv ≫
      NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
        originalFirstModuleSource.{u, v} ≫ (comparison.{u, v} NativeSymmetricDelooping.firstIndex
          PointedCGWH.sphereOne.{u, v}).hom := by
  let e₀ := NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
    (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})
  let e₁ := NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v}
    NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}
  let p := NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v}
    NativeSymmetricLambda.firstSource.{u, v}
  let q := NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
    originalFirstModuleSource.{u, v}
  have hNat : e₀.hom ≫ p = q ≫ e₁.hom :=
    originalFreeComparison_precompose NativeSymmetricLambda.firstSource.{u, v}
  have hUnit : nativeUnitComparison.{u, v}.inv ≫ e₀.inv = sourceUnit.{u, v}.inv :=
    nativeUnitComparison_inverse_source_prefix.{u, v}.trans
      (congrArg Iso.inv sourceUnit_eq_original.{u, v})
  have hR : NativeSymmetricR.comparison.{u, v} =
      e₁.symm ≪≫ comparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v} := rfl
  have h := cancel_original_source_word e₀ e₁ p q nativeUnitComparison.{u, v} sourceUnit.{u, v}
    (comparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}) hNat hUnit
  have hValue := congrArg (fun e => NativeSymmetricLambda.coaugmentation.{u, v} ≫ e.hom) hR
  exact hValue.trans h

private def modulePre : moduleHom.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}) ⟶
    moduleHom.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v} :=
  SourceImageWord.boundModulePre A.{u, v}
    (freeModule.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (freeModule.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    originalFirstModuleSource.{u, v}

/-- The entire original unit, scalar inverse and source pre-map form the original module word. -/
def originalFirstRawModuleWord : 𝟭 NativeSymmetricFreeFunction.OriginalModule.{u, v} ⟶
    targetModuleFunctor.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v} :=
  SourceImageWord.moduleWord E.{u, v}
    (moduleComparison (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (moduleComparison NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}) zeroScalarIndexUnit.{u, v}
    modulePre.{u, v}


set_option maxHeartbeats 500000 in
/-- The entire native source square is the original transported module pre-map,
with every source index, coefficient, free-module arrow and carrier map retained. -/
theorem native_pre_source_square_nat
    (r s : Operad.SmallFinBijGroupoid) (K L : PointedCGWH.{u, v})
    (g : freeModule.{u, v} s L ⟶ freeModule.{u, v} r K) :
    (sourceTransport.{u, v} r K).inv ≫
      NativeOmegaPreparation.SymmetricFunction.precompose.{u, v} g ≫
      (sourceTransport.{u, v} s L).hom =
    Functor.whiskerLeft E.{u, v}.inverse
      (Functor.whiskerRight
        (SourceImageWord.boundModulePre A.{u, v} (freeModule.{u, v} r K)
          (freeModule.{u, v} s L) g) E.{u, v}.functor) :=
  symmetricGenSharedProof% (module_source_square_nat
    (V := PointedCGWH.SymmetricSequence.{u, v})
    (D := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    A.{u, v} E.{u, v} (freeModule.{u, v} r K) (freeModule.{u, v} s L) g
    (sourceTransport_source.{u, v} r K) (sourceTransport_source.{u, v} s L))

set_option maxHeartbeats 500000 in
/-- Every original native input reads back the same entire module pre-map. -/
theorem native_pre_source_square_app
    (r s : Operad.SmallFinBijGroupoid) (K L : PointedCGWH.{u, v})
    (g : freeModule.{u, v} s L ⟶ freeModule.{u, v} r K)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    (sourceTransport.{u, v} r K).inv.app X ≫
      (NativeOmegaPreparation.SymmetricFunction.precompose.{u, v} g).app X ≫
      (sourceTransport.{u, v} s L).hom.app X =
      E.{u, v}.functor.map
        ((SourceImageWord.boundModulePre A.{u, v} (freeModule.{u, v} r K)
          (freeModule.{u, v} s L) g).app (E.{u, v}.inverse.obj X)) := by
  have h := NatTrans.congr_app (native_pre_source_square_nat r s K L g) X
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using h


set_option maxHeartbeats 1000000 in
/-- The whole native source word is precisely the original carrier image of the module word. -/
symmetricGenSharedDeclaration% original_firstSource_whole_normalized_image :
    Functor.whiskerLeft E.{u, v}.functor originalFirstComparison.{u, v} =
      SourceImageWord.carrierWord E.{u, v}
        (moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
        (moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
          zeroScalarIndexUnit.{u, v}
        modulePre.{u, v} := symmetricGenSharedGoalProof% (by
  refine (congrArg (Functor.whiskerLeft E.{u, v}.functor)
    original_firstSource_source_word.{u, v}).trans ?_
  apply native_compose_source_image_word_nat
    (F := moduleHom.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (G := moduleHom.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    (e := moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (e' := moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    (u₀ := zeroScalarIndexUnit.{u, v}) (p := modulePre.{u, v})
    (w := sourceUnit.{u, v})
    (s := sourceTransport.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (s' := sourceTransport.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    (q := NativeOmegaPreparation.SymmetricFunction.precompose.{u, v} originalFirstModuleSource.{u, v})
    (c := comparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
  · intro N
    exact OriginalCarrierZeroSourceUnit.sourceUnitFromModule_inv_on_image_of_value E.{u, v}
      (moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) zeroScalarIndexUnit.{u, v}
      (sourceTransport.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})) sourceUnit.{u, v} rfl N
  · intro N
    exact SourceImageWord.sourceTail_hom_app E.{u, v}
      (moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
      (sourceTransport.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
      (comparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
      (comparison_eq_source_tail.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}) (E.{u,
        v}.functor.obj N)
  · intro N
    exact native_pre_source_square_app.{u, v}
      (𝟙_ Operad.SmallFinBijGroupoid) NativeSymmetricDelooping.firstIndex
      (𝟙_ PointedCGWH.{u, v}) PointedCGWH.sphereOne.{u, v}
      originalFirstModuleSource.{u, v} (E.{u, v}.functor.obj N)

)

set_option maxHeartbeats 500000 in
/-- The full original module-to-operator map and recovery counit read back the
same underlying module map at every native output, for every entire target functor. -/
theorem carrier_image_component
    (R : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (w : 𝟭 OriginalModule.{u, v} ⟶ originalCarrierEquivalence.{u, v}.functor ⋙ R ⋙ originalCarrierEquivalence.{u,
      v}.inverse)
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    component ((Functor.whiskerRight w originalCarrierEquivalence.{u, v}.functor ≫
      Functor.whiskerLeft (originalCarrierEquivalence.{u, v}.functor ⋙ R) originalCarrierEquivalence.{u,
        v}.counitIso.hom).app N)
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (w.app N).hom.natTrans.app n := by
  let f := originalCarrierEquivalence.{u, v}.functor.map (w.app N)
  let e := originalCarrierEquivalence.{u, v}.counitIso.hom.app (R.obj (originalCarrierEquivalence.{u, v}.functor.obj N))
  have hc := component_comp f e (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have hf : component f (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (w.app N).hom.natTrans.app n :=
    toOperatorMorphism_component (w.app N) (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have he : component e (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      𝟙 ((R.obj (originalCarrierEquivalence.{u, v}.functor.obj N)).toEnrichedFunctor.obj
        (PointedCGWH.symmetricOperatorObj.{u, v} n)) :=
    moduleOperatorEquivalence_counit_component
      (R.obj (originalCarrierEquivalence.{u, v}.functor.obj N)) (PointedCGWH.symmetricOperatorObj.{u, v} n)
  exact hc.trans ((congrArg₂ (fun p q => p ≫ q) hf he).trans
    (Category.comp_id ((w.app N).hom.natTrans.app n)))


set_option maxHeartbeats 500000 in
/-- The whole source image reads back a named original module word. All
functors and word data stay arbitrary, before any original free source is fixed. -/
theorem native_component_of_source_word
    (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    {F G : OriginalModule.{u, v} ⥤ OriginalModule.{u, v}}
    {R₀ : NativeCarrier.{u, v} ⥤ NativeCarrier.{u, v}}
    (e : F ≅ originalCarrierEquivalence.{u, v}.functor ⋙ R₀ ⋙ originalCarrierEquivalence.{u, v}.inverse)
    (e' : G ≅ originalCarrierEquivalence.{u, v}.functor ⋙ target.{u, v} r K ⋙ originalCarrierEquivalence.{u, v}.inverse)
    (u₀ : R₀ ≅ 𝟭 NativeCarrier.{u, v}) (p : F ⟶ G)
    (w : 𝟭 OriginalModule.{u, v} ⟶ targetModuleFunctor.{u, v} r K)
    (hw : w = SourceImageWord.moduleWord originalCarrierEquivalence.{u, v} e e' u₀ p)
    (c : 𝟭 NativeCarrier.{u, v} ⟶ target.{u, v} r K)
    (hImage : Functor.whiskerLeft originalCarrierEquivalence.{u, v}.functor c =
      SourceImageWord.carrierWord originalCarrierEquivalence.{u, v} e e' u₀ p)
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    component (c.app (originalCarrierEquivalence.{u, v}.functor.obj N))
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (w.app N).hom.natTrans.app n := by
  let imageWord : (𝟭 OriginalModule.{u, v} ⟶ targetModuleFunctor.{u, v} r K) →
      (originalCarrierEquivalence.{u, v}.functor ⟶ originalCarrierEquivalence.{u, v}.functor ⋙ target.{u, v} r K) :=
    fun z => Functor.whiskerRight z originalCarrierEquivalence.{u, v}.functor ≫
      Functor.whiskerLeft (originalCarrierEquivalence.{u, v}.functor ⋙ target.{u, v} r K) originalCarrierEquivalence.{u,
        v}.counitIso.hom
  have h := congrArg (fun f => component f (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (NatTrans.congr_app hImage N)
  have hWord := congrArg
    (fun z => component ((imageWord z).app N) (PointedCGWH.symmetricOperatorObj.{u, v} n)) hw
  have hTail := carrier_image_component (target.{u, v} r K) w N n
  exact h.trans (hWord.symm.trans hTail)

set_option maxHeartbeats 500000 in
/-- The original typed raw action and full source image give the same native
component uniformly, before any unit or sphere record is specialized. -/
theorem native_action_component_of_source_word
    (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    {F G : OriginalModule.{u, v} ⥤ OriginalModule.{u, v}}
    {R₀ : NativeCarrier.{u, v} ⥤ NativeCarrier.{u, v}}
    (e : F ≅ originalCarrierEquivalence.{u, v}.functor ⋙ R₀ ⋙ originalCarrierEquivalence.{u, v}.inverse)
    (e' : G ≅ originalCarrierEquivalence.{u, v}.functor ⋙ target.{u, v} r K ⋙ originalCarrierEquivalence.{u, v}.inverse)
    (u₀ : R₀ ≅ 𝟭 NativeCarrier.{u, v}) (p : F ⟶ G)
    (w : 𝟭 OriginalModule.{u, v} ⟶ targetModuleFunctor.{u, v} r K)
    (hw : w = SourceImageWord.moduleWord originalCarrierEquivalence.{u, v} e e' u₀ p)
    (c : 𝟭 NativeCarrier.{u, v} ⟶ target.{u, v} r K)
    (hImage : Functor.whiskerLeft originalCarrierEquivalence.{u, v}.functor c =
      SourceImageWord.carrierWord originalCarrierEquivalence.{u, v} e e' u₀ p)
    (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid)
    (a : N.X.functor.obj n ⟶ (ihom (C := PointedCGWH.{u, v}) K).obj
      (N.X.functor.obj (n ⊗ r)))
    (ha : (w.app N).hom.natTrans.app n = a) :
    component (c.app (originalCarrierEquivalence.{u, v}.functor.obj N))
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      a := by
  have h := native_component_of_source_word r K e e' u₀ p w hw c hImage N n
  exact h.trans ha


private theorem moduleComparison_zero_eq_original :
    moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}) =
      NativeSelectedUnitTransport.Native.originalModuleComparison.{u, v} := rfl

private theorem moduleComparison_zero_mate :
    NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} ≫
        (moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v})).hom =
      E.{u, v}.unitIso.hom ≫ Functor.whiskerLeft E.{u, v}.functor
        (Functor.whiskerRight zeroScalarIndexUnit.{u, v}.inv E.{u, v}.inverse) := by
  rw [moduleComparison_zero_eq_original]
  exact NativeSelectedUnitTransport.Native.originalModuleMate_eq_originalCarrierUnitMate.{u, v}

/-- The whole original zero-unit mate removes the module-comparison inverse
from the original module source word before any source or index is selected. -/
theorem original_firstSource_raw_word :
    originalFirstRawModuleWord.{u, v} =
      NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} ≫ modulePre.{u, v} ≫
        (moduleComparison NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}).hom := by
  exact moduleWord_of_whole_mate E.{u, v}
    (moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (moduleComparison NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    zeroScalarIndexUnit.{u, v} modulePre.{u, v}
    NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} moduleComparison_zero_mate.{u, v}

/-- The original precomposition map is the actual balanced action of the
same complete NativeSymmetricDelooping.firstIndex module source followed by the original zero contraction. -/
theorem original_firstSource_contraction_precompose :
    NativeSymmetricSelectedUnit.originalContractionCurry.{u, v} ≫ modulePre.{u, v} =
      SelectedUnitTensorCompatibility.contractionCurrySource A.{u, v}
        (freeModule.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
        (originalFirstModuleSource.{u, v} ≫ actualZeroFreeContraction.{u, v}) := by
  exact contraction_pre_nat A.{u, v}
    (freeModule.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    (freeModule.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    originalFirstModuleSource.{u, v} actualZeroFreeContraction.{u, v}

/-- The full original raw module word carries the actual contracted NativeSymmetricDelooping.firstIndex-source action.
-/
theorem original_firstSource_raw_balanced_word :
    originalFirstRawModuleWord.{u, v} =
      SelectedUnitTensorCompatibility.contractionCurrySource A.{u, v}
        (freeModule.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
        (originalFirstModuleSource.{u, v} ≫ actualZeroFreeContraction.{u, v}) ≫
      (moduleComparison NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}).hom := by
  have h := congrArg (fun f => f ≫ (moduleComparison NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u,
    v}).hom)
    original_firstSource_contraction_precompose.{u, v}
  exact original_firstSource_raw_word.{u, v}.trans
    ((Category.assoc _ _ _).symm.trans h)


private abbrev canonicalFree (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v}) :
    NativeSymmetricFreeFunction.OriginalModule.{u, v} :=
  (Mod.free A.{u, v}.X).obj
    (.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj K))

set_option maxHeartbeats 500000 in
/-- The complete native target action follows from the original whole source,
comparison, coefficient, and word data, uniformly in the actual native r and K. -/
private theorem native_action_of_whole_data
    (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    (q : canonicalFree.{u, v} r K ⟶ Mod.regular A.{u, v}.X)
    {F : NativeSymmetricFreeFunction.OriginalModule.{u, v} ⥤
      NativeSymmetricFreeFunction.OriginalModule.{u, v}}
    (hF : F = Mod.internalHom A.{u, v} (canonicalFree.{u, v} r K))
    (c : 𝟭 NativeSymmetricFreeFunction.OriginalModule.{u, v} ⟶ F)
    (hc : ∀ N, HEq (c.app N)
      (BalancedSourceAction.action A.{u, v} (canonicalFree.{u, v} r K) q N))
    (e : F ≅ targetModuleFunctor.{u, v} r K)
    (he : HEq e (FullFreeFunctionTargetNaturality.comparison
      (I := Operad.SmallFinBijGroupoid) (V := PointedCGWH.{u, v}) A.{u, v} r K
      (targetModuleFunctor.{u, v} r K) (targetSequenceNatIso.{u, v} r K)
      (native_target_pair_square.{u, v} r K)))
    (w : 𝟭 NativeSymmetricFreeFunction.OriginalModule.{u, v} ⟶ targetModuleFunctor.{u, v} r K)
    (hw : w = c ≫ e.hom) (g : K ⟶ PointedCGWH.sphereSequence.{u, v}.functor.obj r)
    (hCoefficient : Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫
      ((Mod.freeForgetAdjunction A.{u, v}.X).unit.app
        (.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj K))).natTrans.app r ≫
      q.hom.natTrans.app r = g)
    (N : NativeSymmetricFreeFunction.OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    (w.app N).hom.natTrans.app n =
      MonoidalClosed.curry (C := PointedCGWH.{u, v})
        ((g ▷ N.X.functor.obj n) ≫
          (DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (r, n) ≫
          N.mod.smul.natTrans.app (r ⊗ n)) ≫
        (ihom (C := PointedCGWH.{u, v}) K).map (N.X.functor.map (β_ r n).hom) := by
  have h := BalancedTarget.action_target_component_of_whole_data
    (I := Operad.SmallFinBijGroupoid) (V := PointedCGWH.{u, v}) A.{u, v} r K
    (targetModuleFunctor.{u, v} r K) (targetSequenceNatIso.{u, v} r K)
    (native_target_pair_square.{u, v} r K) q hF c hc e he N n
  let g₀ : K ⟶ PointedCGWH.sphereSequence.{u, v}.functor.obj r :=
    Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫
      ((Mod.freeForgetAdjunction A.{u, v}.X).unit.app
        (.mk ((evaluationLeftAdjoint PointedCGWH.{u, v} r).obj K))).natTrans.app r ≫
      q.hom.natTrans.app r
  let a : PointedCGWH.sphereSequence.{u, v}.functor.obj r ⊗ N.X.functor.obj n ⟶
      N.X.functor.obj (r ⊗ n) :=
    (DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (r, n) ≫
      N.mod.smul.natTrans.app (r ⊗ n)
  let b := N.X.functor.map (β_ r n).hom
  let p : (K ⟶ PointedCGWH.sphereSequence.{u, v}.functor.obj r) →
      (N.X.functor.obj n ⟶ (ihom (C := PointedCGWH.{u, v}) K).obj
        (N.X.functor.obj (n ⊗ r))) := fun t =>
    MonoidalClosed.curry (C := PointedCGWH.{u, v}) ((t ▷ N.X.functor.obj n) ≫ a) ≫
      (ihom (C := PointedCGWH.{u, v}) K).map b
  let z := ((targetSequenceNatIso.{u, v} r K).hom.app N).natTrans.app n
  have hWord := congrArg (fun t => (t.app N).hom.natTrans.app n) hw
  have hAction : ((c ≫ e.hom).app N).hom.natTrans.app n = p g₀ ≫ z := h
  have hcg : p g₀ = p g := congrArg p hCoefficient
  have hz : z = 𝟙 ((ihom (C := PointedCGWH.{u, v}) K).obj
      (N.X.functor.obj (n ⊗ r))) :=
    targetSequenceIso_inv_component.{u, v} r K N n
  have hpost := congrArg (fun t => t ≫ z) hcg
  have hid := (congrArg (fun t => p g ≫ t) hz).trans (Category.comp_id (p g))
  exact hWord.trans (hAction.trans (hpost.trans hid))


private theorem contraction_app_heq {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
    (B : CommMon C) (M M' : Mod C B.X) (q : M ⟶ Mod.regular B.X)
    (q' : M' ⟶ Mod.regular B.X) (hM : M = M') (hq : HEq q q')
    (N : Mod C B.X) :
    HEq ((SelectedUnitTensorCompatibility.contractionCurrySource B M q).app N)
      (BalancedSourceAction.action B M' q' N) := by
  cases hM
  cases hq
  rfl

attribute [local irreducible] DayFunctor.inst

set_option maxHeartbeats 500000 in
/-- The original NativeSymmetricDelooping.firstIndex source word has the full original native Day action
on every module and output index, with the actual coefficient inverse. -/
symmetricGenSharedDeclaration% original_firstSource_raw_action :
    ∀ (N : NativeSymmetricFreeFunction.OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid),
    (originalFirstRawModuleWord.{u, v}.app N).hom.natTrans.app n =
      MonoidalClosed.curry (C := PointedCGWH.{u, v})
        ((NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ▷ N.X.functor.obj n) ≫
          (DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (NativeSymmetricDelooping.firstIndex, n) ≫
          N.mod.smul.natTrans.app (NativeSymmetricDelooping.firstIndex ⊗ n)) ≫
        (ihom (C := PointedCGWH.{u, v}) PointedCGWH.sphereOne.{u, v}).map (N.X.functor.map (β_
          NativeSymmetricDelooping.firstIndex n).hom) := fun N n => by
  let M := freeModule.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}
  let P : PointedCGWH.SymmetricSequence.{u, v} :=
    .mk ((evaluationLeftAdjoint PointedCGWH.{u, v} NativeSymmetricDelooping.firstIndex).obj PointedCGWH.sphereOne.{u,
      v})
  let Mc := (Mod.free A.{u, v}.X).obj P
  let q : M ⟶ Mod.regular A.{u, v}.X :=
    originalFirstModuleSource.{u, v} ≫ actualZeroFreeContraction.{u, v}
  let qc := NativeAdjointData.canonicalMap.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v} q
  let c := SelectedUnitTensorCompatibility.contractionCurrySource A.{u, v} M q
  have hM : M = Mc :=
    FreeSourceObjects.actual_free_module_eq_canonical.{u, v} NativeSymmetricDelooping.firstIndex
      PointedCGWH.sphereOne.{u, v}
  have hq : HEq q qc := (NativeAdjointData.canonicalMap_heq_original.{u, v}
    NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v} q).symm
  have hc : ∀ T : NativeSymmetricFreeFunction.OriginalModule.{u, v}, HEq (c.app T)
      (BalancedSourceAction.action A.{u, v} Mc qc T) :=
    contraction_app_heq A.{u, v} M Mc q qc hM hq
  have he : HEq (moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
      (FullFreeFunctionTargetNaturality.comparison (I := Operad.SmallFinBijGroupoid) (V := PointedCGWH.{u, v}) A.{u, v}
        NativeSymmetricDelooping.firstIndex
        PointedCGWH.sphereOne.{u, v} (targetModuleFunctor.{u, v} NativeSymmetricDelooping.firstIndex
          PointedCGWH.sphereOne.{u, v})
        (targetSequenceNatIso.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
        (native_target_pair_square.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})) :=
    (NativeSelectedUnitTransport.SourceValueTools.rebaseComparison_heq
      (moduleComparisonNat.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
      (moduleComparison_source.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})).trans HEq.rfl
  have hCoefficient := (NativeAdjointData.canonical_generator_eq_original_day_adjunct.{u, v}
    NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v} q).trans
      FirstCoefficient.DayReadback.original_first_source_contracted_generator.{u, v}
  have hw : originalFirstRawModuleWord.{u, v} =
      c ≫ (moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v}).hom :=
    original_firstSource_raw_balanced_word.{u, v}
  exact native_action_of_whole_data.{u, v} NativeSymmetricDelooping.firstIndex
    PointedCGWH.sphereOne.{u, v} qc (congrArg (Mod.internalHom A.{u, v}) hM) c hc
    (moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    he originalFirstRawModuleWord.{u, v} hw NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv
    hCoefficient N n


set_option maxHeartbeats 1000000 in
/-- Every original module/index component of the full native source is the same actual action. -/
theorem original_firstSource_gen (N : NativeSymmetricFreeFunction.OriginalModule.{u, v}) (n :
  Operad.SmallFinBijGroupoid) :
    component (originalFirstComparison.{u, v}.app (originalCarrierEquivalence.{u, v}.functor.obj N))
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      MonoidalClosed.curry
        ((NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ▷ N.X.functor.obj n) ≫
          (DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (NativeSymmetricDelooping.firstIndex, n) ≫
          N.mod.smul.natTrans.app (NativeSymmetricDelooping.firstIndex ⊗ n)) ≫
        (ihom PointedCGWH.sphereOne.{u, v}).map (N.X.functor.map (β_ NativeSymmetricDelooping.firstIndex n).hom) := by
  exact native_action_component_of_source_word
    (r := NativeSymmetricDelooping.firstIndex) (K := PointedCGWH.sphereOne.{u, v})
    (e := moduleComparison.{u, v} (𝟙_ Operad.SmallFinBijGroupoid) (𝟙_ PointedCGWH.{u, v}))
    (e' := moduleComparison.{u, v} NativeSymmetricDelooping.firstIndex PointedCGWH.sphereOne.{u, v})
    (u₀ := zeroScalarIndexUnit.{u, v}) (p := modulePre.{u, v})
    (w := originalFirstRawModuleWord.{u, v}) (hw := rfl)
    (c := originalFirstComparison.{u, v})
    (hImage := original_firstSource_whole_normalized_image.{u, v})
    (N := N) (n := n) (a := _) (ha := original_firstSource_raw_action N n)

set_option maxHeartbeats 500000 in
/-- The original NativeSymmetricDelooping.firstIndex module action is its full native Omega transpose and coefficient
map. -/
theorem original_module_action_omega (N : NativeSymmetricFreeFunction.OriginalModule.{u, v}) (n :
  Operad.SmallFinBijGroupoid) :
    MonoidalClosed.curry (C := PointedCGWH.{u, v})
        ((NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ▷ N.X.functor.obj n) ≫
          (DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (NativeSymmetricDelooping.firstIndex, n) ≫
          N.mod.smul.natTrans.app (NativeSymmetricDelooping.firstIndex ⊗ n)) ≫
        (ihom (C := PointedCGWH.{u, v}) PointedCGWH.sphereOne.{u, v}).map (N.X.functor.map (β_
          NativeSymmetricDelooping.firstIndex n).hom) =
      NativeSymmetricDelooping.omegaMap (originalCarrierEquivalence.{u, v}.functor.obj N) n
        NativeSymmetricDelooping.firstIndex ≫
        (MonoidalClosed.pre NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv).app
          (N.X.functor.obj (n ⊗ NativeSymmetricDelooping.firstIndex)) := by
  let a : PointedCGWH.sphereSequence.{u, v}.functor.obj NativeSymmetricDelooping.firstIndex ⊗ N.X.functor.obj n ⟶
    N.X.functor.obj (NativeSymmetricDelooping.firstIndex ⊗ n) :=
    (DayFunctor.η PointedCGWH.sphereSequence.{u, v} N.X).app (NativeSymmetricDelooping.firstIndex, n) ≫
      N.mod.smul.natTrans.app (NativeSymmetricDelooping.firstIndex ⊗ n)
  let b := N.X.functor.map (β_ NativeSymmetricDelooping.firstIndex n).hom
  have h := NativeModuleOmegaFormula.adjoint.{u, v} N n NativeSymmetricDelooping.firstIndex
  change NativeSymmetricDelooping.omegaMap (originalCarrierEquivalence.{u, v}.functor.obj N) n
    NativeSymmetricDelooping.firstIndex =
    MonoidalClosed.curry (a ≫ b) at h
  erw [← MonoidalClosed.curry_natural_right]
  change MonoidalClosed.curry (C := PointedCGWH.{u, v})
    ((NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ▷ N.X.functor.obj n) ≫ (a ≫ b)) = _
  erw [← MonoidalClosed.curry_pre_app]
  exact congrArg (fun f => f ≫
    (MonoidalClosed.pre NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv).app
      (N.X.functor.obj (n ⊗ NativeSymmetricDelooping.firstIndex))) h.symm

/-- The entire original native scalar map is retained before every component is selected. -/
abbrev originalFirstStructure : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) ⟶
    PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex ⋙ cotensor PointedCGWH.sphereOne.{u,
      v} :=
  NativeSymmetricDelooping.comparisonNat.{u, v} NativeSymmetricDelooping.firstIndex ≫
    (Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex)
      NativeSymmetricDelooping.firstLoopIso.{u, v}).hom

/-- Every original structure component has the native Omega arrow followed by the same scalar map. -/
theorem originalFirstStructure_component (X : (EnrichedFunctorCat PointedCGWH.{u, v}
  PointedCGWH.SymmetricOperatorIndex.{u, v})) (n : Operad.SmallFinBijGroupoid) :
    component (originalFirstStructure.{u, v}.app X) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      NativeSymmetricDelooping.omegaMap X n NativeSymmetricDelooping.firstIndex ≫
        (MonoidalClosed.pre NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv).app
          (X.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ NativeSymmetricDelooping.firstIndex)))
            := by
  let a := (NativeSymmetricDelooping.comparisonNat.{u, v} NativeSymmetricDelooping.firstIndex).app X
  let b := (Functor.isoWhiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex)
    NativeSymmetricDelooping.firstLoopIso.{u, v}).hom.app X
  have hc := component_comp a b (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have ha := NativeSymmetricDelooping.comparison_component NativeSymmetricDelooping.firstIndex X n
  have hWhole : b = cotensorScalarMap
      NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv
      ((PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex).obj X) := rfl
  have hb := (congrArg (fun f => component f (PointedCGWH.symmetricOperatorObj.{u, v} n))
    hWhole).trans (cotensorScalarMap_component NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv
      ((PointedCGWH.SymmetricShift.functor.{u, v} NativeSymmetricDelooping.firstIndex).obj X)
      (PointedCGWH.symmetricOperatorObj.{u, v} n))
  exact hc.trans (congrArg₂ (fun f g => f ≫ g) ha hb)

private theorem equivalence_whiskerLeft_injective {C : Type*} [Category C]
    {D : Type*} [Category D] (e : C ≌ D) {F G : D ⥤ D} (f g : F ⟶ G)
    (h : Functor.whiskerLeft e.functor f = Functor.whiskerLeft e.functor g) : f = g := by
  apply NatTrans.ext
  funext X
  let i := e.counitIso.hom.app X
  apply (cancel_epi (F.map i)).mp
  have hX := NatTrans.congr_app h (e.inverse.obj X)
  exact (f.naturality i).trans
    ((congrArg (fun t => t ≫ G.map i) hX).trans (g.naturality i).symm)


set_option maxHeartbeats 500000 in
/-- The complete original input/output component laws identify two whole native
maps. Both typed action families remain arbitrary before any native source is fixed. -/
theorem native_whole_eq_of_action_data
    (r : Operad.SmallFinBijGroupoid) (K : PointedCGWH.{u, v})
    (c d : 𝟭 NativeCarrier.{u, v} ⟶ target.{u, v} r K)
    (p q : ∀ (N : OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid),
      N.X.functor.obj n ⟶ (ihom (C := PointedCGWH.{u, v}) K).obj
        (N.X.functor.obj (n ⊗ r)))
    (hc : ∀ N n, component (c.app (originalCarrierEquivalence.{u, v}.functor.obj N))
      (PointedCGWH.symmetricOperatorObj.{u, v} n) = p N n)
    (hpq : ∀ N n, p N n = q N n)
    (hd : ∀ N n, component (d.app (originalCarrierEquivalence.{u, v}.functor.obj N))
      (PointedCGWH.symmetricOperatorObj.{u, v} n) = q N n) : c = d := by
  apply equivalence_whiskerLeft_injective originalCarrierEquivalence.{u, v}
  apply NatTrans.ext
  funext N
  apply hom_ext
  intro x
  rcases x with ⟨n⟩
  exact (hc N n).trans ((hpq N n).trans (hd N n).symm)








end NativeOmegaRecovery.NativeSymmetricSourceGEN.WholeOriginalGEN
