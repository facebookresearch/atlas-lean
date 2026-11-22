/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.Basic

/-!
# Whole original RIGHT classes on the actual genuine original D_R source

Both models are constructed from actual native factories and genuinely
proved equivalences. These proofs compare all five literal original classes
and recover them on source diagrams through the actual inverse/counit.
They do not compare arbitrary choices of factorization algorithms.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole weakEquivalences class is the same on the actual original RIGHT carrier. -/
theorem original_weakEquivalences_eq :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      weakEquivalences Carrier.{u, v}) =
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.Spectra.Symmetric.DRightPresentation.presentation);
      weakEquivalences Carrier.{u, v}) := by
  funext M N f
  exact propext ((RightPresentationModel.weakEquivalences_iff f).trans (weakEquivalences_iff
    f).symm)

/-- The whole fibrations class is the same on the actual original RIGHT carrier. -/
theorem original_fibrations_eq :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      fibrations Carrier.{u, v}) =
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.Spectra.Symmetric.DRightPresentation.presentation);
      fibrations Carrier.{u, v}) := by
  funext M N f
  exact propext ((RightPresentationModel.fibrations_iff f).trans (fibrations_iff f).symm)

/-- The whole trivialFibrations class is the same on the actual original RIGHT carrier. -/
theorem original_trivialFibrations_eq :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      trivialFibrations Carrier.{u, v}) =
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.Spectra.Symmetric.DRightPresentation.presentation);
      trivialFibrations Carrier.{u, v}) := by
  funext M N f
  exact propext ((RightPresentationModel.trivialFibrations_iff f).trans (trivialFibrations_iff
    f).symm)

/-- The entire original standard free family gives the same cofibrations class in both models. -/
theorem original_cofibrations_eq :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      cofibrations Carrier.{u, v}) =
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.Spectra.Symmetric.DRightPresentation.presentation);
      cofibrations Carrier.{u, v}) :=
  RightPresentationModel.standard_cofibrations_eq.trans cofibrations_eq.symm

/-- The entire original standard free family gives the same trivialCofibrations class in both
  models. -/
theorem original_trivialCofibrations_eq :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      trivialCofibrations Carrier.{u, v}) =
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.Spectra.Symmetric.DRightPresentation.presentation);
      trivialCofibrations Carrier.{u, v}) :=
  RightPresentationModel.standard_trivialCofibrations_eq.trans trivialCofibrations_eq.symm

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
private theorem source_property_roundtrip (P : MorphismProperty SourceCarrier.{u, v})
    [P.RespectsIso] : (P.inverseImage presentation.functor).inverseImage presentation.inverse = P
      := by
  funext X Y f
  apply propext
  exact P.arrow_mk_iso_iff
    (CategoryTheory.Arrow.isoOfNatIso presentation.counitIso (CategoryTheory.Arrow.mk f))

/-- The actual source inverse recovers the entire original weakEquivalences class. -/
theorem original_weakEquivalences_inverseImage :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      weakEquivalences Carrier.{u, v}).inverseImage presentation.inverse =
    (let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index));
      weakEquivalences SourceCarrier.{u, v}) := by
  rw [original_weakEquivalences_eq]
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  change ((weakEquivalences SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
    presentation.inverse = weakEquivalences SourceCarrier.{u, v}
  exact source_property_roundtrip _

/-- The actual source inverse recovers the entire original cofibrations class. -/
theorem original_cofibrations_inverseImage :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      cofibrations Carrier.{u, v}).inverseImage presentation.inverse =
    (let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index));
      cofibrations SourceCarrier.{u, v}) := by
  rw [original_cofibrations_eq]
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  change ((cofibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
    presentation.inverse = cofibrations SourceCarrier.{u, v}
  exact source_property_roundtrip _

/-- The actual source inverse recovers the entire original fibrations class. -/
theorem original_fibrations_inverseImage :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      fibrations Carrier.{u, v}).inverseImage presentation.inverse =
    (let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index));
      fibrations SourceCarrier.{u, v}) := by
  rw [original_fibrations_eq]
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  change ((fibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
    presentation.inverse = fibrations SourceCarrier.{u, v}
  exact source_property_roundtrip _

/-- The actual source inverse recovers the entire original trivialFibrations class. -/
theorem original_trivialFibrations_inverseImage :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      trivialFibrations Carrier.{u, v}).inverseImage presentation.inverse =
    (let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index));
      trivialFibrations SourceCarrier.{u, v}) := by
  rw [original_trivialFibrations_eq]
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  change ((trivialFibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
    presentation.inverse = trivialFibrations SourceCarrier.{u, v}
  exact source_property_roundtrip _

/-- The actual source inverse recovers the entire original trivialCofibrations class. -/
theorem original_trivialCofibrations_inverseImage :
    (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
      trivialCofibrations Carrier.{u, v}).inverseImage presentation.inverse =
    (let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index));
      trivialCofibrations SourceCarrier.{u, v}) := by
  rw [original_trivialCofibrations_eq]
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  change ((trivialCofibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
    presentation.inverse = trivialCofibrations SourceCarrier.{u, v}
  exact source_property_roundtrip _

/-- The actual original-module/source adjunction is Quillen for both constructed models. -/
theorem originalSource_isQuillenAdjunction :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    presentation.toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  exact {
    preservesCofibrations := fun _ _ f h =>
      (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f)
        original_cofibrations_eq)).mp h
    preservesTrivialCofibrations := fun _ _ f h =>
      (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f)
        original_trivialCofibrations_eq)).mp h }

/-- The inverse source/module adjunction preserves both original right classes. -/
theorem inverseOriginalSource_isQuillenAdjunction :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    presentation.symm.toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · exact fun _ _ f h =>
      (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f)
        original_fibrations_eq)).mp h
  · exact fun _ _ f h =>
      (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f)
        original_trivialFibrations_eq)).mp h


attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel

/-- Conjugate the complete given source adjunction through both actual canonical conversions. -/
def canonicalSourceEquivalence : Spectrum.{u, v} ≌ Spectrum.{u, v} :=
  (canonicalPresentation.symm.trans presentation).trans canonicalSourcePresentation

/-- The original source unit and the original RIGHT counit compare the full actual native functor. -/
def canonicalSourceFunctorIso : canonicalSourceEquivalence.{u, v}.functor ≅ 𝟭 Spectrum.{u, v} :=
  Functor.associator canonicalPresentation.inverse presentation.functor
      (presentation.inverse ⋙ canonicalPresentation.functor) ≪≫
    Functor.isoWhiskerLeft canonicalPresentation.inverse
      (Functor.associator presentation.functor presentation.inverse canonicalPresentation.functor).symm ≪≫
    Functor.isoWhiskerLeft canonicalPresentation.inverse
      (Functor.isoWhiskerRight presentation.unitIso.symm canonicalPresentation.functor) ≪≫
    Functor.isoWhiskerLeft canonicalPresentation.inverse (Functor.leftUnitor canonicalPresentation.functor) ≪≫
    canonicalPresentation.counitIso

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- The full actual conjugated source adjunction is Quillen on the canonical spectrum model. -/
theorem canonicalSource_isQuillenAdjunction : canonicalSourceEquivalence.{u, v}.toAdjunction.IsQuillenAdjunction := by
  exact {
    preservesCofibrations := fun _ _ f h =>
      ((cofibrations Spectrum.{u, v}).arrow_mk_iso_iff
        (Arrow.isoOfNatIso canonicalSourceFunctorIso (Arrow.mk f))).mpr h
    preservesTrivialCofibrations := fun _ _ f h =>
      ((trivialCofibrations Spectrum.{u, v}).arrow_mk_iso_iff
        (Arrow.isoOfNatIso canonicalSourceFunctorIso (Arrow.mk f))).mpr h }

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- The supplied inverse adjunction also uses its actual full native functor and canonical model. -/
theorem inverseCanonicalSource_isQuillenAdjunction :
    canonicalSourceEquivalence.{u, v}.symm.toAdjunction.IsQuillenAdjunction := by
  have c : canonicalSourceEquivalence.{u, v}.inverse ≅ 𝟭 Spectrum.{u, v} := canonicalSourceFunctorIso
  exact {
    preservesCofibrations := fun _ _ f h =>
      ((cofibrations Spectrum.{u, v}).arrow_mk_iso_iff
        (Arrow.isoOfNatIso c (Arrow.mk f))).mpr h
    preservesTrivialCofibrations := fun _ _ f h =>
      ((trivialCofibrations Spectrum.{u, v}).arrow_mk_iso_iff
        (Arrow.isoOfNatIso c (Arrow.mk f))).mpr h }


end PointedCGWH.Spectra.Symmetric.DRightPresentation
