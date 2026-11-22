/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.Comparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.CanonicalCarrierMigration

/-!
# The given original RIGHT κ algorithm on the actual genuine original D_R diagrams

Transport the actual original module κ/I and κ/J data through the genuine
source equivalence. The proved native source class identities retag only
the class proofs; Z/i/p and every Arrow map keep the original algorithm.
No equality with separately selected source-index SOA choices is asserted.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.MorphismProperty.FunctorialFactorizationData
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- All five literal raw D_R classes are the explicit canonical inverse images, at every caller bottom. -/
theorem sourceClassReadback :
    letI : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
      (A := PointedCGWH.SymmetricDRight.Index)
    weakEquivalences SourceCarrier.{u, v} = sourceWeak ∧
      cofibrations SourceCarrier.{u, v} = sourceCofibrations ∧
      fibrations SourceCarrier.{u, v} = sourceFibrations ∧
      trivialFibrations SourceCarrier.{u, v} = sourceTrivialFibrations ∧
      trivialCofibrations SourceCarrier.{u, v} = sourceTrivialCofibrations :=
  ⟨Native.weakEquivalences_eq.trans sourceWeak_eq_evaluation.symm,
   Native.cofibrations_eq.trans sourceCofibrations_eq_generators.symm,
   Native.fibrations_eq.trans sourceFibrations_eq_evaluation.symm,
   Native.trivialFibrations_eq.trans sourceTrivialFibrations_eq_evaluation.symm,
   Native.trivialCofibrations_eq.trans sourceTrivialCofibrations_eq_generators.symm⟩

/-- The direct D_R κ/I record keeps its own supplied-bottom algorithm and every original field. -/
def directCofibrantFactorizationData :
    FunctorialFactorizationData sourceCofibrations.{u, v} sourceTrivialFibrations := by
  letI : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
    (A := PointedCGWH.SymmetricDRight.Index)
  exact (Native.cofibrantFactorizationData.{u, v} (A := PointedCGWH.SymmetricDRight.Index)).ofLE
    (fun _ _ f h => (Iff.of_eq (congrArg
      (fun P : MorphismProperty SourceCarrier.{u, v} => P f) sourceClassReadback.2.1)).mp h)
    (fun _ _ f h => (Iff.of_eq (congrArg
      (fun P : MorphismProperty SourceCarrier.{u, v} => P f) sourceClassReadback.2.2.2.1)).mp h)

/-- The direct D_R κ/J record keeps its own supplied-bottom algorithm and every original field. -/
def directFibrantFactorizationData :
    FunctorialFactorizationData sourceTrivialCofibrations.{u, v} sourceFibrations := by
  letI : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
    (A := PointedCGWH.SymmetricDRight.Index)
  exact (Native.fibrantFactorizationData.{u, v} (A := PointedCGWH.SymmetricDRight.Index)).ofLE
    (fun _ _ f h => (Iff.of_eq (congrArg
      (fun P : MorphismProperty SourceCarrier.{u, v} => P f) sourceClassReadback.2.2.2.2)).mp h)
    (fun _ _ f h => (Iff.of_eq (congrArg
      (fun P : MorphismProperty SourceCarrier.{u, v} => P f) sourceClassReadback.2.2.1)).mp h)

omit B in
private theorem factorizationData_heq_of_fields {C : Type*} [Category C]
    {P Q P' Q' : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (d' : FunctorialFactorizationData P' Q')
    (hP : P = P') (hQ : Q = Q') (hZ : d.Z = d'.Z)
    (hi : HEq d.i d'.i) (hp : HEq d.p d'.p) : HEq d d' := by
  cases hP
  cases hQ
  cases d
  cases d'
  dsimp at hZ hi hp
  cases hZ
  cases eq_of_heq hi
  cases eq_of_heq hp
  rfl

/-- The whole direct D_R record, including class proofs and all original maps, is unchanged. -/
theorem directCofibrantFactorizationData_heq_existing :
    HEq directCofibrantFactorizationData.{u, v}
      (Native.cofibrantFactorizationData.{u, v} (A := PointedCGWH.SymmetricDRight.Index)) :=
  factorizationData_heq_of_fields directCofibrantFactorizationData
    (Native.cofibrantFactorizationData.{u, v} (A := PointedCGWH.SymmetricDRight.Index))
    sourceClassReadback.2.1.symm
    sourceClassReadback.2.2.2.1.symm rfl (HEq.rfl) (HEq.rfl)

/-- The whole direct D_R record, including class proofs and all original maps, is unchanged. -/
theorem directFibrantFactorizationData_heq_existing :
    HEq directFibrantFactorizationData.{u, v}
      (Native.fibrantFactorizationData.{u, v} (A := PointedCGWH.SymmetricDRight.Index)) :=
  factorizationData_heq_of_fields directFibrantFactorizationData
    (Native.fibrantFactorizationData.{u, v} (A := PointedCGWH.SymmetricDRight.Index))
    sourceClassReadback.2.2.2.2.symm
    sourceClassReadback.2.2.1.symm rfl (HEq.rfl) (HEq.rfl)

/-- All direct D_R Z/i/p fields are exactly the original κ small-object data. -/
theorem directCofibrantFactorizationData_fields :
    letI : (generators (A := PointedCGWH.SymmetricDRight.Index)
      PointedCGWH.realizedBoundaryInclusions.{u, v}).IsCardinalForSmallObjectArgument
        realizedGeneratorCardinal.{v} := Native.generatorsI_isCardinalForSmallObjectArgument
    let original := SmallObject.functorialFactorizationData
      (generators (A := PointedCGWH.SymmetricDRight.Index)
        PointedCGWH.realizedBoundaryInclusions.{u, v}) realizedGeneratorCardinal.{v}
    directCofibrantFactorizationData.Z = original.Z ∧
      directCofibrantFactorizationData.i = original.i ∧
      directCofibrantFactorizationData.p = original.p :=
  Native.cofibrantFactorizationData_fields (A := PointedCGWH.SymmetricDRight.Index)

/-- All direct D_R Z/i/p fields are exactly the original κ small-object data. -/
theorem directFibrantFactorizationData_fields :
    letI : (generators (A := PointedCGWH.SymmetricDRight.Index)
      PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
        realizedGeneratorCardinal.{v} := Native.generatorsJ_isCardinalForSmallObjectArgument
    let original := SmallObject.functorialFactorizationData
      (generators (A := PointedCGWH.SymmetricDRight.Index)
        PointedCGWH.realizedHornInclusions.{u, v}) realizedGeneratorCardinal.{v}
    directFibrantFactorizationData.Z = original.Z ∧
      directFibrantFactorizationData.i = original.i ∧
      directFibrantFactorizationData.p = original.p :=
  Native.fibrantFactorizationData_fields (A := PointedCGWH.SymmetricDRight.Index)

include B in
/-- The same actual original module κ/I data with exact source inverse/unit/counit. -/
def originalCofibrantFactorizationData :
    FunctorialFactorizationData sourceCofibrations.{u, v} sourceTrivialFibrations :=
  CanonicalCarrierMigration.sourceCofibrantFactorizationData.ofEquivalence presentation.symm

omit B in
/-- The whole source middle retains exactly the original module middle algorithm. -/
theorem originalCofibrantFactorizationData_Z [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :
  (originalCofibrantFactorizationData.{u, v}).Z =
    presentation.inverse.mapArrow ⋙ (CanonicalCarrierMigration.sourceCofibrantFactorizationData.{u, v}).Z ⋙
      presentation.functor := rfl

omit B in
/-- The entire source first map retains the actual original module map and source counit inverse. -/
theorem originalCofibrantFactorizationData_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalCofibrantFactorizationData.{u, v}).i.app f = presentation.counitIso.inv.app f.left ≫
      presentation.functor.map ((CanonicalCarrierMigration.sourceCofibrantFactorizationData.{u, v}).i.app
        (presentation.inverse.mapArrow.obj f)) := rfl

omit B in
/-- The entire source second map retains the actual original module map and source counit. -/
theorem originalCofibrantFactorizationData_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalCofibrantFactorizationData.{u, v}).p.app f =
      presentation.functor.map ((CanonicalCarrierMigration.sourceCofibrantFactorizationData.{u, v}).p.app
        (presentation.inverse.mapArrow.obj f)) ≫
        presentation.counitIso.hom.app f.right := rfl

omit B in
/-- Every full original Arrow square retains its entire original module middle map. -/
theorem originalCofibrantFactorizationData_Z_map [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {f g :
  CategoryTheory.Arrow SourceCarrier.{u, v}}
  (φ : f ⟶ g) :
    (originalCofibrantFactorizationData.{u, v}).Z.map φ =
      presentation.functor.map ((CanonicalCarrierMigration.sourceCofibrantFactorizationData.{u, v}).Z.map
        (presentation.inverse.mapArrow.map φ)) := rfl

omit B in
/-- The full source arrow is factored by the transported original maps. -/
theorem originalCofibrantFactorizationData_fac [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalCofibrantFactorizationData.{u, v}).i.app f ≫ (originalCofibrantFactorizationData.{u,
      v}).p.app f = f.hom :=
  (originalCofibrantFactorizationData.{u, v}).fac_app

/-- Both whole source maps lie in the actual constructed native source classes. -/
theorem originalCofibrantFactorizationData_classes (f : CategoryTheory.Arrow SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    cofibrations SourceCarrier.{u, v} ((originalCofibrantFactorizationData.{u, v}).i.app f) ∧
      trivialFibrations SourceCarrier.{u, v} ((originalCofibrantFactorizationData.{u, v}).p.app f)
        := by
  let _ : ModelCategory SourceCarrier.{u, v} :=
    EnrichedProjective.Native.modelCategory (A := PointedCGWH.SymmetricDRight.Index)
  have h := sourceClassReadback.{u, v} (B := B)
  exact ⟨(Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P (originalCofibrantFactorizationData.i.app f)) h.2.1)).mpr
        (originalCofibrantFactorizationData.hi f),
    (Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P (originalCofibrantFactorizationData.p.app f)) h.2.2.2.1)).mpr
        (originalCofibrantFactorizationData.hp f)⟩

/-- The actual original module unit compares the entire transported middle functor. -/
def originalCofibrantFactorizationDataComparisonIso : (originalCofibrantFactorizationData.{u,
  v}).Z ⋙ presentation.inverse ≅
    presentation.inverse.mapArrow ⋙
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalenceZComparisonIso
    presentation.symm

/-- Recover the complete original first map through the actual source inverse. -/
theorem originalCofibrantFactorizationData_mapped_i (f : CategoryTheory.Arrow SourceCarrier.{u,
  v}) :
    presentation.inverse.map ((originalCofibrantFactorizationData.{u, v}).i.app f) ≫
      (originalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app f =
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app
          (presentation.inverse.mapArrow.obj f) := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalence_mapped_i
    presentation.symm f

/-- Recover the complete original second map through the actual source inverse. -/
theorem originalCofibrantFactorizationData_mapped_p (f : CategoryTheory.Arrow SourceCarrier.{u,
  v}) :
    (originalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app
        (presentation.inverse.mapArrow.obj f) =
        presentation.inverse.map ((originalCofibrantFactorizationData.{u, v}).p.app f) := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalence_mapped_p
    presentation.symm f

/-- Every complete source commutative square preserves the original middle comparison. -/
theorem originalCofibrantFactorizationData_naturality
    {f g : CategoryTheory.Arrow SourceCarrier.{u, v}} (φ : f ⟶ g) :
    presentation.inverse.map ((originalCofibrantFactorizationData.{u, v}).Z.map φ) ≫
      (originalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app g =
        (originalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
          ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map
            (presentation.inverse.mapArrow.map φ) :=
  (originalCofibrantFactorizationDataComparisonIso.{u, v}).hom.naturality φ

include B in
/-- The same actual original module κ/J data with exact source inverse/unit/counit. -/
def originalFibrantFactorizationData :
    FunctorialFactorizationData sourceTrivialCofibrations.{u, v} sourceFibrations :=
  CanonicalCarrierMigration.sourceFibrantFactorizationData.ofEquivalence presentation.symm

omit B in
/-- The whole source middle retains exactly the original module middle algorithm. -/
theorem originalFibrantFactorizationData_Z [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :
  (originalFibrantFactorizationData.{u, v}).Z =
    presentation.inverse.mapArrow ⋙ (CanonicalCarrierMigration.sourceFibrantFactorizationData.{u, v}).Z ⋙
      presentation.functor := rfl

omit B in
/-- The entire source first map retains the actual original module map and source counit inverse. -/
theorem originalFibrantFactorizationData_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalFibrantFactorizationData.{u, v}).i.app f = presentation.counitIso.inv.app f.left ≫
      presentation.functor.map ((CanonicalCarrierMigration.sourceFibrantFactorizationData.{u, v}).i.app
        (presentation.inverse.mapArrow.obj f)) := rfl

omit B in
/-- The entire source second map retains the actual original module map and source counit. -/
theorem originalFibrantFactorizationData_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalFibrantFactorizationData.{u, v}).p.app f =
      presentation.functor.map ((CanonicalCarrierMigration.sourceFibrantFactorizationData.{u, v}).p.app
        (presentation.inverse.mapArrow.obj f)) ≫
        presentation.counitIso.hom.app f.right := rfl

omit B in
/-- Every full original Arrow square retains its entire original module middle map. -/
theorem originalFibrantFactorizationData_Z_map [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {f g :
  CategoryTheory.Arrow SourceCarrier.{u, v}}
  (φ : f ⟶ g) :
    (originalFibrantFactorizationData.{u, v}).Z.map φ =
      presentation.functor.map ((CanonicalCarrierMigration.sourceFibrantFactorizationData.{u, v}).Z.map
        (presentation.inverse.mapArrow.map φ)) := rfl

omit B in
/-- The full source arrow is factored by the transported original maps. -/
theorem originalFibrantFactorizationData_fac [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalFibrantFactorizationData.{u, v}).i.app f ≫ (originalFibrantFactorizationData.{u,
      v}).p.app f = f.hom :=
  (originalFibrantFactorizationData.{u, v}).fac_app

/-- Both whole source maps lie in the actual constructed native source classes. -/
theorem originalFibrantFactorizationData_classes (f : CategoryTheory.Arrow SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    trivialCofibrations SourceCarrier.{u, v} ((originalFibrantFactorizationData.{u, v}).i.app f) ∧
      fibrations SourceCarrier.{u, v} ((originalFibrantFactorizationData.{u, v}).p.app f) := by
  let _ : ModelCategory SourceCarrier.{u, v} :=
    EnrichedProjective.Native.modelCategory (A := PointedCGWH.SymmetricDRight.Index)
  have h := sourceClassReadback.{u, v} (B := B)
  exact ⟨(Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P (originalFibrantFactorizationData.i.app f)) h.2.2.2.2)).mpr
        (originalFibrantFactorizationData.hi f),
    (Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P (originalFibrantFactorizationData.p.app f)) h.2.2.1)).mpr
        (originalFibrantFactorizationData.hp f)⟩

/-- The actual original module unit compares the entire transported middle functor. -/
def originalFibrantFactorizationDataComparisonIso : (originalFibrantFactorizationData.{u, v}).Z ⋙
  presentation.inverse ≅
    presentation.inverse.mapArrow ⋙ ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalenceZComparisonIso
    presentation.symm

/-- Recover the complete original first map through the actual source inverse. -/
theorem originalFibrantFactorizationData_mapped_i (f : CategoryTheory.Arrow SourceCarrier.{u, v}) :
    presentation.inverse.map ((originalFibrantFactorizationData.{u, v}).i.app f) ≫
      (originalFibrantFactorizationDataComparisonIso.{u, v}).hom.app f =
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i.app
          (presentation.inverse.mapArrow.obj f) := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalence_mapped_i
    presentation.symm f

/-- Recover the complete original second map through the actual source inverse. -/
theorem originalFibrantFactorizationData_mapped_p (f : CategoryTheory.Arrow SourceCarrier.{u, v}) :
    (originalFibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p.app
        (presentation.inverse.mapArrow.obj f) =
        presentation.inverse.map ((originalFibrantFactorizationData.{u, v}).p.app f) := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalence_mapped_p
    presentation.symm f

/-- Every complete source commutative square preserves the original middle comparison. -/
theorem originalFibrantFactorizationData_naturality
    {f g : CategoryTheory.Arrow SourceCarrier.{u, v}} (φ : f ⟶ g) :
    presentation.inverse.map ((originalFibrantFactorizationData.{u, v}).Z.map φ) ≫
      (originalFibrantFactorizationDataComparisonIso.{u, v}).hom.app g =
        (originalFibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
          ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map
            (presentation.inverse.mapArrow.map φ) :=
  (originalFibrantFactorizationDataComparisonIso.{u, v}).hom.naturality φ

/-- The whole model-free-derived source record retains the actual original RIGHT algorithm at every bottom. -/
theorem originalCofibrantFactorizationData_heq_existing :
    HEq (originalCofibrantFactorizationData.{u, v})
      (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
       let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
         PointedCGWH.SymmetricDRight.Index));
       (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
         PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalence
         presentation.symm).ofLE
         (fun _ _ f h =>
           (Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} => P f)
             original_cofibrations_inverseImage)).mp h)
         (fun _ _ f h =>
           (Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} => P f)
             original_trivialFibrations_inverseImage)).mp h)) := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact factorizationData_heq_of_fields originalCofibrantFactorizationData _
    sourceClassReadback.2.1.symm sourceClassReadback.2.2.2.1.symm
    rfl (HEq.rfl) (HEq.rfl)

/-- The whole model-free-derived source record retains the actual original RIGHT algorithm at every bottom. -/
theorem originalFibrantFactorizationData_heq_existing :
    HEq (originalFibrantFactorizationData.{u, v})
      (let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v});
       let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
         PointedCGWH.SymmetricDRight.Index));
       (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
         PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).ofEquivalence
         presentation.symm).ofLE
         (fun _ _ f h =>
           (Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} => P f)
             original_trivialCofibrations_inverseImage)).mp h)
         (fun _ _ f h =>
           (Iff.of_eq (congrArg (fun P : MorphismProperty SourceCarrier.{u, v} => P f)
             original_fibrations_inverseImage)).mp h)) := by
  have hB : ‹OrderBot realizedGeneratorCardinal.{v}.ord.ToType› =
      EnrichedProjective.Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact factorizationData_heq_of_fields originalFibrantFactorizationData _
    sourceClassReadback.2.2.2.2.symm sourceClassReadback.2.2.1.symm
    rfl (HEq.rfl) (HEq.rfl)


/-- Both complete factor maps land in the fixed canonical Spectrum classes. -/
theorem directCofibrantFactorizationData_canonical_classes (f : Arrow SourceCarrier.{u, v}) :
    cofibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
      (directCofibrantFactorizationData.i.app f)) ∧
      trivialFibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
        (directCofibrantFactorizationData.p.app f)) :=
  ⟨directCofibrantFactorizationData.hi f, directCofibrantFactorizationData.hp f⟩

/-- Every whole direct D_R Arrow map is the same supplied-bottom κ map. -/
theorem directCofibrantFactorizationData_Z_map {f g : Arrow SourceCarrier.{u, v}} (φ : f ⟶ g) :
    directCofibrantFactorizationData.Z.map φ =
      (EnrichedProjective.Native.cofibrantFactorizationData.{u, v}
        (B := B) (A := PointedCGWH.SymmetricDRight.Index)).Z.map φ := rfl

/-- The direct D_R maps factor the entire original source arrow. -/
theorem directCofibrantFactorizationData_fac (f : Arrow SourceCarrier.{u, v}) :
    directCofibrantFactorizationData.i.app f ≫ directCofibrantFactorizationData.p.app f = f.hom :=
  directCofibrantFactorizationData.fac_app

/-- Both complete factor maps land in the fixed canonical Spectrum classes. -/
theorem directFibrantFactorizationData_canonical_classes (f : Arrow SourceCarrier.{u, v}) :
    trivialCofibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
      (directFibrantFactorizationData.i.app f)) ∧
      fibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
        (directFibrantFactorizationData.p.app f)) :=
  ⟨directFibrantFactorizationData.hi f, directFibrantFactorizationData.hp f⟩

/-- Every whole direct D_R Arrow map is the same supplied-bottom κ map. -/
theorem directFibrantFactorizationData_Z_map {f g : Arrow SourceCarrier.{u, v}} (φ : f ⟶ g) :
    directFibrantFactorizationData.Z.map φ =
      (EnrichedProjective.Native.fibrantFactorizationData.{u, v}
        (B := B) (A := PointedCGWH.SymmetricDRight.Index)).Z.map φ := rfl

/-- The direct D_R maps factor the entire original source arrow. -/
theorem directFibrantFactorizationData_fac (f : Arrow SourceCarrier.{u, v}) :
    directFibrantFactorizationData.i.app f ≫ directFibrantFactorizationData.p.app f = f.hom :=
  directFibrantFactorizationData.fac_app

omit B in
/-- Both complete factor maps land in the fixed canonical Spectrum classes. -/
theorem originalCofibrantFactorizationData_canonical_classes [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f
  : Arrow SourceCarrier.{u, v}) :
    cofibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
      (originalCofibrantFactorizationData.i.app f)) ∧
      trivialFibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
        (originalCofibrantFactorizationData.p.app f)) :=
  ⟨originalCofibrantFactorizationData.hi f, originalCofibrantFactorizationData.hp f⟩

omit B in
/-- Both complete factor maps land in the fixed canonical Spectrum classes. -/
theorem originalFibrantFactorizationData_canonical_classes [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  Arrow SourceCarrier.{u, v}) :
    trivialCofibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
      (originalFibrantFactorizationData.i.app f)) ∧
      fibrations Spectrum.{u, v} (canonicalSourcePresentation.functor.map
        (originalFibrantFactorizationData.p.app f)) :=
  ⟨originalFibrantFactorizationData.hi f, originalFibrantFactorizationData.hp f⟩

end PointedCGWH.Spectra.Symmetric.DRightPresentation
