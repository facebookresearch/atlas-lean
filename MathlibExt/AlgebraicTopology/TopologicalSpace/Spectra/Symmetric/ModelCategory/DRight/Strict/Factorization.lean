/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveBasedNative.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.StrictSource

/-!
# Given original RIGHT cardinal data on literal strict source diagrams

The actual original RIGHT algorithm first passes through the proved full
D_R source equivalence, then through the actual chosen-base equivalence.
All complete middle maps, factorization maps and original comparisons are
retained; every strict middle preserves the chosen base literally.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.EnrichedZeroCompletion
open CategoryTheory.MorphismProperty.FunctorialFactorizationData
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

/-- The actual literal chosen-zero source carrier of the original RIGHT transport. -/
abbrev StrictSourceCarrier := EnrichedProjective.BasedNativePresentation.StrictCarrier.{u, v}
  (A := PointedCGWH.SymmetricDRight.Index)

/-- The actual original carrier equivalence followed by chosen-base source transport. -/
abbrev strictPresentation : Carrier.{u, v} ≌ StrictSourceCarrier.{u, v} :=
  EnrichedProjective.NativePresentation.strictSourceEquivalence presentation

/-- The actual strict restriction and original source equivalences lead to canonical Spectrum. -/
def canonicalStrictSourcePresentation : StrictSourceCarrier.{u, v} ≌ Spectrum.{u, v} :=
  (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)).trans canonicalSourcePresentation

/-- The complete strict class is the canonical source class under actual restriction. -/
def strictSourceWeak : MorphismProperty StrictSourceCarrier.{u, v} :=
  sourceWeak.inverseImage strictRestriction

/-- The complete strict class is the canonical source class under actual restriction. -/
def strictSourceCofibrations : MorphismProperty StrictSourceCarrier.{u, v} :=
  sourceCofibrations.inverseImage strictRestriction

/-- The complete strict class is the canonical source class under actual restriction. -/
def strictSourceFibrations : MorphismProperty StrictSourceCarrier.{u, v} :=
  sourceFibrations.inverseImage strictRestriction

/-- The complete strict class is the canonical source class under actual restriction. -/
def strictSourceTrivialFibrations : MorphismProperty StrictSourceCarrier.{u, v} :=
  sourceTrivialFibrations.inverseImage strictRestriction

/-- The complete strict class is the canonical source class under actual restriction. -/
def strictSourceTrivialCofibrations : MorphismProperty StrictSourceCarrier.{u, v} :=
  sourceTrivialCofibrations.inverseImage strictRestriction

section ActualStrictData
variable {W₁ W₂ : MorphismProperty SourceCarrier.{u, v}}
  [W₁.RespectsIso] [W₂.RespectsIso]

private theorem actual_strict_i_app (data : FunctorialFactorizationData W₁ W₂)
    (f : Arrow StrictSourceCarrier.{u, v}) :
    (data.ofEquivalence (EnrichedProjective.BasedNativePresentation.strictEquivalence
      (A := PointedCGWH.SymmetricDRight.Index))).i.app f =
        (EnrichedProjective.BasedNativePresentation.strictEquivalence
          (A := PointedCGWH.SymmetricDRight.Index)).unitIso.hom.app f.left ≫
            strictExtension.map (data.i.app (strictRestriction.mapArrow.obj f)) :=
  data.ofEquivalence_i_app (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)) f

private theorem actual_strict_p_app (data : FunctorialFactorizationData W₁ W₂)
    (f : Arrow StrictSourceCarrier.{u, v}) :
    (data.ofEquivalence (EnrichedProjective.BasedNativePresentation.strictEquivalence
      (A := PointedCGWH.SymmetricDRight.Index))).p.app f =
        strictExtension.map (data.p.app (strictRestriction.mapArrow.obj f)) ≫
          (EnrichedProjective.BasedNativePresentation.strictEquivalence
            (A := PointedCGWH.SymmetricDRight.Index)).unitIso.inv.app f.right :=
  data.ofEquivalence_p_app (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)) f

private theorem actual_strict_comparison_i (data : FunctorialFactorizationData W₁ W₂)
    (i : (data.ofEquivalence (EnrichedProjective.BasedNativePresentation.strictEquivalence
      (A := PointedCGWH.SymmetricDRight.Index))).Z ⋙ strictRestriction ≅
        strictRestriction.mapArrow ⋙ data.Z)
    (hi : i = data.ofEquivalenceZComparisonIso
      (EnrichedProjective.BasedNativePresentation.strictEquivalence
        (A := PointedCGWH.SymmetricDRight.Index))) (f : Arrow StrictSourceCarrier.{u, v}) :
    strictRestriction.map ((data.ofEquivalence
      (EnrichedProjective.BasedNativePresentation.strictEquivalence
        (A := PointedCGWH.SymmetricDRight.Index))).i.app f) ≫ i.hom.app f =
          data.i.app (strictRestriction.mapArrow.obj f) := by
  rw [hi]
  exact data.ofEquivalence_mapped_i (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)) f

private theorem actual_strict_comparison_p (data : FunctorialFactorizationData W₁ W₂)
    (i : (data.ofEquivalence (EnrichedProjective.BasedNativePresentation.strictEquivalence
      (A := PointedCGWH.SymmetricDRight.Index))).Z ⋙ strictRestriction ≅
        strictRestriction.mapArrow ⋙ data.Z)
    (hi : i = data.ofEquivalenceZComparisonIso
      (EnrichedProjective.BasedNativePresentation.strictEquivalence
        (A := PointedCGWH.SymmetricDRight.Index))) (f : Arrow StrictSourceCarrier.{u, v}) :
    i.hom.app f ≫ data.p.app (strictRestriction.mapArrow.obj f) =
      strictRestriction.map ((data.ofEquivalence
        (EnrichedProjective.BasedNativePresentation.strictEquivalence
          (A := PointedCGWH.SymmetricDRight.Index))).p.app f) := by
  rw [hi]
  exact data.ofEquivalence_mapped_p (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)) f
end ActualStrictData

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every literal raw strict class is the canonical inverse image at the original caller bottom. -/
theorem strictSourceClassReadback :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    weakEquivalences StrictSourceCarrier.{u, v} = strictSourceWeak ∧
      cofibrations StrictSourceCarrier.{u, v} = strictSourceCofibrations ∧
      fibrations StrictSourceCarrier.{u, v} = strictSourceFibrations ∧
      trivialFibrations StrictSourceCarrier.{u, v} = strictSourceTrivialFibrations ∧
      trivialCofibrations StrictSourceCarrier.{u, v} = strictSourceTrivialCofibrations := by
  let _ : ModelCategory SourceCarrier.{u, v} :=
    EnrichedProjective.Native.modelCategory (A := PointedCGWH.SymmetricDRight.Index)
  have h := sourceClassReadback.{u, v} (B := B)
  exact ⟨congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P.inverseImage strictRestriction) h.1,
    congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P.inverseImage strictRestriction) h.2.1,
    congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P.inverseImage strictRestriction) h.2.2.1,
    congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P.inverseImage strictRestriction) h.2.2.2.1,
    congrArg (fun P : MorphismProperty SourceCarrier.{u, v} =>
      P.inverseImage strictRestriction) h.2.2.2.2⟩

/-- Transport the exact given original RIGHT algorithm to the actual literal strict source. -/
def strictOriginalCofibrantFactorizationData :
    FunctorialFactorizationData strictSourceCofibrations.{u, v}
      strictSourceTrivialFibrations :=
  (originalCofibrantFactorizationData.{u, v}).ofEquivalence
    (EnrichedProjective.BasedNativePresentation.strictEquivalence
      (A := PointedCGWH.SymmetricDRight.Index))

omit B in
/-- The whole strict middle retains actual restriction, original source algorithm and extension. -/
theorem strictOriginalCofibrantFactorizationData_Z [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :
  (strictOriginalCofibrantFactorizationData.{u,
  v}).Z =
    strictRestriction.mapArrow ⋙ (originalCofibrantFactorizationData.{u, v}).Z ⋙ strictExtension
      := rfl

omit B in
/-- The whole first map retains the actual strict unit and original source first map. -/
theorem strictOriginalCofibrantFactorizationData_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    (strictOriginalCofibrantFactorizationData.{u, v}).i.app f =
      (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)).unitIso.hom.app f.left ≫
        strictExtension.map ((originalCofibrantFactorizationData.{u, v}).i.app
          (strictRestriction.mapArrow.obj f)) :=
  actual_strict_i_app (originalCofibrantFactorizationData.{u, v}) f

omit B in
/-- The whole second map retains the original source second map and actual strict unit inverse. -/
theorem strictOriginalCofibrantFactorizationData_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    (strictOriginalCofibrantFactorizationData.{u, v}).p.app f =
      strictExtension.map ((originalCofibrantFactorizationData.{u, v}).p.app
        (strictRestriction.mapArrow.obj f)) ≫
        (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)).unitIso.inv.app f.right :=
  actual_strict_p_app (originalCofibrantFactorizationData.{u, v}) f

omit B in
/-- Every full original Arrow square retains its whole original source middle map. -/
theorem strictOriginalCofibrantFactorizationData_Z_map [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {f g : CategoryTheory.Arrow StrictSourceCarrier.{u, v}} (φ : f ⟶ g) :
    (strictOriginalCofibrantFactorizationData.{u, v}).Z.map φ = strictExtension.map
      ((originalCofibrantFactorizationData.{u, v}).Z.map (strictRestriction.mapArrow.map φ)) := rfl

omit B in
/-- Both whole maps factor the same entire strict source arrow. -/
theorem strictOriginalCofibrantFactorizationData_fac [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    (strictOriginalCofibrantFactorizationData.{u, v}).i.app f ≫
      (strictOriginalCofibrantFactorizationData.{u, v}).p.app f = f.hom :=
  (strictOriginalCofibrantFactorizationData.{u, v}).fac_app

omit B in
/-- The exact original RIGHT algorithm has a literal chosen-zero strict middle. -/
theorem strictOriginalCofibrantFactorizationData_base [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    ((strictOriginalCofibrantFactorizationData.{u, v}).Z.obj f).obj.toEnrichedFunctor.obj
      EnrichedZeroCompletion.zero = (0 : PointedCGWH.{u, v}) :=
  ((strictOriginalCofibrantFactorizationData.{u, v}).Z.obj f).property

/-- Both exact original algorithm maps have the actual constructed strict classes. -/
theorem strictOriginalCofibrantFactorizationData_classes (f : CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    cofibrations StrictSourceCarrier.{u, v} ((strictOriginalCofibrantFactorizationData.{u,
      v}).i.app f) ∧
      trivialFibrations StrictSourceCarrier.{u, v} ((strictOriginalCofibrantFactorizationData.{u,
        v}).p.app f) := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} :=
    EnrichedProjective.BasedNativePresentation.strictModelCategory
  have h := strictSourceClassReadback.{u, v} (B := B)
  exact ⟨(Iff.of_eq (congrArg (fun P : MorphismProperty StrictSourceCarrier.{u, v} =>
      P (strictOriginalCofibrantFactorizationData.i.app f)) h.2.1)).mpr
        (strictOriginalCofibrantFactorizationData.hi f),
    (Iff.of_eq (congrArg (fun P : MorphismProperty StrictSourceCarrier.{u, v} =>
      P (strictOriginalCofibrantFactorizationData.p.app f)) h.2.2.2.1)).mpr
        (strictOriginalCofibrantFactorizationData.hp f)⟩

/-- The actual chosen-base counit recovers the entire original source middle. -/
def strictOriginalCofibrantFactorizationDataComparisonIso :
  (strictOriginalCofibrantFactorizationData.{u, v}).Z ⋙ strictRestriction ≅
    strictRestriction.mapArrow ⋙ (originalCofibrantFactorizationData.{u, v}).Z :=
  (originalCofibrantFactorizationData.{u, v}).ofEquivalenceZComparisonIso
    (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index))

omit B in
/-- The original source first map is recovered through the full actual comparison. -/
theorem strictOriginalCofibrantFactorizationData_mapped_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    strictRestriction.map ((strictOriginalCofibrantFactorizationData.{u, v}).i.app f) ≫
      (strictOriginalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app f =
        (originalCofibrantFactorizationData.{u, v}).i.app (strictRestriction.mapArrow.obj f) :=
  actual_strict_comparison_i (originalCofibrantFactorizationData.{u, v})
    strictOriginalCofibrantFactorizationDataComparisonIso rfl f

omit B in
/-- The original source second map is recovered through the full actual comparison. -/
theorem strictOriginalCofibrantFactorizationData_mapped_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    (strictOriginalCofibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
      (originalCofibrantFactorizationData.{u, v}).p.app (strictRestriction.mapArrow.obj f) =
        strictRestriction.map ((strictOriginalCofibrantFactorizationData.{u, v}).p.app f) :=
  actual_strict_comparison_p (originalCofibrantFactorizationData.{u, v})
    strictOriginalCofibrantFactorizationDataComparisonIso rfl f

/-- Transport the exact given original RIGHT algorithm to the actual literal strict source. -/
def strictOriginalFibrantFactorizationData :
    FunctorialFactorizationData strictSourceTrivialCofibrations.{u, v}
      strictSourceFibrations :=
  (originalFibrantFactorizationData.{u, v}).ofEquivalence
    (EnrichedProjective.BasedNativePresentation.strictEquivalence
      (A := PointedCGWH.SymmetricDRight.Index))

omit B in
/-- The whole strict middle retains actual restriction, original source algorithm and extension. -/
theorem strictOriginalFibrantFactorizationData_Z [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :
  (strictOriginalFibrantFactorizationData.{u,
  v}).Z =
    strictRestriction.mapArrow ⋙ (originalFibrantFactorizationData.{u, v}).Z ⋙ strictExtension :=
      rfl

omit B in
/-- The whole first map retains the actual strict unit and original source first map. -/
theorem strictOriginalFibrantFactorizationData_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow StrictSourceCarrier.{u,
  v}) :
    (strictOriginalFibrantFactorizationData.{u, v}).i.app f =
      (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)).unitIso.hom.app f.left ≫
        strictExtension.map ((originalFibrantFactorizationData.{u, v}).i.app
          (strictRestriction.mapArrow.obj f)) :=
  actual_strict_i_app (originalFibrantFactorizationData.{u, v}) f

omit B in
/-- The whole second map retains the original source second map and actual strict unit inverse. -/
theorem strictOriginalFibrantFactorizationData_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow StrictSourceCarrier.{u,
  v}) :
    (strictOriginalFibrantFactorizationData.{u, v}).p.app f =
      strictExtension.map ((originalFibrantFactorizationData.{u, v}).p.app
        (strictRestriction.mapArrow.obj f)) ≫
        (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index)).unitIso.inv.app f.right :=
  actual_strict_p_app (originalFibrantFactorizationData.{u, v}) f

omit B in
/-- Every full original Arrow square retains its whole original source middle map. -/
theorem strictOriginalFibrantFactorizationData_Z_map [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {f g : CategoryTheory.Arrow StrictSourceCarrier.{u, v}} (φ : f ⟶ g) :
    (strictOriginalFibrantFactorizationData.{u, v}).Z.map φ = strictExtension.map
      ((originalFibrantFactorizationData.{u, v}).Z.map (strictRestriction.mapArrow.map φ)) := rfl

omit B in
/-- Both whole maps factor the same entire strict source arrow. -/
theorem strictOriginalFibrantFactorizationData_fac [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    (strictOriginalFibrantFactorizationData.{u, v}).i.app f ≫
      (strictOriginalFibrantFactorizationData.{u, v}).p.app f = f.hom :=
  (strictOriginalFibrantFactorizationData.{u, v}).fac_app

omit B in
/-- The exact original RIGHT algorithm has a literal chosen-zero strict middle. -/
theorem strictOriginalFibrantFactorizationData_base [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    ((strictOriginalFibrantFactorizationData.{u, v}).Z.obj f).obj.toEnrichedFunctor.obj
      EnrichedZeroCompletion.zero = (0 : PointedCGWH.{u, v}) :=
  ((strictOriginalFibrantFactorizationData.{u, v}).Z.obj f).property

/-- Both exact original algorithm maps have the actual constructed strict classes. -/
theorem strictOriginalFibrantFactorizationData_classes (f : CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    trivialCofibrations StrictSourceCarrier.{u, v} ((strictOriginalFibrantFactorizationData.{u,
      v}).i.app f) ∧
      fibrations StrictSourceCarrier.{u, v} ((strictOriginalFibrantFactorizationData.{u, v}).p.app
        f) := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} :=
    EnrichedProjective.BasedNativePresentation.strictModelCategory
  have h := strictSourceClassReadback.{u, v} (B := B)
  exact ⟨(Iff.of_eq (congrArg (fun P : MorphismProperty StrictSourceCarrier.{u, v} =>
      P (strictOriginalFibrantFactorizationData.i.app f)) h.2.2.2.2)).mpr
        (strictOriginalFibrantFactorizationData.hi f),
    (Iff.of_eq (congrArg (fun P : MorphismProperty StrictSourceCarrier.{u, v} =>
      P (strictOriginalFibrantFactorizationData.p.app f)) h.2.2.1)).mpr
        (strictOriginalFibrantFactorizationData.hp f)⟩

/-- The actual chosen-base counit recovers the entire original source middle. -/
def strictOriginalFibrantFactorizationDataComparisonIso :
  (strictOriginalFibrantFactorizationData.{u, v}).Z ⋙ strictRestriction ≅
    strictRestriction.mapArrow ⋙ (originalFibrantFactorizationData.{u, v}).Z :=
  (originalFibrantFactorizationData.{u, v}).ofEquivalenceZComparisonIso
    (EnrichedProjective.BasedNativePresentation.strictEquivalence
    (A := PointedCGWH.SymmetricDRight.Index))

omit B in
/-- The original source first map is recovered through the full actual comparison. -/
theorem strictOriginalFibrantFactorizationData_mapped_i [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    strictRestriction.map ((strictOriginalFibrantFactorizationData.{u, v}).i.app f) ≫
      (strictOriginalFibrantFactorizationDataComparisonIso.{u, v}).hom.app f =
        (originalFibrantFactorizationData.{u, v}).i.app (strictRestriction.mapArrow.obj f) :=
  actual_strict_comparison_i (originalFibrantFactorizationData.{u, v})
    strictOriginalFibrantFactorizationDataComparisonIso rfl f

omit B in
/-- The original source second map is recovered through the full actual comparison. -/
theorem strictOriginalFibrantFactorizationData_mapped_p [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] (f :
  CategoryTheory.Arrow
  StrictSourceCarrier.{u, v}) :
    (strictOriginalFibrantFactorizationDataComparisonIso.{u, v}).hom.app f ≫
      (originalFibrantFactorizationData.{u, v}).p.app (strictRestriction.mapArrow.obj f) =
        strictRestriction.map ((strictOriginalFibrantFactorizationData.{u, v}).p.app f) :=
  actual_strict_comparison_p (originalFibrantFactorizationData.{u, v})
    strictOriginalFibrantFactorizationDataComparisonIso rfl f

omit B in
/-- Both complete strict factor maps land in the fixed canonical Spectrum classes. -/
theorem strictOriginalCofibrantFactorizationData_canonical_classes [_B : OrderBot
  realizedGeneratorCardinal.{v}.ord.ToType] (f : Arrow StrictSourceCarrier.{u, v}) :
    cofibrations Spectrum.{u, v} (canonicalStrictSourcePresentation.functor.map
      (strictOriginalCofibrantFactorizationData.i.app f)) ∧
      trivialFibrations Spectrum.{u, v} (canonicalStrictSourcePresentation.functor.map
        (strictOriginalCofibrantFactorizationData.p.app f)) :=
  ⟨strictOriginalCofibrantFactorizationData.hi f, strictOriginalCofibrantFactorizationData.hp f⟩

omit B in
/-- Both complete strict factor maps land in the fixed canonical Spectrum classes. -/
theorem strictOriginalFibrantFactorizationData_canonical_classes [_B : OrderBot
  realizedGeneratorCardinal.{v}.ord.ToType] (f : Arrow StrictSourceCarrier.{u, v}) :
    trivialCofibrations Spectrum.{u, v} (canonicalStrictSourcePresentation.functor.map
      (strictOriginalFibrantFactorizationData.i.app f)) ∧
      fibrations Spectrum.{u, v} (canonicalStrictSourcePresentation.functor.map
        (strictOriginalFibrantFactorizationData.p.app f)) :=
  ⟨strictOriginalFibrantFactorizationData.hi f, strictOriginalFibrantFactorizationData.hp f⟩

end PointedCGWH.Spectra.Symmetric.DRightPresentation
