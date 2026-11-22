/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.RepresentableBoundaryLeibnizComparison
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalScalarSM7
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanCartesian
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct

/-!
# Original representable tests, monic factors and actual free-cell extension

The only locality assumption is the original representable-product condition
for the tested arrow in the localization at S. The family criterion is its
specialization to the arrows S a. All monic tests and the generator certificate
used by the native lifting theorem are derived internally. The auxiliary replacement and both
augmentation components are the actual original free-cell constructions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open scoped MonoidalCategory Simplicial SSet.modelCategoryQuillen
open scoped SimplicialPresheaf.InjectiveKan

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D]

/-- Actual baseline weakness is preserved by both products, without endpoint fibrancy. -/
theorem originalBaseProductWeak {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ f)
    (Y : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ (Y ◁ f) ∧
      SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ (f ▷ Y) := by
  have hl : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ (Y ◁ f) := by
    intro a
    let _ : WeakEquivalence (f.app a) := (weakEquivalence_iff _).mpr (hf a)
    let _ : Adjunction.IsQuillenAdjunction (ihom.adjunction (Y.obj a)) :=
      ihomAdjunction_isQuillenAdjunction_of_isCofibrant (Y.obj a)
    have h : WeakEquivalence (Y.obj a ◁ f.app a) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
        (adj := ihom.adjunction (Y.obj a)) (f.app a)
    exact (weakEquivalence_iff _).mp h
  let e : Arrow.mk (f ▷ Y) ≅ Arrow.mk (Y ◁ f) :=
    Arrow.isoMk (β_ A Y) (β_ B Y) (by ext a n z; rfl)
  let W := SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ
  exact ⟨hl, (W.arrow_mk_iso_iff e).mpr hl⟩

variable [Small.{u} D] [LocallySmall.{u} D]
attribute [local instance] modelCategory

/-- The SAME internally selected global right factor is baseline weak. -/
theorem originalMonicFactorRightBaseWeak (s : Arrow (SimplicialPresheaf.{u} D)) :
    SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ
      (originalMonicLocalizerFactor s).p := by
  have ht : trivialFibrations (SimplicialPresheaf.{u} D)
      (originalMonicLocalizerFactor s).p := by
    rw [(data D).trivialFibrations_eq]
    exact (originalMonicLocalizerFactor s).hp
  have hw := ht.2
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences
    (originalMonicLocalizerFactor s).p at hw
  rw [(data D).weakEquivalences_eq] at hw
  exact hw

private theorem baselineWeakLocal {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ f) :
    originalLocalEquivalences S f := by
  apply weakEquivalences_le_originalLocalEquivalences S f
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences f
  rw [(data D).weakEquivalences_eq]
  exact hf

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem originalMonoProductLeft {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Y : SimplicialPresheaf.{u} D)
    (hf : monomorphisms (SimplicialPresheaf.{u} D) f) :
    monomorphisms (SimplicialPresheaf.{u} D) (Y ◁ f) := by
  change Mono f at hf
  change Mono (Y ◁ f)
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro d
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  apply (mono_iff_injective _).mpr
  have hd : Mono (f.app d) := (NatTrans.mono_iff_mono_app f).mp hf d
  have hn : Function.Injective ((f.app d).app n) :=
    (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app (f.app d)).mp hd n)
  intro x y h
  change (x.1, (f.app d).app n x.2) = (y.1, (f.app d).app n y.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (hn (Prod.mk.inj h).2)

attribute [local instance] originalLocalEquivalences_hasTwoOutOfThreeProperty
  originalLocalEquivalences_isStableUnderRetracts
  localTrivialMonomorphisms_isStableUnderRetracts

/-- The representable tests for one arbitrary arrow give the same actual monic-factor tests. -/
theorem originalMonicFactorRepresentableLocalTrivialOfRepresentable {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (s : Arrow (SimplicialPresheaf.{u} D))
    (hRep : ∀ d : D, originalLocalEquivalences S (s.hom ▷ discreteYoneda.obj d)) (d : D) :
    localTrivialMonomorphisms S
      (discreteYoneda.obj d ◁ (originalMonicLocalizerFactor s).i) := by
  let q := originalMonicLocalizerFactor s
  let Y := discreteYoneda.obj d
  have hm : monomorphisms (SimplicialPresheaf.{u} D) (Y ◁ q.i) :=
    originalMonoProductLeft q.i Y q.hi
  let e : Arrow.mk (s.hom ▷ Y) ≅ Arrow.mk (Y ◁ s.hom) :=
    Arrow.isoMk (β_ s.left Y) (β_ s.right Y) (by ext z n x; rfl)
  have hs : originalLocalEquivalences S (Y ◁ s.hom) :=
    ((originalLocalEquivalences S).arrow_mk_iso_iff e).mp (hRep d)
  have hp : originalLocalEquivalences S (Y ◁ q.p) := baselineWeakLocal S _
    (originalBaseProductWeak q.p (originalMonicFactorRightBaseWeak s) Y).1
  have hfac : (Y ◁ q.i) ≫ (Y ◁ q.p) = Y ◁ s.hom := by
    rw [← MonoidalCategory.whiskerLeft_comp, q.fac]
  have hi : originalLocalEquivalences S (Y ◁ q.i) :=
    (originalLocalEquivalences S).of_postcomp _ _ hp (hfac.symm ▸ hs)
  exact ⟨hm, hi⟩

/-- The family-generator monic-factor test is the arbitrary-arrow result at `S a`. -/
theorem originalMonicFactorRepresentableLocalTrivial {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ (a : I) (d : D), originalLocalEquivalences S
      ((S a).hom ▷ discreteYoneda.obj d)) (a : I) (d : D) :
    localTrivialMonomorphisms S
      (discreteYoneda.obj d ◁ (originalMonicLocalizerFactor (S a)).i) :=
  originalMonicFactorRepresentableLocalTrivialOfRepresentable S (S a) (hCriterion a) d

variable {I : Type i} [Small.{u} I]

/-- Full scalar SM7 and the WHOLE generator Iso prove the actual free generator locally trivial. -/
theorem originalFreeBoundaryFactorLocalTrivialOfRepresentable
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (s : Arrow (SimplicialPresheaf.{u} D))
    (hRep : ∀ d : D, originalLocalEquivalences S (s.hom ▷ discreteYoneda.obj d))
    (d : D) (n : ℕ) :
    localTrivialMonomorphisms S
      (Arrow.mk ((freeEvaluationFunctor.obj d).map (SSet.boundary.{u} n).ι) □
        Arrow.mk (originalMonicLocalizerFactor s).i).hom := by
  let q := originalMonicLocalizerFactor s
  let t := discreteYoneda.obj d ◁ q.i
  let pp := scalarPushoutObjObj t (SSet.boundary.{u} n).ι
  have ht : localTrivialMonomorphisms S t :=
    originalMonicFactorRepresentableLocalTrivialOfRepresentable S s hRep d
  have hc : localTrivialMonomorphisms S pp.ι := by
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    have htc : trivialCofibrations (SimplicialPresheaf.{u} D) t := by
      rw [(originalLocalSmithData S).trivialCofibrations_eq]
      exact ht
    have hb : cofibrations SSet.{u} (SSet.boundary.{u} n).ι :=
      (cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono _)
    have h := localized_scalar_pushoutObjObj_trivialCofibration_of_left
      S t (SSet.boundary.{u} n).ι pp htc hb
    rw [(originalLocalSmithData S).trivialCofibrations_eq] at h
    exact h
  exact ((localTrivialMonomorphisms S).arrow_mk_iso_iff
    (freeBoundaryMonicFactorIso (fun _ : PUnit.{1} => s) PUnit.unit d n)).mpr hc

/-- The internally proved generator law extends to the actual original double-left class. -/
theorem originalFreeLeftFactorProductLocalTrivialOfRepresentable
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (s : Arrow (SimplicialPresheaf.{u} D))
    (hRep : ∀ d : D, originalLocalEquivalences S (s.hom ▷ discreteYoneda.obj d))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (hf : (projectiveBoundaryMaps (D := D)).rlp.llp f) :
    localTrivialMonomorphisms S
      (Arrow.mk f □ Arrow.mk (originalMonicLocalizerFactor s).i).hom := by
  let q := originalMonicLocalizerFactor s
  let A := projectiveBoundaryMaps (D := D)
  let B := MorphismProperty.ofHoms (fun _ : PUnit.{1} => q.i)
  let M := localTrivialMonomorphisms S
  have hM : M.rlp.llp = M := by
    simpa only [M, localTrivialMonomorphisms_eq_llp] using
      MorphismProperty.llp_rlp_llp (localWeakRightTests S)
  have hi : B.rlp.llp q.i := (MorphismProperty.le_llp_rlp B) _
    (MorphismProperty.ofHoms.mk (f := fun _ : PUnit.{1} => q.i) PUnit.unit)
  have hfree : ∀ ⦃U V W Z : SimplicialPresheaf.{u} D⦄ (c : U ⟶ V), A c →
      ∀ (b : W ⟶ Z), B b → M.rlp.llp (Arrow.mk c □ Arrow.mk b).hom := by
    intro U V W Z c hc b hb
    obtain ⟨z, hz⟩ := (MorphismProperty.adjointFamilyGenerators_iff
      (fun e : Dᵒᵖ => freeEvaluationFunctor.obj e.unop) SSet.modelCategoryQuillen.I.{u} c).mp hc
    obtain ⟨n, hn⟩ := (MorphismProperty.ofHoms_iff
      (fun n : ℕ => (SSet.boundary.{u} n).ι) z.2.1.hom).mp z.2.2
    obtain ⟨_, hb⟩ := (MorphismProperty.ofHoms_iff (fun _ : PUnit.{1} => q.i) b).mp hb
    let e₁ : Arrow.mk c ≅ Arrow.mk
        ((freeEvaluationFunctor.obj z.1.unop).map (SSet.boundary.{u} n).ι) :=
      eqToIso hz ≪≫ (freeEvaluationFunctor.obj z.1.unop).mapArrow.mapIso (eqToIso hn)
    let e₂ : Arrow.mk b ≅ Arrow.mk q.i := eqToIso hb
    let e := (MonoidalCategory.Arrow.pushoutProduct.mapIso e₁).app (Arrow.mk b) ≪≫
      (MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk
        ((freeEvaluationFunctor.obj z.1.unop).map (SSet.boundary.{u} n).ι))).mapIso e₂
    rw [hM]
    exact (M.arrow_mk_iso_iff e).mpr
      (originalFreeBoundaryFactorLocalTrivialOfRepresentable S s hRep z.1.unop n)
  have h := MorphismProperty.pushoutProduct_mem_rlp_llp A B M hfree hf hi
  rwa [hM] at h

/-- The auxiliary free-cell replacement is a constructed left-class object, not a chosen Q/R. -/
theorem originalAuxiliaryProductFactorLocalTrivialOfRepresentable
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (s : Arrow (SimplicialPresheaf.{u} D))
    (hRep : ∀ d : D, originalLocalEquivalences S (s.hom ▷ discreteYoneda.obj d))
    (Y : SimplicialPresheaf.{u} D) :
    localTrivialMonomorphisms S
      ((representableBoundaryReplacement (D := D)).obj Y ◁
        (originalMonicLocalizerFactor s).i) := by
  let Q := representableBoundaryReplacement (D := D)
  have hleft : (projectiveBoundaryMaps (D := D)).rlp.llp (initial.to (Q.obj Y)) := by
    have he : (representableBoundaryFactorization (D := D)).i.app
        (Arrow.mk (initial.to Y)) = initial.to (Q.obj Y) := initialIsInitial.hom_ext _ _
    rw [← he]
    exact (representableBoundaryFactorization (D := D)).hi (Arrow.mk (initial.to Y))
  have h := originalFreeLeftFactorProductLocalTrivialOfRepresentable S s hRep
    (initial.to (Q.obj Y)) hleft
  let e := MonoidalCategory.Arrow.PushoutProduct.isInitialIso' (W := Q.obj Y)
    (Arrow.mk (originalMonicLocalizerFactor s).i) (initialIsInitial
      (C := SimplicialPresheaf.{u} D))
  exact ((localTrivialMonomorphisms S).arrow_mk_iso_iff e).mp h

/-- The representable tests for one arbitrary arrow give its monic-factor product and both product tests. -/
theorem originalArrowRepresentableCriterion_allProductWeak
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (s : Arrow (SimplicialPresheaf.{u} D))
    (hRep : ∀ d : D, originalLocalEquivalences S (s.hom ▷ discreteYoneda.obj d))
    (Y : SimplicialPresheaf.{u} D) :
    localTrivialMonomorphisms S (Y ◁ (originalMonicLocalizerFactor s).i) ∧
      originalLocalEquivalences S (Y ◁ s.hom) ∧
      originalLocalEquivalences S (s.hom ▷ Y) := by
  let q := originalMonicLocalizerFactor s
  let Q := representableBoundaryReplacement (D := D)
  let ε := representableBoundaryAugmentation (D := D)
  have haux : localTrivialMonomorphisms S (Q.obj Y ◁ q.i) :=
    originalAuxiliaryProductFactorLocalTrivialOfRepresentable S s hRep Y
  have he : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ (ε.app Y) :=
    (representableBoundaryAugmentation_laws (𝟙 Y) (𝟙 Y)).2.2.2.2.2.2.2
  have heA : originalLocalEquivalences S (ε.app Y ▷ s.left) := baselineWeakLocal S _
    (originalBaseProductWeak (ε.app Y) he s.left).2
  have heB : originalLocalEquivalences S (ε.app Y ▷ q.Z) := baselineWeakLocal S _
    (originalBaseProductWeak (ε.app Y) he q.Z).2
  have hsquare : (Q.obj Y ◁ q.i) ≫ (ε.app Y ▷ q.Z) =
      (ε.app Y ▷ s.left) ≫ (Y ◁ q.i) :=
    ((curriedTensor (SimplicialPresheaf.{u} D)).map (ε.app Y)).naturality q.i
  have hcomp : originalLocalEquivalences S
      ((ε.app Y ▷ s.left) ≫ (Y ◁ q.i)) :=
    hsquare ▸ (originalLocalEquivalences S).comp_mem _ _ haux.2 heB
  have hwi : originalLocalEquivalences S (Y ◁ q.i) :=
    (originalLocalEquivalences S).of_precomp _ _ heA hcomp
  have hmi : localTrivialMonomorphisms S (Y ◁ q.i) :=
    ⟨originalMonoProductLeft q.i Y q.hi, hwi⟩
  have hwp : originalLocalEquivalences S (Y ◁ q.p) := baselineWeakLocal S _
    (originalBaseProductWeak q.p (originalMonicFactorRightBaseWeak s) Y).1
  have hs : originalLocalEquivalences S (Y ◁ s.hom) := by
    have h := (originalLocalEquivalences S).comp_mem _ _ hwi hwp
    rwa [← MonoidalCategory.whiskerLeft_comp, q.fac] at h
  let e : Arrow.mk (s.hom ▷ Y) ≅ Arrow.mk (Y ◁ s.hom) :=
    Arrow.isoMk (β_ s.left Y) (β_ s.right Y) (by ext z n x; rfl)
  exact ⟨hmi, hs, ((originalLocalEquivalences S).arrow_mk_iso_iff e).mpr hs⟩

/-- The family-generator free-boundary test specializes the arbitrary-arrow result. -/
theorem originalFreeBoundaryFactorLocalTrivial
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ (a : I) (d : D), originalLocalEquivalences S
      ((S a).hom ▷ discreteYoneda.obj d)) (a : I) (d : D) (n : ℕ) :
    localTrivialMonomorphisms S
      (Arrow.mk ((freeEvaluationFunctor.obj d).map (SSet.boundary.{u} n).ι) □
        Arrow.mk (originalMonicLocalizerFactor (S a)).i).hom :=
  originalFreeBoundaryFactorLocalTrivialOfRepresentable S (S a) (hCriterion a) d n

/-- The family-generator free-left test specializes the arbitrary-arrow result. -/
theorem originalFreeLeftFactorProductLocalTrivial
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ (a : I) (d : D), originalLocalEquivalences S
      ((S a).hom ▷ discreteYoneda.obj d)) (a : I)
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (hf : (projectiveBoundaryMaps (D := D)).rlp.llp f) :
    localTrivialMonomorphisms S
      (Arrow.mk f □ Arrow.mk (originalMonicLocalizerFactor (S a)).i).hom :=
  originalFreeLeftFactorProductLocalTrivialOfRepresentable S (S a) (hCriterion a) f hf

/-- The family-generator replacement test specializes the arbitrary-arrow result. -/
theorem originalAuxiliaryProductFactorLocalTrivial
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ (a : I) (d : D), originalLocalEquivalences S
      ((S a).hom ▷ discreteYoneda.obj d)) (a : I) (Y : SimplicialPresheaf.{u} D) :
    localTrivialMonomorphisms S
      ((representableBoundaryReplacement (D := D)).obj Y ◁
        (originalMonicLocalizerFactor (S a)).i) :=
  originalAuxiliaryProductFactorLocalTrivialOfRepresentable S (S a) (hCriterion a) Y

/-- The full family criterion specializes the arbitrary-arrow theorem without dropping its factor test. -/
theorem originalRepresentableCriterion_allProductWeak
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ (a : I) (d : D), originalLocalEquivalences S
      ((S a).hom ▷ discreteYoneda.obj d)) (a : I) (Y : SimplicialPresheaf.{u} D) :
    localTrivialMonomorphisms S (Y ◁ (originalMonicLocalizerFactor (S a)).i) ∧
      originalLocalEquivalences S (Y ◁ (S a).hom) ∧
      originalLocalEquivalences S ((S a).hom ▷ Y) :=
  originalArrowRepresentableCriterion_allProductWeak S (S a) (hCriterion a) Y

end SimplicialPresheaf.InjectiveKan
