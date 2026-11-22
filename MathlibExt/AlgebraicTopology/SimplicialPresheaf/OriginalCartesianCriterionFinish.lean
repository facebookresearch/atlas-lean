/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original Cartesian criterion and global closed lifting laws.
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalCartesianLocalPowers
import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# A representable criterion for Cartesian localized models

For a working-small localizing family on a working-small, locally small site, the chosen
localized model is a closed symmetric Cartesian monoidal model exactly when every localizing
arrow remains locally weak after product with every representable presheaf. The same criterion
is equivalent to the full Cartesian pushout-product and global pullback-Hom axioms, with both
trivial branches proved for the supplied structural squares.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open scoped SimplicialPresheaf.InjectiveKan SSet.modelCategoryQuillen MonoidalCategory
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]
attribute [local instance] originalLocalEquivalences_hasTwoOutOfThreeProperty
  originalLocalEquivalences_isStableUnderRetracts
  localTrivialMonomorphisms_isStableUnderCobaseChange

omit [Small.{u} D] [LocallySmall.{u} D] [Small.{u} I] in
private theorem actualCartesianMonoProducts
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Y : SimplicialPresheaf.{u} D)
    (hf : monomorphisms (SimplicialPresheaf.{u} D) f) :
    monomorphisms (SimplicialPresheaf.{u} D) (Y ◁ f) ∧
      monomorphisms (SimplicialPresheaf.{u} D) (f ▷ Y) := by
  have hl : monomorphisms (SimplicialPresheaf.{u} D) (Y ◁ f) := by
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
  let e : Arrow.mk (f ▷ Y) ≅ Arrow.mk (Y ◁ f) :=
    Arrow.isoMk (β_ A Y) (β_ B Y) (by ext d n x; rfl)
  exact ⟨hl, ((monomorphisms (SimplicialPresheaf.{u} D)).arrow_mk_iso_iff e).mpr hl⟩

private theorem actualCartesianPPMono
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j)
    (hi : monomorphisms (SimplicialPresheaf.{u} D) i)
    (hj : monomorphisms (SimplicialPresheaf.{u} D) j) :
    monomorphisms (SimplicialPresheaf.{u} D) sq.ι := by
  have hci : cofibrations (SimplicialPresheaf.{u} D) i := by
    change (data D).model.categoryWithCofibrations.cofibrations i
    rw [(data D).cofibrations_eq]
    exact hi
  have hcj : cofibrations (SimplicialPresheaf.{u} D) j := by
    change (data D).model.categoryWithCofibrations.cofibrations j
    rw [(data D).cofibrations_eq]
    exact hj
  have h := cartesian_pushoutObjObj_cofibration i j sq hci hcj
  change (data D).model.categoryWithCofibrations.cofibrations sq.ι at h
  rwa [(data D).cofibrations_eq] at h

/-- Cofibrations give the SAME supplied Cartesian structural cofibration in the local model. -/
theorem originalLocalCartesianPP_cofibration
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i → cofibrations (SimplicialPresheaf.{u} D) j →
      cofibrations (SimplicialPresheaf.{u} D) sq.ι := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hj
  change (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations i at hi
  change (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations j at hj
  rw [(originalLocalSmithData S).cofibrations_eq] at hi hj
  change (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations sq.ι
  rw [(originalLocalSmithData S).cofibrations_eq]
  exact actualCartesianPPMono i j sq hi hj

/-- The left-trivial branch uses the original flipped square and BOTH factor maps. -/
theorem originalRepresentableCriterion_cartesianPP_trivialLeft
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d))
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    trivialCofibrations (SimplicialPresheaf.{u} D) i → cofibrations (SimplicialPresheaf.{u} D) j →
      trivialCofibrations (SimplicialPresheaf.{u} D) sq.ι := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hj
  have hmi : localTrivialMonomorphisms S i := by
    rwa [(originalLocalSmithData S).trivialCofibrations_eq] at hi
  have hmj : monomorphisms (SimplicialPresheaf.{u} D) j := by
    change (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations j at hj
    rwa [(originalLocalSmithData S).cofibrations_eq] at hj
  have hiK : localTrivialMonomorphisms S (i ▷ K) :=
    ⟨(actualCartesianMonoProducts i K hmi.1).2,
      (originalRepresentableCriterion_allArrowProductWeak S hCriterion i hmi.2 K).2⟩
  have hinr : localTrivialMonomorphisms S sq.inr :=
    (localTrivialMonomorphisms S).of_isPushout sq.isPushout.flip hiK
  have hiL : originalLocalEquivalences S (i ▷ L) :=
    (originalRepresentableCriterion_allArrowProductWeak S hCriterion i hmi.2 L).2
  have hcomp : originalLocalEquivalences S (sq.inr ≫ sq.ι) := sq.inr_ι.symm ▸ hiL
  have hweak := (originalLocalEquivalences S).of_precomp sq.inr sq.ι hinr.2 hcomp
  rw [(originalLocalSmithData S).trivialCofibrations_eq]
  exact ⟨actualCartesianPPMono i j sq hmi.1 hmj, hweak⟩

/-- The right-trivial branch uses the original unflipped square and BOTH factor maps. -/
theorem originalRepresentableCriterion_cartesianPP_trivialRight
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d))
    {A B K L : SimplicialPresheaf.{u} D} (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} D)).PushoutObjObj i j) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    cofibrations (SimplicialPresheaf.{u} D) i → trivialCofibrations (SimplicialPresheaf.{u} D) j →
      trivialCofibrations (SimplicialPresheaf.{u} D) sq.ι := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  intro hi hj
  have hmi : monomorphisms (SimplicialPresheaf.{u} D) i := by
    change (originalLocalSmithData S).model.categoryWithCofibrations.cofibrations i at hi
    rwa [(originalLocalSmithData S).cofibrations_eq] at hi
  have hmj : localTrivialMonomorphisms S j := by
    rwa [(originalLocalSmithData S).trivialCofibrations_eq] at hj
  have hjA : localTrivialMonomorphisms S (A ◁ j) :=
    ⟨(actualCartesianMonoProducts j A hmj.1).1,
      (originalRepresentableCriterion_allArrowProductWeak S hCriterion j hmj.2 A).1⟩
  have hinl : localTrivialMonomorphisms S sq.inl :=
    (localTrivialMonomorphisms S).of_isPushout sq.isPushout hjA
  have hjB : originalLocalEquivalences S (B ◁ j) :=
    (originalRepresentableCriterion_allArrowProductWeak S hCriterion j hmj.2 B).1
  have hcomp : originalLocalEquivalences S (sq.inl ≫ sq.ι) := sq.inl_ι.symm ▸ hjB
  have hweak := (originalLocalEquivalences S).of_precomp sq.inl sq.ι hinl.2 hcomp
  rw [(originalLocalSmithData S).trivialCofibrations_eq]
  exact ⟨actualCartesianPPMono i j sq hmi hmj.1, hweak⟩

/-- The native Cartesian monoidal model witness is constructed on the SAME original-S model. -/
theorem originalRepresentableCriterion_closedCartesianModel
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    IsClosedSymmetricMonoidalModelCategory (SimplicialPresheaf.{u} D) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  let _ : IsCofibrant (𝟙_ (SimplicialPresheaf.{u} D)) := (originalLocalSmithData S).all_cofibrant _
  exact isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    (SimplicialPresheaf.{u} D)
    (by
      intro A B K L i j hi hj
      exact originalLocalCartesianPP_cofibration S i j
        (Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D)) i j) hi hj)
    (by
      intro A B K L i j hi hj
      exact originalRepresentableCriterion_cartesianPP_trivialLeft S hCriterion i j
        (Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D)) i j) hi hj)
    (by
      intro A B K L i j hi hj
      exact originalRepresentableCriterion_cartesianPP_trivialRight S hCriterion i j
        (Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D)) i j) hi hj)

/-- Full native Cartesian compatibility is equivalent to the exact ORIGINAL representable
criterion. -/
theorem originalLocalCartesianModel_iff_representableCriterion
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    IsClosedSymmetricMonoidalModelCategory (SimplicialPresheaf.{u} D) ↔
      ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  constructor
  · intro hModel
    let _ : IsClosedSymmetricMonoidalModelCategory (SimplicialPresheaf.{u} D) := hModel
    intro a d
    have hs : originalLocalEquivalences S (S a).hom := by
      intro Z hZ
      exact hZ.2 a
    let Y := discreteYoneda.obj d
    let _ : IsCofibrant Y := (originalLocalSmithData S).all_cofibrant Y
    let _ : IsCofibrant (S a).left := (originalLocalSmithData S).all_cofibrant _
    let _ : IsCofibrant (S a).right := (originalLocalSmithData S).all_cofibrant _
    let _ : Adjunction.IsQuillenAdjunction (ihom.adjunction Y) :=
      ihomAdjunction_isQuillenAdjunction_of_isCofibrant Y
    have hsLocal : weakEquivalences (SimplicialPresheaf.{u} D) (S a).hom := by
      change
          (originalLocalSmithData S).model.categoryWithWeakEquivalences.weakEquivalences (S a).hom
      rw [(originalLocalSmithData S).weakEquivalences_eq]
      exact hs
    let _ : WeakEquivalence (S a).hom := (weakEquivalence_iff _).mpr hsLocal
    have h := Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := ihom.adjunction Y) (S a).hom
    have hw : originalLocalEquivalences S (Y ◁ (S a).hom) := by
      have h' := (weakEquivalence_iff _).mp h
      change (originalLocalSmithData S).model.categoryWithWeakEquivalences.weakEquivalences _ at h'
      rwa [(originalLocalSmithData S).weakEquivalences_eq] at h'
    let e : Arrow.mk ((S a).hom ▷ Y) ≅ Arrow.mk (Y ◁ (S a).hom) :=
      Arrow.isoMk (β_ (S a).left Y) (β_ (S a).right Y) (by ext z n x; rfl)
    exact ((originalLocalEquivalences S).arrow_mk_iso_iff e).mpr hw
  · intro hCriterion
    exact originalRepresentableCriterion_closedCartesianModel S hCriterion

/-- The same criterion gives all native Cartesian pushout-product clauses. -/
theorem originalLocalCartesianPP_iff_representableCriterion
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} D) ↔
      ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  constructor
  · intro hpp
    let _ : IsCofibrant (𝟙_ (SimplicialPresheaf.{u} D)) :=
        (originalLocalSmithData S).all_cofibrant _
    have hm := isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
      (SimplicialPresheaf.{u} D)
      (by
        intro A B K L i j hi hj
        exact hpp.1 i j hi hj)
      (by
        intro A B K L i j hi hj
        exact hpp.2.1 i j hi hj)
      (by
        intro A B K L i j hi hj
        exact hpp.2.2 i j hi hj)
    exact (originalLocalCartesianModel_iff_representableCriterion S).mp hm
  · intro hc
    let _ : IsClosedSymmetricMonoidalModelCategory (SimplicialPresheaf.{u} D) :=
      originalRepresentableCriterion_closedCartesianModel S hc
    exact IsClosedSymmetricMonoidalModelCategory.cartesianPushoutProductAxiom

/-- The genuine closed GLOBAL pullback-Hom axiom is the same native criterion. -/
theorem originalLocalCartesianPB_iff_representableCriterion
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
    CartesianPullbackHomAxiom (C := SimplicialPresheaf.{u} D) ↔
      ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  rw [← cartesianPushoutProductAxiom_iff_pullbackHomAxiom]
  exact originalLocalCartesianPP_iff_representableCriterion S

end SimplicialPresheaf.InjectiveKan
