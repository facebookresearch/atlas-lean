/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalTestingProducts
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingSaturation
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization

/-!
# Actual finite-interval testing product corners

The chosen native pushout-product of two monomorphisms is a monic testing
 equivalence when either input is. The proof uses product testing, actual
cobase stability and both pushout legs, before model construction.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u
namespace SSet.joyalInterval

/-- The full product-corner condition for the actual testing left class,
with either weak input and both original monomorphisms. -/
theorem testingTrivialCofibrations_pushoutProduct
    {A B C D : SSet.{u}} (i : A ⟶ B) (j : C ⟶ D) [Mono i] [Mono j]
    (hw : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i ∨
      productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions j) :
    productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions
      (Arrow.mk i □ Arrow.mk j).hom := by
  let W : MorphismProperty SSet.{u} :=
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
  let T : MorphismProperty SSet.{u} :=
    productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions
  let : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions
      auxiliaryAnodyneExtensions.rlp := by
    change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions auxiliaryNaiveFibrations
    infer_instance
  have leftCase : ∀ {P Q R S : SSet.{u}} (f : P ⟶ Q) (g : R ⟶ S)
      [Mono f] [Mono g], W f → T (Arrow.mk f □ Arrow.mk g).hom := by
    intro P Q R S f g hf hg hWf
    let : Mono f := hf
    let : Mono g := hg
    let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) f g
    change T sq.ι
    have : Mono (f ▷ R) := by
      constructor
      intro X a b h
      apply CartesianMonoidalCategory.hom_ext
      · apply (cancel_mono f).1
        simpa only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst] using
          congrArg (fun k ↦ k ≫ CartesianMonoidalCategory.fst Q R) h
      · simpa only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd] using
          congrArg (fun k ↦ k ≫ CartesianMonoidalCategory.snd Q R) h
    have hTR : T (f ▷ R) :=
      (productPrecylinder.testingTrivialCofibrations_iff auxiliaryAnodyneExtensions _).mpr
        ⟨inferInstance, testingEquivalences_whiskerRight R f hWf⟩
    have hTinr : T sq.inr := T.of_isPushout sq.isPushout.flip hTR
    have hWcomp : W (sq.inr ≫ sq.ι) := by
      rw [sq.inr_ι]
      exact testingEquivalences_whiskerRight S f hWf
    have hMono : Mono sq.ι := by
      change Mono (Arrow.mk f □ Arrow.mk g).hom
      exact (SSet.monomorphism_product_corner f g).1
    refine (productPrecylinder.testingTrivialCofibrations_iff
      auxiliaryAnodyneExtensions sq.ι).mpr ⟨hMono, ?_⟩
    exact W.of_precomp sq.inr sq.ι
      ((productPrecylinder.testingTrivialCofibrations_iff
        auxiliaryAnodyneExtensions sq.inr).mp hTinr).2 hWcomp
  rcases hw with hi | hj
  · exact leftCase i j hi
  · exact (T.arrow_iso_iff
      (MonoidalCategory.Arrow.PushoutProduct.braiding (Arrow.mk i) (Arrow.mk j))).mpr
        (leftCase j i hj)

end SSet.joyalInterval
