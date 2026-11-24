/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingFunctor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidAssembly

/-!
# Original braided tensorators descend to invariant full Day multiplication

On every whole generator, the original inverse index braid and coefficient
braid intertwine the original tensorator and the complete output action.
The source braided law is used on its original enriched functor. No target
monoid or target braiding instance is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LaxMonoid

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

include B in
/-- Every complete coend generator intertwines the original braid and descended multiplication. -/
@[reassoc]
theorem gen_multiply_braid (k : I) (a : I × I) :
    gen d.tensorEnrichedFunctor S S k a ≫
        BraidingComponents.component d b S S k ≫
        EnrichedFunctorCat.component (multiply d S L) k =
      gen d.tensorEnrichedFunctor S S k a ≫
        EnrichedFunctorCat.component (multiply d S L) k := by
  let x := a.1 ⊗ a.2
  let y := a.2 ⊗ a.1
  let H : V := x ⟶[V] k
  let K : V := y ⟶[V] k
  let Q := S.obj a.1 ⊗ S.obj a.2
  let R := S.obj a.2 ⊗ S.obj a.1
  let γ : H ⊗ Q ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k :=
    gen d.tensorEnrichedFunctor S S k a
  let δ : K ⊗ R ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k :=
    gen d.tensorEnrichedFunctor S S k (a.2, a.1)
  let t := BraidingComponents.component d b S S k
  let m := EnrichedFunctorCat.component (multiply d S L) k
  let w : H ⟶ K := eHomWhiskerRight V (β_ a.1 a.2).inv k
  let v : Q ⟶ R := (β_ (S.obj a.1) (S.obj a.2)).hom
  let p : Q ⟶ S.obj x := L.mu a.1 a.2
  let q : R ⟶ S.obj y := L.mu a.2 a.1
  let o : S.obj x ⟶ S.obj y := S.toOrdinaryFunctor.map (β_ a.1 a.2).hom
  let z : H ⊗ S.obj x ⟶ S.obj k := ActionFromTransformation.targetAction S x k
  let z' : K ⊗ S.obj y ⟶ S.obj k := ActionFromTransformation.targetAction S y k
  have hγ : γ ≫ t = (w ⊗ₘ v) ≫ δ := BraidingComponents.gen_component d b S S k a
  have hδ : δ ≫ m = (𝟙 K ⊗ₘ q) ≫ z' := gen_multiply d S L k (a.2, a.1)
  have hm : γ ≫ m = (𝟙 H ⊗ₘ p) ≫ z := gen_multiply d S L k a
  have hb : p ≫ o = v ≫ q := B.braided a.1 a.2
  have hs : (𝟙 H ⊗ₘ p) ≫ z =
      ((𝟙 H ≫ w) ⊗ₘ (p ≫ o)) ≫ z' :=
    targetAction_sourceIso S (β_ a.1 a.2) k p (𝟙 H)
  have ht : (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ q) = w ⊗ₘ (v ≫ q) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have h : (𝟙 H ⊗ₘ p) ≫ z = (w ⊗ₘ (v ≫ q)) ≫ z' := by
    calc
      _ = ((𝟙 H ≫ w) ⊗ₘ (p ≫ o)) ≫ z' := hs
      _ = (w ⊗ₘ (p ≫ o)) ≫ z' :=
        congrArg (fun u => (u ⊗ₘ (p ≫ o)) ≫ z') (Category.id_comp w)
      _ = _ := congrArg (fun u => (w ⊗ₘ u) ≫ z') hb
  change γ ≫ t ≫ m = γ ≫ m
  calc
    _ = (w ⊗ₘ v) ≫ δ ≫ m := by
      simpa only [Category.assoc] using congrArg (fun u => u ≫ m) hγ
    _ = (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ q) ≫ z' := congrArg (fun u => (w ⊗ₘ v) ≫ u) hδ
    _ = (w ⊗ₘ (v ≫ q)) ≫ z' := by
      simpa only [Category.assoc] using congrArg (fun u => u ≫ z') ht
    _ = (𝟙 H ⊗ₘ p) ≫ z := h.symm
    _ = _ := hm.symm

include B in
/-- The whole original coend braid preserves the whole descended original multiplication. -/
theorem multiply_braid :
    (BraidingFunctor.functorIso d b S S).hom ≫ multiply d S L = multiply d S L := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  rw [EnrichedFunctorCat.component_comp, BraidingFunctor.functorIso_hom_component]
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor S S k
  exact gen_multiply_braid d b S L B k

end CategoryTheory.EnrichedDayKernel.LaxMonoid
