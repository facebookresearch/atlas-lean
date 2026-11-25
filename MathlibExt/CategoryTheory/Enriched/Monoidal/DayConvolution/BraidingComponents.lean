/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingWeights
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingCoefficients
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ColimitMonoidal

/-!
# Genuine continuous Day braiding components

The original index braid and value braid descend through both complete
enriched coend relation faces. The tensor objects and input maps are the
unchanged original Day construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingComponents

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (F G : EnrichedFunctor V I V) (k : I)

/-- Descend the actual index and coefficient braids through the full original Day coend. -/
@[no_expose]
def component : EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k ⟶
    EnrichedDayKernel.obj d.tensorEnrichedFunctor G F k :=
  Enriched.weightedCoend.Transport.map (BraidingIndex.swap (V := V))
    (weight d.tensorEnrichedFunctor k) (weight d.tensorEnrichedFunctor k)
    (F.externalTensor G) (G.externalTensor F)
    (fun X => (BraidingWeights.weightIso d k X).hom)
    (fun X => (β_ (F.obj X.1) (G.obj X.2)).hom)
    (BraidingWeights.transport_weight_naturality d b k)
    (BraidingCoefficients.naturality F G)

/-- Each entire original generator maps by the original inverse index braid and value braid. -/
@[reassoc]
theorem gen_component (X : I × I) :
    gen d.tensorEnrichedFunctor F G k X ≫ component d b F G k =
      (eHomWhiskerRight V (β_ X.1 X.2).inv k ⊗ₘ (β_ (F.obj X.1) (G.obj X.2)).hom) ≫
        gen d.tensorEnrichedFunctor G F k (X.2, X.1) := by
  have h := Enriched.weightedCoend.Transport.ι_map (BraidingIndex.swap (V := V))
    (weight d.tensorEnrichedFunctor k) (weight d.tensorEnrichedFunctor k)
    (F.externalTensor G) (G.externalTensor F)
    (fun X => (BraidingWeights.weightIso d k X).hom)
    (fun X => (β_ (F.obj X.1) (G.obj X.2)).hom)
    (BraidingWeights.transport_weight_naturality d b k)
    (BraidingCoefficients.naturality F G) X
  exact h.trans (congrArg (fun w => (w ⊗ₘ (β_ (F.obj X.1) (G.obj X.2)).hom) ≫
    gen d.tensorEnrichedFunctor G F k (X.2, X.1)) (BraidingWeights.weightIso_hom d k X))

/-- The descended braiding retains the full original enriched balancing law on every generator. -/
theorem generator_balanced :
    Balanced d.tensorEnrichedFunctor F G k
      (fun X => gen d.tensorEnrichedFunctor F G k X ≫ component d b F G k) := by
  intro X Y
  have h := congrArg (fun t => t ≫ component d b F G k)
    (gen_balanced d.tensorEnrichedFunctor F G k X Y)
  simpa only [Category.assoc] using h

/-- The two actual coend braiding components compose to the whole original identity map. -/
theorem component_symmetry :
    component d b F G k ≫ component d b G F k =
      𝟙 (EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k) := by
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor F G k
  rintro ⟨p, q⟩
  let H : V := (p ⊗ q) ⟶[V] k
  let K : V := (q ⊗ p) ⟶[V] k
  let Q : V := F.obj p ⊗ G.obj q
  let R : V := G.obj q ⊗ F.obj p
  let A : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k
  let B : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor G F k
  let γ : H ⊗ Q ⟶ A := gen d.tensorEnrichedFunctor F G k (p, q)
  let δ : K ⊗ R ⟶ B := gen d.tensorEnrichedFunctor G F k (q, p)
  let c : A ⟶ B := component d b F G k
  let c' : B ⟶ A := component d b G F k
  let w : H ⟶ K := eHomWhiskerRight V (β_ p q).inv k
  let w' : K ⟶ H := eHomWhiskerRight V (β_ q p).inv k
  let v : Q ⟶ R := (β_ (F.obj p) (G.obj q)).hom
  let v' : R ⟶ Q := (β_ (G.obj q) (F.obj p)).hom
  have hγ : γ ≫ c = (w ⊗ₘ v) ≫ δ := gen_component d b F G k (p, q)
  have hδ : δ ≫ c' = (w' ⊗ₘ v') ≫ γ := gen_component d b G F k (q, p)
  have he : (β_ q p).inv = (β_ p q).hom :=
    (SymmetricCategory.braiding_swap_eq_inv_braiding q p).symm
  have hw' : w' = eHomWhiskerRight V (β_ p q).hom k :=
    congrArg (fun f => eHomWhiskerRight V f k) he
  have hw : w ≫ w' = 𝟙 H :=
    (congrArg (fun f => w ≫ f) hw').trans
      (eHomWhiskerRightIso V I (β_ p q) (Y := k)).inv_hom_id
  have hv : v ≫ v' = 𝟙 Q := SymmetricCategory.symmetry (F.obj p) (G.obj q)
  have ht : (w ⊗ₘ v) ≫ (w' ⊗ₘ v') = 𝟙 (H ⊗ Q) := by
    rw [tensorHom_comp_tensorHom, hw, hv, id_tensorHom_id]
  change γ ≫ c ≫ c' = γ ≫ 𝟙 A
  calc
    _ = (w ⊗ₘ v) ≫ δ ≫ c' := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ c') hγ
    _ = (w ⊗ₘ v) ≫ (w' ⊗ₘ v') ≫ γ :=
      congrArg (fun t => (w ⊗ₘ v) ≫ t) hδ
    _ = 𝟙 (H ⊗ Q) ≫ γ := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ γ) ht
    _ = _ := by rw [Category.id_comp, Category.comp_id]

/-- The actual inverse component is the same original braid with the two inputs reversed. -/
def componentIso : EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k ≅
    EnrichedDayKernel.obj d.tensorEnrichedFunctor G F k where
  hom := component d b F G k
  inv := component d b G F k
  hom_inv_id := component_symmetry d b F G k
  inv_hom_id := component_symmetry d b G F k

end CategoryTheory.EnrichedDayKernel.BraidingComponents
