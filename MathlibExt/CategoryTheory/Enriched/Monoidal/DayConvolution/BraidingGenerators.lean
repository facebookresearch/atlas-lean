/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingTensor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadTensorHom
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Generators
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendPoint

/-!
# Original Day generators under index arrows and the genuine braid

The full original enriched coend relation moves an actual index arrow
between the entire Hom weight and the coefficient action. Identity
generators retain the original output maps and the original index braid.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingGenerators

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (F G : EnrichedFunctor V I V)

omit [MonoidalCategory I] [HasColimitsOfSize.{uI, uI} V] in
/-- The coefficient action on two actual arrows is the tensor of the original functor maps. -/
theorem coefficient_unitPoint {a a' b b' : I} (f : a ⟶ a') (g : b ⟶ b') :
    (ρ_ (F.obj a ⊗ G.obj b)).inv ≫
        (F.obj a ⊗ G.obj b) ◁
          AssociatorQuadIndex.unitPair (eHomEquiv V f) (eHomEquiv V g) ≫
        MonoidalClosed.uncurry ((F.externalTensor G).map (a, b) (a', b')) =
      F.toOrdinaryFunctor.map f ⊗ₘ G.toOrdinaryFunctor.map g := by
  let A := F.obj a
  let B := G.obj b
  let H : V := a ⟶[V] a'
  let K : V := b ⟶[V] b'
  let p := eHomEquiv V f
  let q := eHomEquiv V g
  let act : (A ⊗ B) ⊗ (H ⊗ K) ⟶ F.obj a' ⊗ G.obj b' :=
    MonoidalClosed.uncurry ((F.externalTensor G).map (a, b) (a', b'))
  let ins : A ⊗ B ⟶ (A ⊗ B) ⊗ (H ⊗ K) :=
    (ρ_ (A ⊗ B)).inv ≫ (𝟙 (A ⊗ B) ⊗ₘ AssociatorQuadIndex.unitPair p q)
  have hp : (ρ_ A).inv ≫ (𝟙 A ⊗ₘ p) ≫ MonoidalClosed.uncurry (F.map a a') =
      F.toOrdinaryFunctor.map f := by
    rw [F.uncurry_map_point]
    exact Iso.inv_hom_id_assoc (ρ_ A) _
  have hq : (ρ_ B).inv ≫ (𝟙 B ⊗ₘ q) ≫ MonoidalClosed.uncurry (G.map b b') =
      G.toOrdinaryFunctor.map g := by
    rw [G.uncurry_map_point]
    exact Iso.inv_hom_id_assoc (ρ_ B) _
  have hu : ins ≫ tensorμ A B H K =
      ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ p)) ⊗ₘ ((ρ_ B).inv ≫ (𝟙 B ⊗ₘ q)) := by
    simpa only [ins, Category.assoc] using AssociatorQuadIndex.unitPair_post p q A B
  have ha : act = tensorμ A B H K ≫
      (MonoidalClosed.uncurry (F.map a a') ⊗ₘ MonoidalClosed.uncurry (G.map b b')) :=
    EnrichedFunctor.externalTensor_uncurry F G (a, b) (a', b')
  have h : ins ≫ act = F.toOrdinaryFunctor.map f ⊗ₘ G.toOrdinaryFunctor.map g := by
    calc
      _ = ins ≫ tensorμ A B H K ≫
        (MonoidalClosed.uncurry (F.map a a') ⊗ₘ MonoidalClosed.uncurry (G.map b b')) :=
        congrArg (fun x => ins ≫ x) ha
      _ = (((ρ_ A).inv ≫ (𝟙 A ⊗ₘ p)) ⊗ₘ ((ρ_ B).inv ≫ (𝟙 B ⊗ₘ q))) ≫
        (MonoidalClosed.uncurry (F.map a a') ⊗ₘ MonoidalClosed.uncurry (G.map b b')) := by
        simpa only [Category.assoc] using congrArg
          (fun x => x ≫
            (MonoidalClosed.uncurry (F.map a a') ⊗ₘ MonoidalClosed.uncurry (G.map b b'))) hu
      _ = _ := by
        rw [tensorHom_comp_tensorHom]
        have hp' := (Category.assoc (ρ_ A).inv (𝟙 A ⊗ₘ p)
          (MonoidalClosed.uncurry (F.map a a'))).trans hp
        have hq' := (Category.assoc (ρ_ B).inv (𝟙 B ⊗ₘ q)
          (MonoidalClosed.uncurry (G.map b b'))).trans hq
        exact congrArg₂ (fun x y => x ⊗ₘ y) hp' hq'
  simp only [ins, act, A, B, p, q, id_tensorHom, Category.assoc] at h
  exact h

omit [HasColimitsOfSize.{uI, uI} V] in
/-- The weight action on two actual arrows is full precomposition by their original tensor. -/
theorem weight_unitPoint (k : I) {a a' b b' : I} (f : a ⟶ a') (g : b ⟶ b') :
    (ρ_ ((a' ⊗ b') ⟶[V] k)).inv ≫
        ((a' ⊗ b') ⟶[V] k) ◁
          AssociatorQuadIndex.unitPair (eHomEquiv V f) (eHomEquiv V g) ≫
        MonoidalClosed.uncurry
          ((weight d.tensorEnrichedFunctor k).map (op (a', b')) (op (a, b))) =
      eHomWhiskerRight V (f ⊗ₘ g) k := by
  let W : V := (a' ⊗ b') ⟶[V] k
  let H : V := (a ⊗ b) ⟶[V] (a' ⊗ b')
  let p : 𝟙_ V ⟶ H := eHomEquiv V (f ⊗ₘ g)
  let pair := AssociatorQuadIndex.unitPair (eHomEquiv V f) (eHomEquiv V g)
  let ins := (ρ_ W).inv ≫ W ◁ pair
  let act : W ⊗ ((a ⟶[V] a') ⊗ (b ⟶[V] b')) ⟶ (a ⊗ b) ⟶[V] k :=
    MonoidalClosed.uncurry
      ((weight d.tensorEnrichedFunctor k).map (op (a', b')) (op (a, b)))
  have he : AssociatorQuadIndex.unitPair (eHomEquiv V f) (eHomEquiv V g) ≫
      d.tensorEnrichedFunctor.map (a, b) (a', b') = p := by
    simpa only [AssociatorQuadIndex.unitPair,
      EnrichedMonoidalCategoryData.tensorEnrichedFunctor, Category.assoc] using
      d.tensorMap_eHomEquiv f g
  have ha : act = W ◁ d.tensorEnrichedFunctor.map (a, b) (a', b') ≫
      (β_ W H).hom ≫ eComp V (a ⊗ b) (a' ⊗ b') k :=
    weight_uncurry_map d.tensorEnrichedFunctor k (a, b) (a', b')
  have h : ins ≫ act = eHomWhiskerRight V (f ⊗ₘ g) k := by
    calc
      _ = ins ≫ W ◁ d.tensorEnrichedFunctor.map (a, b) (a', b') ≫
        (β_ W H).hom ≫ eComp V (a ⊗ b) (a' ⊗ b') k :=
        congrArg (fun x => ins ≫ x) ha
      _ = (ρ_ W).inv ≫ (𝟙 W ⊗ₘ p) ≫ (β_ W H).hom ≫
        eComp V (a ⊗ b) (a' ⊗ b') k := by
        simp only [ins, Category.assoc, ← whiskerLeft_comp_assoc]
        rw [he]
        exact congrArg (fun x => (ρ_ W).inv ≫ x ≫
          (β_ W H).hom ≫ eComp V (a ⊗ b) (a' ⊗ b') k) (id_tensorHom W p).symm
      _ = _ := by
        rw [braiding_naturality_assoc, braiding_tensorUnit_right]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        simp only [eHomWhiskerRight, tensorHom_id, W, p]
  simp only [ins, act, pair, Category.assoc] at h
  exact h

/-- The entire original coend relation moves an index tensor arrow into coefficient actions. -/
@[reassoc]
theorem gen_input (k : I) {a a' b b' : I} (f : a ⟶ a') (g : b ⟶ b') :
    (eHomWhiskerRight V (f ⊗ₘ g) k ⊗ₘ 𝟙 (F.obj a ⊗ G.obj b)) ≫
        gen d.tensorEnrichedFunctor F G k (a, b) =
      (𝟙 ((a' ⊗ b') ⟶[V] k) ⊗ₘ
        (F.toOrdinaryFunctor.map f ⊗ₘ G.toOrdinaryFunctor.map g)) ≫
        gen d.tensorEnrichedFunctor F G k (a', b') := by
  have h := Enriched.weightedCoend.condition_unitPoint
    (weight d.tensorEnrichedFunctor k) (F.externalTensor G) (a, b) (a', b')
    (AssociatorQuadIndex.unitPair (eHomEquiv V f) (eHomEquiv V g))
  let W := (weight d.tensorEnrichedFunctor k).obj (op (a', b'))
  let Q := (F.externalTensor G).obj (a, b)
  let p := AssociatorQuadIndex.unitPair (eHomEquiv V f) (eHomEquiv V g)
  let wa : W ⟶ (a ⊗ b) ⟶[V] k := (ρ_ W).inv ≫ W ◁ p ≫
    MonoidalClosed.uncurry
      ((weight d.tensorEnrichedFunctor k).map (op (a', b')) (op (a, b)))
  let qa : Q ⟶ F.obj a' ⊗ G.obj b' := (ρ_ Q).inv ≫ Q ◁ p ≫
    MonoidalClosed.uncurry ((F.externalTensor G).map (a, b) (a', b'))
  have hw : wa = eHomWhiskerRight V (f ⊗ₘ g) k := weight_unitPoint d k f g
  have hq : qa = F.toOrdinaryFunctor.map f ⊗ₘ G.toOrdinaryFunctor.map g :=
    coefficient_unitPoint F G f g
  change (wa ⊗ₘ 𝟙 Q) ≫ gen d.tensorEnrichedFunctor F G k (a, b) =
    (𝟙 W ⊗ₘ qa) ≫ gen d.tensorEnrichedFunctor F G k (a', b') at h
  rw [hw, hq] at h
  exact h

/-- The full output action on an identity generator at an actual arrow recovers its labelled map. -/
@[reassoc]
theorem unitGenerator_map (a : I × I) {k : I} (f : d.tensorEnrichedFunctor.obj a ⟶ k) :
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G a ≫
        (Output.functor d.tensorEnrichedFunctor F G).toOrdinaryFunctor.map f =
      (λ_ (F.obj a.1 ⊗ G.obj a.2)).inv ≫
        (eHomEquiv V f ⊗ₘ 𝟙 (F.obj a.1 ⊗ G.obj a.2)) ≫
        gen d.tensorEnrichedFunctor F G k a := by
  let Q := (F.externalTensor G).obj a
  let S := Output.functor d.tensorEnrichedFunctor F G
  let E := S.obj (d.tensorEnrichedFunctor.obj a)
  let p : Q ⟶ E := Generators.point d.tensorEnrichedFunctor F G a
  have hp : p = AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G a :=
    (Category.assoc (λ_ Q).inv (eId V (a.1 ⊗ a.2) ⊗ₘ 𝟙 Q)
      (gen d.tensorEnrichedFunctor F G (a.1 ⊗ a.2) a)).symm
  have h := congrArg (fun t => (ρ_ Q).inv ≫ t)
    (Generators.point_output d.tensorEnrichedFunctor F G a k (eHomEquiv V f))
  have hb : (β_ (𝟙_ V) Q).inv = (ρ_ Q).hom ≫ (λ_ Q).inv :=
    (SymmetricCategory.braiding_swap_eq_inv_braiding (𝟙_ V) Q).symm.trans
      (braiding_tensorUnit_right Q)
  change (ρ_ Q).inv ≫ (p ⊗ₘ 𝟙 (𝟙_ V)) ≫ E ◁ eHomEquiv V f ≫
      MonoidalClosed.uncurry (S.map (d.tensorEnrichedFunctor.obj a) k) =
      (ρ_ Q).inv ≫ (β_ (𝟙_ V) Q).inv ≫
        (eHomEquiv V f ⊗ₘ 𝟙 Q) ≫ gen d.tensorEnrichedFunctor F G k a at h
  have ha : E ◁ eHomEquiv V f ≫
      MonoidalClosed.uncurry (S.map (d.tensorEnrichedFunctor.obj a) k) =
      (ρ_ E).hom ≫ S.toOrdinaryFunctor.map f := by
    have h' := S.uncurry_map_point f
    simp only [id_tensorHom] at h'
    exact h'
  have hn : p ▷ 𝟙_ V ≫ (ρ_ E).hom = (ρ_ Q).hom ≫ p := rightUnitor_naturality p
  let o : E ⟶ S.obj k := S.toOrdinaryFunctor.map f
  let r : 𝟙_ V ⟶ (d.tensorEnrichedFunctor.obj a ⟶[V] k) := eHomEquiv V f
  let γ : (d.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ Q ⟶ S.obj k :=
    gen d.tensorEnrichedFunctor F G k a
  rw [ha, tensorHom_id] at h
  change (ρ_ Q).inv ≫ p ▷ 𝟙_ V ≫ (ρ_ E).hom ≫ o =
    (ρ_ Q).inv ≫ (β_ (𝟙_ V) Q).inv ≫ (r ⊗ₘ 𝟙 Q) ≫ γ at h
  have hl : (ρ_ Q).inv ≫ p ▷ 𝟙_ V ≫ (ρ_ E).hom ≫ o = p ≫ o := by
    calc
      _ = (ρ_ Q).inv ≫ (p ▷ 𝟙_ V ≫ (ρ_ E).hom) ≫ o := by
        simp only [Category.assoc]
      _ = (ρ_ Q).inv ≫ ((ρ_ Q).hom ≫ p) ≫ o :=
        congrArg (fun t => (ρ_ Q).inv ≫ t ≫ o) hn
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hr : (ρ_ Q).inv ≫ (β_ (𝟙_ V) Q).inv ≫ (r ⊗ₘ 𝟙 Q) ≫ γ =
      (λ_ Q).inv ≫ (r ⊗ₘ 𝟙 Q) ≫ γ := by
    rw [hb]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h' := hl.symm.trans (h.trans hr)
  rw [hp] at h'
  exact h'

variable [SymmetricCategory I] (b : EnrichedBraidedMonoidalCategoryData V I d)

/-- The actual identity generator braid retains the original inverse index braid as output map. -/
@[reassoc]
theorem unitGenerator_braid (a : I × I) :
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G a ≫
        BraidingComponents.component d b F G (a.1 ⊗ a.2) =
      (β_ (F.obj a.1) (G.obj a.2)).hom ≫
        AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G F (a.2, a.1) ≫
        (Output.functor d.tensorEnrichedFunctor G F).toOrdinaryFunctor.map
          (β_ a.1 a.2).inv := by
  let Q := F.obj a.1 ⊗ G.obj a.2
  let R := G.obj a.2 ⊗ F.obj a.1
  let w := eHomWhiskerRight V (β_ a.1 a.2).inv (a.1 ⊗ a.2)
  let c : Q ⟶ R := (β_ (F.obj a.1) (G.obj a.2)).hom
  let p := eHomEquiv V (β_ a.1 a.2).inv
  have he : eId V (a.1 ⊗ a.2) ≫ w = p :=
    eId_comp_eHomWhiskerRight V I (β_ a.1 a.2).inv
  have hw : AssociatorUnit.identityInsert (a.1 ⊗ a.2) Q ≫ (w ⊗ₘ c) =
      c ≫ (λ_ R).inv ≫ (p ⊗ₘ 𝟙 R) := by
    simp only [AssociatorUnit.identityInsert, Category.assoc]
    rw [tensorHom_comp_tensorHom, he, Category.id_comp]
    simpa only [tensorHom_id] using leftUnitor_inv_comp_tensorHom p c
  let ins := AssociatorUnit.identityInsert (a.1 ⊗ a.2) Q
  let γ : ((a.1 ⊗ a.2) ⟶[V] a.1 ⊗ a.2) ⊗ Q ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor F G (a.1 ⊗ a.2) :=
    gen d.tensorEnrichedFunctor F G (a.1 ⊗ a.2) a
  let δ : ((a.2 ⊗ a.1) ⟶[V] a.1 ⊗ a.2) ⊗ R ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor G F (a.1 ⊗ a.2) :=
    gen d.tensorEnrichedFunctor G F (a.1 ⊗ a.2) (a.2, a.1)
  let t := BraidingComponents.component d b F G (a.1 ⊗ a.2)
  have hg : γ ≫ t = (w ⊗ₘ c) ≫ δ := BraidingComponents.gen_component d b F G _ a
  change (ins ≫ γ) ≫ t = _
  calc
    _ = ins ≫ (w ⊗ₘ c) ≫ δ := (Category.assoc ins γ t).trans
      (congrArg (fun x => ins ≫ x) hg)
    _ = c ≫ (λ_ R).inv ≫ (p ⊗ₘ 𝟙 R) ≫ δ := by
      simpa only [ins, AssociatorUnit.identityInsert, Category.assoc] using
        congrArg (fun x => x ≫ δ) hw
    _ = _ := by
      have hm := congrArg (fun x => c ≫ x)
        (unitGenerator_map d G F (a.2, a.1) (β_ a.1 a.2).inv).symm
      simp only [c, R] at hm
      exact hm

end CategoryTheory.EnrichedDayKernel.BraidingGenerators
