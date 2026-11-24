/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingGenerators

/-!
# Actual braid paths on the full original Day triple generators

Each path retains the whole output Hom and the ordered triple of coefficient
objects. Outer braids use the full coend braid. Inner braids move their actual
index output arrows through the original enriched coend relation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingTriple

section TensorTransfer
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- Tensor functoriality transports every coefficient along a proved whole weight relation. -/
theorem coefficient_transfer {W W' Q D D' Z : V}
    (w : W ⟶ W') (c : Q ⟶ D) (o : D ⟶ D')
    (g : W ⊗ D' ⟶ Z) (g' : W' ⊗ D ⟶ Z)
    (h : (w ⊗ₘ 𝟙 D) ≫ g' = (𝟙 W ⊗ₘ o) ≫ g) :
    (𝟙 W ⊗ₘ (c ≫ o)) ≫ g = (w ⊗ₘ c) ≫ g' := by
  have hc : (𝟙 W ⊗ₘ c) ≫ (𝟙 W ⊗ₘ o) = 𝟙 W ⊗ₘ (c ≫ o) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hw : (𝟙 W ⊗ₘ c) ≫ (w ⊗ₘ 𝟙 D) = w ⊗ₘ c := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  calc
    _ = (𝟙 W ⊗ₘ c) ≫ (𝟙 W ⊗ₘ o) ≫ g := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ g) hc.symm
    _ = (𝟙 W ⊗ₘ c) ≫ (w ⊗ₘ 𝟙 D) ≫ g' :=
      congrArg (fun t => (𝟙 W ⊗ₘ c) ≫ t) h.symm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun t => t ≫ g') hw

end TensorTransfer

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (F G H : EnrichedFunctor V I V) (k : I) (a c e : I)

/-- The full original left flat summand included into the original left nested Day value. -/
abbrev leftAt :
    ((((a ⊗ c) ⊗ e) ⟶[V] k) ⊗ ((F.obj a ⊗ G.obj c) ⊗ H.obj e)) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F G) H k :=
  AssociatorFlat.leftGenerator d F G H k ((a, c), e) ≫
    AssociatorFlattening.flatToNested d F G H k

/-- The full original right flat summand included into the original right nested Day value. -/
abbrev rightAt :
    (((a ⊗ (c ⊗ e)) ⟶[V] k) ⊗ (F.obj a ⊗ (G.obj c ⊗ H.obj e))) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor
        F (Output.functor d.tensorEnrichedFunctor G H) k :=
  AssociatorFlat.rightGenerator d F G H k ((a, c), e) ≫
    AssociatorRightFlattening.flatToNested d F G H k

/-- The complete first block swaps with the third input by the actual inverse index braid. -/
@[reassoc]
theorem outer_left :
    leftAt d F G H k a c e ≫
        BraidingComponents.component d b (Output.functor d.tensorEnrichedFunctor F G) H k =
      (eHomWhiskerRight V (β_ (a ⊗ c) e).inv k ⊗ₘ
        (β_ (F.obj a ⊗ G.obj c) (H.obj e)).hom) ≫
        rightAt d H F G k e a c := by
  let Q := F.obj a ⊗ G.obj c
  let C := H.obj e
  let D := EnrichedDayKernel.obj d.tensorEnrichedFunctor F G (a ⊗ c)
  let W : V := ((a ⊗ c) ⊗ e) ⟶[V] k
  let W' : V := (e ⊗ (a ⊗ c)) ⟶[V] k
  let u : Q ⟶ D := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G (a, c)
  let v : Q ⊗ C ⟶ C ⊗ Q := (β_ Q C).hom
  let t : D ⊗ C ⟶ C ⊗ D := (β_ D C).hom
  let w : W ⟶ W' := eHomWhiskerRight V (β_ (a ⊗ c) e).inv k
  let γ : W ⊗ (D ⊗ C) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
        H k := gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H k
          (a ⊗ c, e)
  let δ : W' ⊗ (C ⊗ D) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor H (Output.functor d.tensorEnrichedFunctor F G)
        k := gen d.tensorEnrichedFunctor H (Output.functor d.tensorEnrichedFunctor F G) k
          (e, a ⊗ c)
  let z := BraidingComponents.component d b (Output.functor d.tensorEnrichedFunctor F G) H k
  let ins := 𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)
  let ins' := 𝟙 W' ⊗ₘ (𝟙 C ⊗ₘ u)
  have hl : leftAt d F G H k a c e = ins ≫ γ :=
    AssociatorFlattening.leftGenerator_flatToNested d F G H k ((a, c), e)
  have hr : rightAt d H F G k e a c = ins' ≫ δ :=
    AssociatorRightFlattening.rightGenerator_flatToNested d H F G k ((e, a), c)
  have hz : γ ≫ z = (w ⊗ₘ t) ≫ δ :=
    BraidingComponents.gen_component d b (Output.functor d.tensorEnrichedFunctor F G) H k
      (a ⊗ c, e)
  have hv : (u ⊗ₘ 𝟙 C) ≫ t = v ≫ (𝟙 C ⊗ₘ u) := braiding_naturality u (𝟙 C)
  have hw : ins ≫ (w ⊗ₘ t) = (w ⊗ₘ v) ≫ ins' := by
    simp only [ins, ins', tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg (fun x => w ⊗ₘ x) hv
  change leftAt d F G H k a c e ≫ z = (w ⊗ₘ v) ≫ rightAt d H F G k e a c
  calc
    _ = ins ≫ (w ⊗ₘ t) ≫ δ :=
      (congrArg (fun x => x ≫ z) hl).trans
        ((Category.assoc ins γ z).trans (congrArg (fun x => ins ≫ x) hz))
    _ = (w ⊗ₘ v) ≫ ins' ≫ δ := by
      simpa only [Category.assoc] using congrArg (fun x => x ≫ δ) hw
    _ = _ := congrArg (fun x => (w ⊗ₘ v) ≫ x) hr.symm

/-- Swapping the first input with the complete last block retains the actual inverse index braid. -/
@[reassoc]
theorem outer_right :
    rightAt d F G H k a c e ≫
        BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k =
      (eHomWhiskerRight V (β_ a (c ⊗ e)).inv k ⊗ₘ
        (β_ (F.obj a) (G.obj c ⊗ H.obj e)).hom) ≫
        leftAt d G H F k c e a := by
  let A := F.obj a
  let Q := G.obj c ⊗ H.obj e
  let D := EnrichedDayKernel.obj d.tensorEnrichedFunctor G H (c ⊗ e)
  let W : V := (a ⊗ (c ⊗ e)) ⟶[V] k
  let W' : V := ((c ⊗ e) ⊗ a) ⟶[V] k
  let u : Q ⟶ D := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (c, e)
  let v : A ⊗ Q ⟶ Q ⊗ A := (β_ A Q).hom
  let t : A ⊗ D ⟶ D ⊗ A := (β_ A D).hom
  let w : W ⟶ W' := eHomWhiskerRight V (β_ a (c ⊗ e)).inv k
  let γ : W ⊗ (A ⊗ D) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
        k := gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) k
          (a, c ⊗ e)
  let δ : W' ⊗ (D ⊗ A) ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor G H)
        F k := gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor G H) F k
          (c ⊗ e, a)
  let z := BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k
  let ins := 𝟙 W ⊗ₘ (𝟙 A ⊗ₘ u)
  let ins' := 𝟙 W' ⊗ₘ (u ⊗ₘ 𝟙 A)
  have hl : rightAt d F G H k a c e = ins ≫ γ :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F G H k ((a, c), e)
  have hr : leftAt d G H F k c e a = ins' ≫ δ :=
    AssociatorFlattening.leftGenerator_flatToNested d G H F k ((c, e), a)
  have hz : γ ≫ z = (w ⊗ₘ t) ≫ δ :=
    BraidingComponents.gen_component d b F (Output.functor d.tensorEnrichedFunctor G H) k
      (a, c ⊗ e)
  have hv : (𝟙 A ⊗ₘ u) ≫ t = v ≫ (u ⊗ₘ 𝟙 A) := braiding_naturality (𝟙 A) u
  have hw : ins ≫ (w ⊗ₘ t) = (w ⊗ₘ v) ≫ ins' := by
    simp only [ins, ins', tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg (fun x => w ⊗ₘ x) hv
  change rightAt d F G H k a c e ≫ z = (w ⊗ₘ v) ≫ leftAt d G H F k c e a
  calc
    _ = ins ≫ (w ⊗ₘ t) ≫ δ :=
      (congrArg (fun x => x ≫ z) hl).trans
        ((Category.assoc ins γ z).trans (congrArg (fun x => ins ≫ x) hz))
    _ = (w ⊗ₘ v) ≫ ins' ≫ δ := by
      simpa only [Category.assoc] using congrArg (fun x => x ≫ δ) hw
    _ = _ := congrArg (fun x => (w ⊗ₘ v) ≫ x) hr.symm

/-- The complete left inner braid keeps all three coefficient objects and the whole output Hom. -/
@[reassoc]
theorem inner_left :
    leftAt d F G H k a c e ≫ Input.mapAt d.tensorEnrichedFunctor
        (BraidingFunctor.functorIso d b F G).hom (GradedNatTrans.unitId H) k =
      (eHomWhiskerRight V ((β_ a c).inv ▷ e) k ⊗ₘ
        ((β_ (F.obj a) (G.obj c)).hom ⊗ₘ 𝟙 (H.obj e))) ≫
        leftAt d G F H k c a e := by
  let P := F.obj a ⊗ G.obj c
  let P' := G.obj c ⊗ F.obj a
  let C := H.obj e
  let FG := Output.functor d.tensorEnrichedFunctor F G
  let GF := Output.functor d.tensorEnrichedFunctor G F
  let D := FG.obj (a ⊗ c)
  let D' := GF.obj (c ⊗ a)
  let D₁ := GF.obj (a ⊗ c)
  let W : V := ((a ⊗ c) ⊗ e) ⟶[V] k
  let W' : V := ((c ⊗ a) ⊗ e) ⟶[V] k
  let u : P ⟶ D := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G (a, c)
  let u' : P' ⟶ D' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G F (c, a)
  let v : P ⟶ P' := (β_ (F.obj a) (G.obj c)).hom
  let t : D ⟶ D₁ := BraidingComponents.component d b F G (a ⊗ c)
  let o : D' ⟶ D₁ := GF.toOrdinaryFunctor.map (β_ a c).inv
  let w : W ⟶ W' := eHomWhiskerRight V ((β_ a c).inv ▷ e) k
  let γ : W ⊗ (D ⊗ C) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor FG H k :=
    gen d.tensorEnrichedFunctor FG H k (a ⊗ c, e)
  let δ : W ⊗ (D₁ ⊗ C) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor GF H k :=
    gen d.tensorEnrichedFunctor GF H k (a ⊗ c, e)
  let δ' : W' ⊗ (D' ⊗ C) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor GF H k :=
    gen d.tensorEnrichedFunctor GF H k (c ⊗ a, e)
  let m := Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F G).hom
    (GradedNatTrans.unitId H) k
  let ins := 𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)
  let ins' := 𝟙 W' ⊗ₘ (u' ⊗ₘ 𝟙 C)
  let q := (v ≫ u') ⊗ₘ 𝟙 C
  let oq := o ⊗ₘ 𝟙 C
  have hl : leftAt d F G H k a c e = ins ≫ γ :=
    AssociatorFlattening.leftGenerator_flatToNested d F G H k ((a, c), e)
  have hr : leftAt d G F H k c a e = ins' ≫ δ' :=
    AssociatorFlattening.leftGenerator_flatToNested d G F H k ((c, a), e)
  have hu : u ≫ t = v ≫ u' ≫ o :=
    BraidingGenerators.unitGenerator_braid d F G b (a, c)
  have ht : (eHomEquiv V).symm ((BraidingFunctor.functorIso d b F G).hom.app (a ⊗ c)) = t :=
    BraidingFunctor.functorIso_hom_component d b F G (a ⊗ c)
  have hm : γ ≫ m = (𝟙 W ⊗ₘ (t ⊗ₘ 𝟙 C)) ≫ δ := by
    have h := Input.gen_mapAt d.tensorEnrichedFunctor
      (BraidingFunctor.functorIso d b F G).hom (GradedNatTrans.unitId H) k (a ⊗ c, e)
    rw [ht, GradedNatTrans.unitId_component] at h
    exact h
  have hrel : (w ⊗ₘ 𝟙 (D' ⊗ C)) ≫ δ' = (𝟙 W ⊗ₘ oq) ≫ δ := by
    have h := BraidingGenerators.gen_input d GF H k (β_ a c).inv (𝟙 e)
    have he : eHomWhiskerRight V ((β_ a c).inv ⊗ₘ 𝟙 e) k = w := by
      simp only [tensorHom_id]
      rfl
    simp only [Functor.map_id] at h
    rw [he] at h
    exact h
  have hq : ((u ≫ t) ⊗ₘ 𝟙 C) = q ≫ oq := by
    simp only [q, oq, tensorHom_comp_tensorHom, Category.comp_id]
    exact congrArg (fun z => z ⊗ₘ 𝟙 C) (hu.trans (Category.assoc v u' o).symm)
  have hs : ins ≫ (𝟙 W ⊗ₘ (t ⊗ₘ 𝟙 C)) = 𝟙 W ⊗ₘ (q ≫ oq) := by
    simp only [ins, tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => 𝟙 W ⊗ₘ z) hq
  have hf : (w ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ ins' = w ⊗ₘ q := by
    simp only [ins', q, tensorHom_comp_tensorHom, Category.comp_id]
  change leftAt d F G H k a c e ≫ m = (w ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ leftAt d G F H k c a e
  calc
    _ = ins ≫ (𝟙 W ⊗ₘ (t ⊗ₘ 𝟙 C)) ≫ δ :=
      (congrArg (fun z => z ≫ m) hl).trans
        ((Category.assoc ins γ m).trans (congrArg (fun z => ins ≫ z) hm))
    _ = (𝟙 W ⊗ₘ (q ≫ oq)) ≫ δ := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ δ) hs
    _ = (w ⊗ₘ q) ≫ δ' := coefficient_transfer w q oq δ δ' hrel
    _ = (w ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ ins' ≫ δ' := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ δ') hf.symm
    _ = _ := congrArg (fun z => (w ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ z) hr.symm

/-- The complete right inner braid keeps all three coefficient objects and the whole output Hom. -/
@[reassoc]
theorem inner_right :
    rightAt d F G H k a c e ≫ Input.mapAt d.tensorEnrichedFunctor
        (GradedNatTrans.unitId F) (BraidingFunctor.functorIso d b G H).hom k =
      (eHomWhiskerRight V (a ◁ (β_ c e).inv) k ⊗ₘ
        (𝟙 (F.obj a) ⊗ₘ (β_ (G.obj c) (H.obj e)).hom)) ≫
        rightAt d F H G k a e c := by
  let A := F.obj a
  let P := G.obj c ⊗ H.obj e
  let P' := H.obj e ⊗ G.obj c
  let GH := Output.functor d.tensorEnrichedFunctor G H
  let HG := Output.functor d.tensorEnrichedFunctor H G
  let D := GH.obj (c ⊗ e)
  let D' := HG.obj (e ⊗ c)
  let D₁ := HG.obj (c ⊗ e)
  let W : V := (a ⊗ (c ⊗ e)) ⟶[V] k
  let W' : V := (a ⊗ (e ⊗ c)) ⟶[V] k
  let u : P ⟶ D := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (c, e)
  let u' : P' ⟶ D' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor H G (e, c)
  let v : P ⟶ P' := (β_ (G.obj c) (H.obj e)).hom
  let t : D ⟶ D₁ := BraidingComponents.component d b G H (c ⊗ e)
  let o : D' ⟶ D₁ := HG.toOrdinaryFunctor.map (β_ c e).inv
  let w : W ⟶ W' := eHomWhiskerRight V (a ◁ (β_ c e).inv) k
  let γ : W ⊗ (A ⊗ D) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F GH k :=
    gen d.tensorEnrichedFunctor F GH k (a, c ⊗ e)
  let δ : W ⊗ (A ⊗ D₁) ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F HG k :=
    gen d.tensorEnrichedFunctor F HG k (a, c ⊗ e)
  let δ' : W' ⊗ (A ⊗ D') ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F HG k :=
    gen d.tensorEnrichedFunctor F HG k (a, e ⊗ c)
  let m := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (BraidingFunctor.functorIso d b G H).hom k
  let ins := 𝟙 W ⊗ₘ (𝟙 A ⊗ₘ u)
  let ins' := 𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ u')
  let q := 𝟙 A ⊗ₘ (v ≫ u')
  let oq := 𝟙 A ⊗ₘ o
  have hl : rightAt d F G H k a c e = ins ≫ γ :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F G H k ((a, c), e)
  have hr : rightAt d F H G k a e c = ins' ≫ δ' :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F H G k ((a, e), c)
  have hu : u ≫ t = v ≫ u' ≫ o :=
    BraidingGenerators.unitGenerator_braid d G H b (c, e)
  have ht : (eHomEquiv V).symm ((BraidingFunctor.functorIso d b G H).hom.app (c ⊗ e)) = t :=
    BraidingFunctor.functorIso_hom_component d b G H (c ⊗ e)
  have hm : γ ≫ m = (𝟙 W ⊗ₘ (𝟙 A ⊗ₘ t)) ≫ δ := by
    have h := Input.gen_mapAt d.tensorEnrichedFunctor
      (GradedNatTrans.unitId F) (BraidingFunctor.functorIso d b G H).hom k (a, c ⊗ e)
    rw [GradedNatTrans.unitId_component, ht] at h
    exact h
  have hrel : (w ⊗ₘ 𝟙 (A ⊗ D')) ≫ δ' = (𝟙 W ⊗ₘ oq) ≫ δ := by
    have h := BraidingGenerators.gen_input d F HG k (𝟙 a) (β_ c e).inv
    have he : eHomWhiskerRight V (𝟙 a ⊗ₘ (β_ c e).inv) k = w := by
      simp only [id_tensorHom]
      rfl
    simp only [Functor.map_id] at h
    rw [he] at h
    exact h
  have hq : (𝟙 A ⊗ₘ (u ≫ t)) = q ≫ oq := by
    simp only [q, oq, tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => 𝟙 A ⊗ₘ z) (hu.trans (Category.assoc v u' o).symm)
  have hs : ins ≫ (𝟙 W ⊗ₘ (𝟙 A ⊗ₘ t)) = 𝟙 W ⊗ₘ (q ≫ oq) := by
    simp only [ins, tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => 𝟙 W ⊗ₘ z) hq
  have hf : (w ⊗ₘ (𝟙 A ⊗ₘ v)) ≫ ins' = w ⊗ₘ q := by
    simp only [ins', q, tensorHom_comp_tensorHom, Category.comp_id]
  change rightAt d F G H k a c e ≫ m = (w ⊗ₘ (𝟙 A ⊗ₘ v)) ≫ rightAt d F H G k a e c
  calc
    _ = ins ≫ (𝟙 W ⊗ₘ (𝟙 A ⊗ₘ t)) ≫ δ :=
      (congrArg (fun z => z ≫ m) hl).trans
        ((Category.assoc ins γ m).trans (congrArg (fun z => ins ≫ z) hm))
    _ = (𝟙 W ⊗ₘ (q ≫ oq)) ≫ δ := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ δ) hs
    _ = (w ⊗ₘ q) ≫ δ' := coefficient_transfer w q oq δ δ' hrel
    _ = (w ⊗ₘ (𝟙 A ⊗ₘ v)) ≫ ins' ≫ δ' := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ δ') hf.symm
    _ = _ := congrArg (fun z => (w ⊗ₘ (𝟙 A ⊗ₘ v)) ≫ z) hr.symm

end CategoryTheory.EnrichedDayKernel.BraidingTriple
