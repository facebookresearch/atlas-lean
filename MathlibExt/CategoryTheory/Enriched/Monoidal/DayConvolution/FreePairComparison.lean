/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module
public import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LeftKanNaturality

/-!
# The genuine Day tensor of two free enriched diagrams

The actual external tensor is compared with the actual free diagram on
the product index by the original coefficient/Hom interchange and its
inverse. Applying the original Day/Kan comparison and the proved Kan/free
comparison gives the native Day pair. Both coefficients and all product
Hom objects occur in the maps; no tensor or free-pair comparison is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uC uD uK

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.FreePairComparison

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory

private theorem three_map_naturality {E : Type uV} [Category.{vV} E]
    {A A' B B' D D' F F' : E}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ F)
    (a' : A' ⟶ B') (b' : B' ⟶ D') (c' : D' ⟶ F')
    (p : A ⟶ A') (q : B ⟶ B') (r : D ⟶ D') (s : F ⟶ F')
    (ha : p ≫ a' = a ≫ q) (hb : q ≫ b' = b ≫ r) (hc : r ≫ c' = c ≫ s) :
    p ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ s := by
  calc
    _ = (p ≫ a') ≫ (b' ≫ c') := (Category.assoc _ _ _).symm
    _ = (a ≫ q) ≫ (b' ≫ c') := congrArg (fun f => f ≫ (b' ≫ c')) ha
    _ = a ≫ ((q ≫ b') ≫ c') := by simp only [Category.assoc]
    _ = a ≫ ((b ≫ r) ≫ c') := congrArg (fun f => a ≫ (f ≫ c')) hb
    _ = a ≫ b ≫ (r ≫ c') := by simp only [Category.assoc]
    _ = a ≫ b ≫ (c ≫ s) := congrArg (fun f => a ≫ b ≫ f) hc
    _ = _ := by simp only [Category.assoc]

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]

omit [MonoidalClosed V] in
private theorem middle_swap_involution (X U Y W : V) :
    tensorμ X U Y W ≫ tensorμ X Y U W = 𝟙 ((X ⊗ U) ⊗ (Y ⊗ W)) := by
  have hs : tensorμ X Y U W = tensorδ X U Y W := by
    dsimp only [tensorμ, tensorδ]
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding U Y]
  rw [hs]
  exact tensorμ_tensorδ X U Y W

omit [MonoidalClosed V] in
private theorem coefficient_associativity (X Y U W P Q : V) :
    tensorμ (X ⊗ U) (Y ⊗ W) P Q ≫
        ((α_ X U P).hom ⊗ₘ (α_ Y W Q).hom) ≫
        tensorμ X (U ⊗ P) Y (W ⊗ Q) =
      (tensorμ X U Y W ▷ (P ⊗ Q)) ≫
        (α_ (X ⊗ Y) (U ⊗ W) (P ⊗ Q)).hom ≫
        ((X ⊗ Y) ◁ tensorμ U W P Q) := by
  have h := tensor_associativity X Y U W P Q
  have ht := congrArg (fun f =>
    (tensorμ X U Y W ▷ (P ⊗ Q)) ≫ f ≫ tensorμ X (U ⊗ P) Y (W ⊗ Q)) h
  simp only [Category.assoc] at ht
  rw [← comp_whiskerRight_assoc, middle_swap_involution,
    id_whiskerRight, Category.id_comp, middle_swap_involution, Category.comp_id] at ht
  exact ht

omit [MonoidalClosed V] in
/-- The full coefficient interchange preserves both actual free composition actions. -/
theorem action_interchange (X Y U W P Q U' W' : V)
    (f : U ⊗ P ⟶ U') (g : W ⊗ Q ⟶ W') :
    tensorμ (X ⊗ U) (Y ⊗ W) P Q ≫
        (((α_ X U P).hom ≫ (X ◁ f)) ⊗ₘ ((α_ Y W Q).hom ≫ (Y ◁ g))) ≫
        tensorμ X U' Y W' =
      (tensorμ X U Y W ▷ (P ⊗ Q)) ≫
        (α_ (X ⊗ Y) (U ⊗ W) (P ⊗ Q)).hom ≫
        ((X ⊗ Y) ◁ (tensorμ U W P Q ≫ (f ⊗ₘ g))) := by
  have hn := tensorμ_natural (𝟙 X) f (𝟙 Y) g
  simp only [id_tensorHom, whiskerLeft_id] at hn
  rw [← tensorHom_comp_tensorHom, Category.assoc, hn]
  have h := congrArg (fun t => t ≫ ((X ⊗ Y) ◁ (f ⊗ₘ g)))
    (coefficient_associativity X Y U W P Q)
  simpa only [whiskerLeft_comp, Category.assoc] using h

omit [MonoidalClosed V] in
private theorem pair_left_unit (P Q : V) :
    (λ_ (P ⊗ Q)).inv ≫ ((λ_ (𝟙_ V)).inv ▷ (P ⊗ Q)) ≫
        tensorμ (𝟙_ V) (𝟙_ V) P Q = (λ_ P).inv ⊗ₘ (λ_ Q).inv := by
  apply (cancel_mono ((λ_ P).hom ⊗ₘ (λ_ Q).hom)).1
  simp only [Category.assoc]
  rw [← tensor_left_unitality, Iso.inv_hom_id]
  rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id]

omit [MonoidalClosed V] in
private theorem pair_right_unit (X Y : V) :
    (ρ_ (X ⊗ Y)).inv ≫ ((X ⊗ Y) ◁ (λ_ (𝟙_ V)).inv) ≫
        tensorμ X Y (𝟙_ V) (𝟙_ V) = (ρ_ X).inv ⊗ₘ (ρ_ Y).inv := by
  apply (cancel_mono ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom)).1
  simp only [Category.assoc]
  rw [← tensor_right_unitality, Iso.inv_hom_id]
  rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id]

omit [MonoidalClosed V] in
/-- Full source points and their unit insertion preserve the actual tensor interchange. -/
theorem source_point_interchange (U W P Q : V) (p : 𝟙_ V ⟶ U) (q : 𝟙_ V ⟶ W) :
    (λ_ (P ⊗ Q)).inv ≫ (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ▷ (P ⊗ Q)) ≫
        tensorμ U W P Q =
      ((λ_ P).inv ≫ (p ▷ P)) ⊗ₘ ((λ_ Q).inv ≫ (q ▷ Q)) := by
  rw [comp_whiskerRight, Category.assoc, tensorμ_natural_left]
  have h := congrArg (fun f => f ≫ ((p ▷ P) ⊗ₘ (q ▷ Q))) (pair_left_unit P Q)
  simpa only [tensorHom_comp_tensorHom, Category.assoc] using h

omit [MonoidalClosed V] in
/-- Both original free-unit coefficients are recovered by the actual inverse interchange. -/
theorem coefficient_point_interchange (X Y U W : V)
    (p : 𝟙_ V ⟶ U) (q : 𝟙_ V ⟶ W) :
    (ρ_ (X ⊗ Y)).inv ≫ ((X ⊗ Y) ◁ ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q))) ≫
        tensorδ X U Y W =
      ((ρ_ X).inv ≫ (X ◁ p)) ⊗ₘ ((ρ_ Y).inv ≫ (Y ◁ q)) := by
  have hs : tensorδ X U Y W = tensorμ X Y U W := by
    dsimp only [tensorμ, tensorδ]
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding U Y]
  rw [hs, whiskerLeft_comp, Category.assoc, tensorμ_natural_right]
  have h := congrArg (fun f => f ≫ ((X ◁ p) ⊗ₘ (Y ◁ q))) (pair_right_unit X Y)
  simpa only [tensorHom_comp_tensorHom, Category.assoc] using h

omit [MonoidalClosed V] in
/-- The product-enrichment source map retains both original full Hom precompositions. -/
theorem sourceHomMap_pair {n n' : C} {m m' : D}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (a : C × D) :
    Free.sourceHomMap (a := (n, m)) (a' := (n', m'))
        ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) a =
      Free.sourceHomMap p a.1 ⊗ₘ Free.sourceHomMap q a.2 := by
  have hc : eComp V (n, m) (n', m') a =
      tensorμ (n ⟶[V] n') (m ⟶[V] m') (n' ⟶[V] a.1) (m' ⟶[V] a.2) ≫
        (eComp V n n' a.1 ⊗ₘ eComp V m m' a.2) :=
    Enriched.prodEComp V C D (n, m) (n', m') a
  change (λ_ ((n' ⟶[V] a.1) ⊗ (m' ⟶[V] a.2))).inv ≫
      (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ▷ ((n' ⟶[V] a.1) ⊗ (m' ⟶[V] a.2))) ≫
      eComp V (n, m) (n', m') a = _
  rw [hc]
  have h := congrArg (fun f => f ≫ (eComp V n n' a.1 ⊗ₘ eComp V m m' a.2))
    (source_point_interchange (n ⟶[V] n') (m ⟶[V] m')
      (n' ⟶[V] a.1) (m' ⟶[V] a.2) p q)
  simpa only [Free.sourceHomMap, tensorHom_comp_tensorHom, Category.assoc] using h

/-- The original external tensor of the two full free enriched diagrams. -/
abbrev externalObject (n : C) (m : D) (X Y : V) : EnrichedFunctorCat V (C × D) :=
  ⟨(Free.object n X).toEnrichedFunctor.externalTensor (Free.object m Y).toEnrichedFunctor⟩

/-- The original full product-Hom free diagram has the original tensor of the coefficients. -/
abbrev productFreeObject (n : C) (m : D) (X Y : V) : EnrichedFunctorCat V (C × D) :=
  Free.object (n, m) (X ⊗ Y)

/-- Both original free actions respect every entire Hom object of the product index. -/
theorem external_full_naturality (n : C) (m : D) (X Y : V) (a b : C × D) :
    MonoidalClosed.uncurry ((externalObject n m X Y).toEnrichedFunctor.map a b) ≫
        tensorμ X (n ⟶[V] b.1) Y (m ⟶[V] b.2) =
      (tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((productFreeObject n m X Y).toEnrichedFunctor.map a b) := by
  rw [EnrichedFunctor.externalTensor_uncurry, Free.object_uncurry_map,
    Free.object_uncurry_map, Free.object_uncurry_map, tensorHom_id]
  change (tensorμ (X ⊗ (n ⟶[V] a.1)) (Y ⊗ (m ⟶[V] a.2))
      (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2) ≫
      (((α_ X (n ⟶[V] a.1) (a.1 ⟶[V] b.1)).hom ≫ (X ◁ eComp V n a.1 b.1)) ⊗ₘ
        ((α_ Y (m ⟶[V] a.2) (a.2 ⟶[V] b.2)).hom ≫ (Y ◁ eComp V m a.2 b.2)))) ≫
      tensorμ X (n ⟶[V] b.1) Y (m ⟶[V] b.2) =
    (tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) ▷
      ((a.1 ⟶[V] b.1) ⊗ (a.2 ⟶[V] b.2))) ≫
      (α_ (X ⊗ Y) ((n ⟶[V] a.1) ⊗ (m ⟶[V] a.2))
        ((a.1 ⟶[V] b.1) ⊗ (a.2 ⟶[V] b.2))).hom ≫
      ((X ⊗ Y) ◁ eComp V (n, m) a b)
  have hc : eComp V (n, m) a b =
      tensorμ (n ⟶[V] a.1) (m ⟶[V] a.2) (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2) ≫
        (eComp V n a.1 b.1 ⊗ₘ eComp V m a.2 b.2) :=
    Enriched.prodEComp V C D (n, m) a b
  rw [hc]
  simpa only [Category.assoc] using action_interchange X Y (n ⟶[V] a.1) (m ⟶[V] a.2)
    (a.1 ⟶[V] b.1) (a.2 ⟶[V] b.2) (n ⟶[V] b.1) (m ⟶[V] b.2)
    (eComp V n a.1 b.1) (eComp V m a.2 b.2)

/-- The coefficient/Hom interchange and its genuine inverse at every product index object. -/
def componentIso (n : C) (m : D) (X Y : V) (a : C × D) :
    (externalObject n m X Y).toEnrichedFunctor.obj a ≅
      (productFreeObject n m X Y).toEnrichedFunctor.obj a where
  hom := tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)
  inv := tensorδ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)
  hom_inv_id := tensorμ_tensorδ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)
  inv_hom_id := tensorδ_tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)

/-- The original inverse interchange respects the same full product-Hom action. -/
theorem external_inv_full_naturality (n : C) (m : D) (X Y : V) (a b : C × D) :
    MonoidalClosed.uncurry ((productFreeObject n m X Y).toEnrichedFunctor.map a b) ≫
        tensorδ X (n ⟶[V] b.1) Y (m ⟶[V] b.2) =
      (tensorδ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((externalObject n m X Y).toEnrichedFunctor.map a b) := by
  let f := componentIso n m X Y a
  let g := componentIso n m X Y b
  let p := MonoidalClosed.uncurry ((externalObject n m X Y).toEnrichedFunctor.map a b)
  let q := MonoidalClosed.uncurry ((productFreeObject n m X Y).toEnrichedFunctor.map a b)
  have h : p ≫ g.hom = (f.hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ q :=
    external_full_naturality n m X Y a b
  change q ≫ g.inv = (f.inv ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ p
  apply (cancel_mono g.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
    tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id]
  simp only [Category.id_comp, id_tensorHom_id]

/-- The genuine external-to-free transformation consists of the original full interchange maps. -/
def externalHom (n : C) (m : D) (X Y : V) :
    externalObject n m X Y ⟶ productFreeObject n m X Y :=
  GradedNatTrans.unitOfComponents
    (fun a => tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2))
    (external_full_naturality n m X Y)

/-- The genuine inverse transformation consists of the original inverse interchange maps. -/
def externalInv (n : C) (m : D) (X Y : V) :
    productFreeObject n m X Y ⟶ externalObject n m X Y :=
  GradedNatTrans.unitOfComponents
    (fun a => tensorδ X (n ⟶[V] a.1) Y (m ⟶[V] a.2))
    (external_inv_full_naturality n m X Y)

/-- The complete external comparison has the literal interchange component at every label. -/
theorem externalHom_component (n : C) (m : D) (X Y : V) (a : C × D) :
    component (externalHom n m X Y) a = tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The complete inverse has the literal inverse interchange component at every label. -/
theorem externalInv_component (n : C) (m : D) (X Y : V) (a : C × D) :
    component (externalInv n m X Y) a = tensorδ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The two actual full external transformations form an isomorphism
of genuine enriched diagrams. -/
def externalIso (n : C) (m : D) (X Y : V) :
    externalObject n m X Y ≅ productFreeObject n m X Y where
  hom := externalHom n m X Y
  inv := externalInv n m X Y
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [component_comp, externalHom_component, externalInv_component, component_id]
    exact tensorμ_tensorδ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [component_comp, externalHom_component, externalInv_component, component_id]
    exact tensorδ_tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)

/-- Simultaneous coefficient maps commute with the complete original external comparison. -/
theorem external_coefficient (n : C) (m : D)
    {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') :
    EnrichedFunctor.externalMap (Free.coefficientMap n f) (Free.coefficientMap m g) ≫
        externalHom n m X' Y' =
      externalHom n m X Y ≫ Free.coefficientMap (n, m) (f ⊗ₘ g) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  have hl := component_comp (F := externalObject n m X Y)
    (G := externalObject n m X' Y') (H := productFreeObject n m X' Y')
    (EnrichedFunctor.externalMap (Free.coefficientMap n f) (Free.coefficientMap m g))
    (externalHom n m X' Y') a
  have hr := component_comp (F := externalObject n m X Y)
    (G := productFreeObject n m X Y) (H := productFreeObject n m X' Y')
    (externalHom n m X Y) (Free.coefficientMap (n, m) (f ⊗ₘ g)) a
  have he : component
      (EnrichedFunctor.externalMap (Free.coefficientMap n f) (Free.coefficientMap m g)) a =
        (f ▷ (n ⟶[V] a.1)) ⊗ₘ (g ▷ (m ⟶[V] a.2)) :=
    (EnrichedFunctor.externalMap_component (Free.coefficientMap n f)
      (Free.coefficientMap m g) a).trans
        (congrArg₂ (fun s t => s ⊗ₘ t) (Free.coefficientMap_component n f a.1)
          (Free.coefficientMap_component m g a.2))
  have hn : ((f ▷ (n ⟶[V] a.1)) ⊗ₘ (g ▷ (m ⟶[V] a.2))) ≫
      tensorμ X' (n ⟶[V] a.1) Y' (m ⟶[V] a.2) =
    tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) ≫
      ((f ⊗ₘ g) ▷ ((n ⟶[V] a.1) ⊗ (m ⟶[V] a.2))) := by
    simpa only [tensorHom_id, id_whiskerRight] using
      tensorμ_natural f (𝟙 (n ⟶[V] a.1)) g (𝟙 (m ⟶[V] a.2))
  exact hl.trans ((congrArg₂ (fun s t => s ≫ t) he
    (externalHom_component n m X' Y' a)).trans
      (hn.trans ((congrArg₂ (fun s t => s ≫ t) (externalHom_component n m X Y a)
        (Free.coefficientMap_component (n, m) (f ⊗ₘ g) a)).symm.trans hr.symm)))

/-- Both labeled source maps commute with the original product-Hom interchange. -/
theorem external_source {n n' : C} {m m' : D}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V) :
    EnrichedFunctor.externalMap (Free.sourceMap p X) (Free.sourceMap q Y) ≫
        externalHom n m X Y =
      externalHom n' m' X Y ≫
        Free.sourceMap ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) (X ⊗ Y) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  have hl := component_comp (F := externalObject n' m' X Y)
    (G := externalObject n m X Y) (H := productFreeObject n m X Y)
    (EnrichedFunctor.externalMap (Free.sourceMap p X) (Free.sourceMap q Y))
    (externalHom n m X Y) a
  have hr := component_comp (F := externalObject n' m' X Y)
    (G := productFreeObject n' m' X Y) (H := productFreeObject n m X Y)
    (externalHom n' m' X Y)
    (Free.sourceMap (a := (n, m)) (a' := (n', m'))
      ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) (X ⊗ Y)) a
  have he : component (EnrichedFunctor.externalMap (Free.sourceMap p X)
      (Free.sourceMap q Y)) a =
        (X ◁ Free.sourceHomMap p a.1) ⊗ₘ (Y ◁ Free.sourceHomMap q a.2) :=
    (EnrichedFunctor.externalMap_component (Free.sourceMap p X) (Free.sourceMap q Y) a).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) (Free.sourceMap_component p X a.1)
        (Free.sourceMap_component q Y a.2))
  have hs : component (Free.sourceMap (a := (n, m)) (a' := (n', m'))
      ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) (X ⊗ Y)) a =
        (X ⊗ Y) ◁ (Free.sourceHomMap p a.1 ⊗ₘ Free.sourceHomMap q a.2) :=
    (Free.sourceMap_component (a := (n, m)) (a' := (n', m'))
      ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) (X ⊗ Y) a).trans
        (congrArg (fun s => (X ⊗ Y) ◁ s) (sourceHomMap_pair p q a))
  have hn : ((X ◁ Free.sourceHomMap p a.1) ⊗ₘ (Y ◁ Free.sourceHomMap q a.2)) ≫
      tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2) =
    tensorμ X (n' ⟶[V] a.1) Y (m' ⟶[V] a.2) ≫
      ((X ⊗ Y) ◁ (Free.sourceHomMap p a.1 ⊗ₘ Free.sourceHomMap q a.2)) := by
    simpa only [id_tensorHom, whiskerLeft_id] using
      tensorμ_natural (𝟙 X) (Free.sourceHomMap p a.1)
        (𝟙 Y) (Free.sourceHomMap q a.2)
  exact hl.trans ((congrArg₂ (fun s t => s ≫ t) he
    (externalHom_component n m X Y a)).trans
      (hn.trans ((congrArg₂ (fun s t => s ≫ t) (externalHom_component n' m' X Y a)
        hs).symm.trans hr.symm)))

/-- Original identity evaluation of the complete inverse recovers both labeled free generators. -/
theorem external_inv_unit (n : C) (m : D) (X Y : V) :
    Free.evaluate (n, m) (X ⊗ Y) (externalObject n m X Y) (externalInv n m X Y) =
      ((ρ_ X).inv ≫ (X ◁ eId V n)) ⊗ₘ ((ρ_ Y).inv ≫ (Y ◁ eId V m)) := by
  rw [Free.evaluate, externalInv_component]
  have hi : eId V (n, m) = (λ_ (𝟙_ V)).inv ≫ (eId V n ⊗ₘ eId V m) :=
    Enriched.prodEId V C D (n, m)
  rw [hi]
  exact coefficient_point_interchange X Y (n ⟶[V] n) (m ⟶[V] m) (eId V n) (eId V m)

section Day

variable {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) F.toEnrichedFunctor)]

/-- The native chosen Day output has both original arbitrary free coefficients. -/
abbrev dayObject (n : C) (m : D) (X Y : V) : EnrichedFunctorCat V K :=
  LeftKanComparison.dayObject T (Free.object n X).toEnrichedFunctor
    (Free.object m Y).toEnrichedFunctor

/-- The genuine Day/Kan maps and the original Kan/free maps construct the complete free-pair Iso. -/
def iso (n : C) (m : D) (X Y : V) :
    dayObject T n m X Y ≅ Free.object (T.obj (n, m)) (X ⊗ Y) :=
  LeftKanComparison.iso T (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor ≪≫
    (leftKan T).mapIso (externalIso n m X Y) ≪≫
    LeftKanFreeComparison.iso T (n, m) (X ⊗ Y)

/-- The entire forward comparison retains the three original genuine transformation maps. -/
theorem iso_hom (n : C) (m : D) (X Y : V) :
    (iso T n m X Y).hom =
      LeftKanComparison.toKan T (Free.object n X).toEnrichedFunctor
        (Free.object m Y).toEnrichedFunctor ≫
      (leftKan T).map (externalHom n m X Y) ≫
      LeftKanFreeComparison.hom T (n, m) (X ⊗ Y) := by
  simp only [iso, Iso.trans_hom, Functor.mapIso_hom]
  rfl

/-- The inverse retains the original free extension, inverse interchange and Kan transpose. -/
theorem iso_inv (n : C) (m : D) (X Y : V) :
    (iso T n m X Y).inv =
      LeftKanFreeComparison.inv T (n, m) (X ⊗ Y) ≫
      (leftKan T).map (externalInv n m X Y) ≫
      LeftKanComparison.fromKan T (Free.object n X).toEnrichedFunctor
        (Free.object m Y).toEnrichedFunctor := by
  simp only [iso, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  rfl

omit [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
  HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)] in
private theorem kanMap_ι {F G : EnrichedFunctorCat V (C × D)}
    (f : F ⟶ G) (k : K) (a : C × D) :
    Enriched.weightedCoend.ι (leftKanWeight T k) F.toEnrichedFunctor a ≫
        component ((leftKan T).map f) k =
      (𝟙 (T.obj a ⟶[V] k) ⊗ₘ component f a) ≫
        Enriched.weightedCoend.ι (leftKanWeight T k) G.toEnrichedFunctor a :=
  (congrArg (fun h => Enriched.weightedCoend.ι (leftKanWeight T k)
      F.toEnrichedFunctor a ≫ h) (leftKanMap_component T f k)).trans
    (leftKanMapComponent_ι T f k a)

/-- The complete contraction of a labeled Day generator, retaining both free Hom coefficients. -/
def generatorCoefficient (n : C) (m : D) (X Y : V) (k : K) (a : C × D) :
    (T.obj a ⟶[V] k) ⊗ ((X ⊗ (n ⟶[V] a.1)) ⊗ (Y ⊗ (m ⟶[V] a.2))) ⟶
      (X ⊗ Y) ⊗ (T.obj (n, m) ⟶[V] k) :=
  ((T.obj a ⟶[V] k) ◁ tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)) ≫
    ((T.obj a ⟶[V] k) ◁ ((X ⊗ Y) ◁ T.map (n, m) a)) ≫
    (β_ (T.obj a ⟶[V] k) ((X ⊗ Y) ⊗ (T.obj (n, m) ⟶[V] T.obj a))).hom ≫
    (α_ (X ⊗ Y) (T.obj (n, m) ⟶[V] T.obj a) (T.obj a ⟶[V] k)).hom ≫
    ((X ⊗ Y) ◁ eComp V (T.obj (n, m)) (T.obj a) k)

/-- Every original Day generator is carried to its complete original free contraction. -/
theorem gen_iso_hom (n : C) (m : D) (X Y : V) (k : K) (a : C × D) :
    EnrichedDayKernel.gen T (Free.object n X).toEnrichedFunctor
        (Free.object m Y).toEnrichedFunctor k a ≫ component (iso T n m X Y).hom k =
      generatorCoefficient T n m X Y k a := by
  let t := LeftKanComparison.toKan T (Free.object n X).toEnrichedFunctor
    (Free.object m Y).toEnrichedFunctor
  let l := (leftKan T).map (externalHom n m X Y)
  let h := LeftKanFreeComparison.hom T (n, m) (X ⊗ Y)
  have hc : component (iso T n m X Y).hom k =
      component t k ≫ component l k ≫ component h k := by
    have hi := congrArg (fun f => component f k) (iso_hom T n m X Y)
    have h1 := component_comp (F := dayObject T n m X Y)
      (G := leftKanObject T (externalObject n m X Y))
      (H := Free.object (T.obj (n, m)) (X ⊗ Y)) t (l ≫ h) k
    have h2 := component_comp (F := leftKanObject T (externalObject n m X Y))
      (G := leftKanObject T (productFreeObject n m X Y))
      (H := Free.object (T.obj (n, m)) (X ⊗ Y)) l h k
    exact hi.trans (h1.trans (congrArg (fun f => component t k ≫ f) h2))
  have hd : EnrichedDayKernel.gen T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor k a ≫ component t k =
    Enriched.weightedCoend.ι (leftKanWeight T k)
      (externalObject n m X Y).toEnrichedFunctor a :=
    LeftKanComparison.gen_toKan T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor k a
  have hm := kanMap_ι T (externalHom n m X Y) k a
  have he := externalHom_component n m X Y a
  have hm' : Enriched.weightedCoend.ι (leftKanWeight T k)
      (externalObject n m X Y).toEnrichedFunctor a ≫ component l k =
    ((T.obj a ⟶[V] k) ◁ tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)) ≫
      Enriched.weightedCoend.ι (leftKanWeight T k)
        (productFreeObject n m X Y).toEnrichedFunctor a :=
    hm.trans ((congrArg (fun f => (𝟙 (T.obj a ⟶[V] k) ⊗ₘ f) ≫
      Enriched.weightedCoend.ι (leftKanWeight T k)
        (productFreeObject n m X Y).toEnrichedFunctor a) he).trans
          (congrArg (fun f => f ≫ Enriched.weightedCoend.ι (leftKanWeight T k)
            (productFreeObject n m X Y).toEnrichedFunctor a) (id_tensorHom _ _)))
  have hf := LeftKanFreeComparison.hom_ι T (n, m) (X ⊗ Y) k a
  exact (congrArg (fun f => EnrichedDayKernel.gen T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor k a ≫ f) hc).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ component l k ≫ component h k) hd).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ component h k) hm').trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun f => ((T.obj a ⟶[V] k) ◁
                tensorμ X (n ⟶[V] a.1) Y (m ⟶[V] a.2)) ≫ f) hf))))))

/-- The inverse uses the original full free extension of the original external Day generators. -/
theorem iso_inv_eq_extend (n : C) (m : D) (X Y : V) :
    (iso T n m X Y).inv =
      Free.extend (T.obj (n, m)) (X ⊗ Y) (dayObject T n m X Y)
        (Free.evaluate (n, m) (X ⊗ Y) (restrictionObject T (dayObject T n m X Y))
          (externalInv n m X Y ≫ Generators.transformation T
            (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor)) := by
  let d := dayObject T n m X Y
  let l := (leftKan T).map (externalInv n m X Y)
  let t := LeftKanComparison.fromKan T (Free.object n X).toEnrichedFunctor
    (Free.object m Y).toEnrichedFunctor
  let q : leftKanObject T (productFreeObject n m X Y) ⟶ d := l ≫ t
  have hu : leftKanUnit T (productFreeObject n m X Y) ≫ restrictionMap T q =
      externalInv n m X Y ≫ Generators.transformation T
        (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor := by
    have hmap : restrictionMap T q = restrictionMap T l ≫ restrictionMap T t :=
      (restriction T).map_comp l t
    have hn := leftKanUnit_natural T (externalInv n m X Y)
    have hd := LeftKanComparison.unit_fromKan T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor
    exact (congrArg (fun f => leftKanUnit T (productFreeObject n m X Y) ≫ f) hmap).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ restrictionMap T t) hn.symm).trans
          ((Category.assoc _ _ _).trans (congrArg (fun f => externalInv n m X Y ≫ f) hd))))
  have hc : LeftKanFreeComparison.homEquiv T (n, m) (X ⊗ Y) d q =
      Free.evaluate (T.obj (n, m)) (X ⊗ Y) d
        (LeftKanFreeComparison.inv T (n, m) (X ⊗ Y) ≫ q) :=
    LeftKanFreeComparison.homEquiv_comparison T (n, m) (X ⊗ Y) d q
  let c : X ⊗ Y ⟶ d.toEnrichedFunctor.obj (T.obj (n, m)) :=
    Free.evaluate (n, m) (X ⊗ Y) (restrictionObject T d)
      (externalInv n m X Y ≫ Generators.transformation T
        (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor)
  have he := Free.evaluate_extend (T.obj (n, m)) (X ⊗ Y) d c
  apply (Free.homEquiv (T.obj (n, m)) (X ⊗ Y) d).injective
  change Free.evaluate (T.obj (n, m)) (X ⊗ Y) d (iso T n m X Y).inv =
    Free.evaluate (T.obj (n, m)) (X ⊗ Y) d
      (Free.extend (T.obj (n, m)) (X ⊗ Y) d c)
  exact ((congrArg (Free.evaluate (T.obj (n, m)) (X ⊗ Y) d) (iso_inv T n m X Y)).trans
    (hc.symm.trans ((LeftKanFreeComparison.homEquiv_apply T (n, m) (X ⊗ Y) d q).trans
      (congrArg (Free.evaluate (n, m) (X ⊗ Y) (restrictionObject T d)) hu)))).trans he.symm

/-- Both original free generators enter the actual Day point at their original ordered labels. -/
def inverseCoefficient (n : C) (m : D) (X Y : V) :
    X ⊗ Y ⟶ (dayObject T n m X Y).toEnrichedFunctor.obj (T.obj (n, m)) :=
  (((ρ_ X).inv ≫ (X ◁ eId V n)) ⊗ₘ ((ρ_ Y).inv ≫ (Y ◁ eId V m))) ≫
    Generators.point T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor (n, m)

/-- The complete inverse evaluates to the original two labeled free generators and Day unit. -/
theorem evaluate_iso_inv (n : C) (m : D) (X Y : V) :
    Free.evaluate (T.obj (n, m)) (X ⊗ Y) (dayObject T n m X Y)
        (iso T n m X Y).inv = inverseCoefficient T n m X Y := by
  have h0 := congrArg
    (Free.evaluate (T.obj (n, m)) (X ⊗ Y) (dayObject T n m X Y))
    (iso_inv_eq_extend T n m X Y)
  have h1 := Free.evaluate_extend (T.obj (n, m)) (X ⊗ Y) (dayObject T n m X Y)
    (Free.evaluate (n, m) (X ⊗ Y) (restrictionObject T (dayObject T n m X Y))
      (externalInv n m X Y ≫ Generators.transformation T
        (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor))
  have h2 := Free.evaluate_postcomp (n, m) (X ⊗ Y) (externalInv n m X Y)
    (Generators.transformation T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor)
  have h3 : (EnrichedFunctorCat.evaluation (n, m)).map (Generators.transformation T
      (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor) =
    Generators.point T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor (n, m) :=
    (EnrichedFunctorCat.evaluation_map (n, m) _).trans (Generators.transformation_component T
      (Free.object n X).toEnrichedFunctor (Free.object m Y).toEnrichedFunctor (n, m))
  exact h0.trans (h1.trans (h2.trans (congrArg₂ (fun f g => f ≫ g)
    (external_inv_unit n m X Y) h3)))

/-- At every output label, the entire inverse uses its original full output-Hom extension action. -/
theorem iso_inv_component (n : C) (m : D) (X Y : V) (k : K) :
    component (iso T n m X Y).inv k =
      (inverseCoefficient T n m X Y ⊗ₘ 𝟙 (T.obj (n, m) ⟶[V] k)) ≫
        MonoidalClosed.uncurry ((dayObject T n m X Y).toEnrichedFunctor.map (T.obj (n, m)) k) :=
  (Free.reconstruct_component (T.obj (n, m)) (X ⊗ Y) (dayObject T n m X Y)
    (iso T n m X Y).inv k).trans
      (congrArg (fun f => Free.extensionComponent (T.obj (n, m)) (X ⊗ Y)
        (dayObject T n m X Y) f k) (evaluate_iso_inv T n m X Y))

private theorem comparison_square
    {n n' : C} {m m' : D} {X X' Y Y' : V}
    (p : Free.object n X ⟶ Free.object n' X')
    (q : Free.object m Y ⟶ Free.object m' Y')
    (r : productFreeObject n m X Y ⟶ productFreeObject n' m' X' Y')
    (s : Free.object (T.obj (n, m)) (X ⊗ Y) ⟶
      Free.object (T.obj (n', m')) (X' ⊗ Y'))
    (he : EnrichedFunctor.externalMap p q ≫ externalHom n' m' X' Y' =
      externalHom n m X Y ≫ r)
    (hl : (leftKan T).map r ≫ LeftKanFreeComparison.hom T (n', m') (X' ⊗ Y') =
      LeftKanFreeComparison.hom T (n, m) (X ⊗ Y) ≫ s) :
    Input.natTrans T p q ≫ (iso T n' m' X' Y').hom = (iso T n m X Y).hom ≫ s := by
  have hd : Input.natTrans T p q ≫ LeftKanComparison.toKan T
      (Free.object n' X').toEnrichedFunctor (Free.object m' Y').toEnrichedFunctor =
    LeftKanComparison.toKan T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor ≫ (leftKan T).map (EnrichedFunctor.externalMap p q) :=
    LeftKanComparison.input_toKan T p q
  have h1 := (leftKan T).map_comp (X := externalObject n m X Y)
    (Y := externalObject n' m' X' Y') (Z := productFreeObject n' m' X' Y')
    (EnrichedFunctor.externalMap p q) (externalHom n' m' X' Y')
  have h2 := (leftKan T).map_comp (X := externalObject n m X Y)
    (Y := productFreeObject n m X Y) (Z := productFreeObject n' m' X' Y')
    (externalHom n m X Y) r
  have hm : (leftKan T).map (EnrichedFunctor.externalMap p q) ≫
      (leftKan T).map (externalHom n' m' X' Y') =
    (leftKan T).map (externalHom n m X Y) ≫ (leftKan T).map r :=
    h1.symm.trans ((congrArg (fun f => (leftKan T).map f) he).trans h2)
  simpa only [iso_hom] using three_map_naturality
    (LeftKanComparison.toKan T (Free.object n X).toEnrichedFunctor
      (Free.object m Y).toEnrichedFunctor)
    ((leftKan T).map (externalHom n m X Y))
    (LeftKanFreeComparison.hom T (n, m) (X ⊗ Y))
    (LeftKanComparison.toKan T (Free.object n' X').toEnrichedFunctor
      (Free.object m' Y').toEnrichedFunctor)
    ((leftKan T).map (externalHom n' m' X' Y'))
    (LeftKanFreeComparison.hom T (n', m') (X' ⊗ Y'))
    (Input.natTrans T p q) ((leftKan T).map (EnrichedFunctor.externalMap p q))
    ((leftKan T).map r) s hd hm hl

/-- The native Day comparison is natural in both complete arbitrary coefficient maps. -/
theorem iso_coefficient (n : C) (m : D)
    {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') :
    Input.natTrans T (Free.coefficientMap n f) (Free.coefficientMap m g) ≫
        (iso T n m X' Y').hom =
      (iso T n m X Y).hom ≫ Free.coefficientMap (T.obj (n, m)) (f ⊗ₘ g) :=
  comparison_square T (Free.coefficientMap n f) (Free.coefficientMap m g)
    (Free.coefficientMap (n, m) (f ⊗ₘ g))
    (Free.coefficientMap (T.obj (n, m)) (f ⊗ₘ g))
    (external_coefficient n m f g) (LeftKanFreeComparison.hom_coefficient T (n, m) (f ⊗ₘ g))

/-- Both original contravariant index arrows are preserved by the actual Day comparison. -/
theorem iso_source {n n' : C} {m m' : D}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V) :
    Input.natTrans T (Free.sourceMap p X) (Free.sourceMap q Y) ≫
        (iso T n m X Y).hom =
      (iso T n' m' X Y).hom ≫
        Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫ T.map (n, m) (n', m')) (X ⊗ Y) :=
  comparison_square T (Free.sourceMap p X) (Free.sourceMap q Y)
    (Free.sourceMap (a := (n, m)) (a' := (n', m'))
      ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) (X ⊗ Y))
    (Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫ T.map (n, m) (n', m')) (X ⊗ Y))
    (external_source p q X Y)
    (LeftKanFreeComparison.hom_source T
      (a := (n, m)) (a' := (n', m')) ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) (X ⊗ Y))

/-- The same two coefficient maps preserve the entire actual inverse comparison. -/
theorem iso_inv_coefficient (n : C) (m : D)
    {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') :
    Free.coefficientMap (T.obj (n, m)) (f ⊗ₘ g) ≫ (iso T n m X' Y').inv =
      (iso T n m X Y).inv ≫
        Input.natTrans T (Free.coefficientMap n f) (Free.coefficientMap m g) := by
  apply (cancel_mono (iso T n m X' Y').hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    iso_coefficient, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The inverse retains both original contravariant index arrows and their full Hom map. -/
theorem iso_inv_source {n n' : C} {m m' : D}
    (p : 𝟙_ V ⟶ (n ⟶[V] n')) (q : 𝟙_ V ⟶ (m ⟶[V] m')) (X Y : V) :
    Free.sourceMap (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ≫ T.map (n, m) (n', m')) (X ⊗ Y) ≫
        (iso T n m X Y).inv =
      (iso T n' m' X Y).inv ≫ Input.natTrans T (Free.sourceMap p X) (Free.sourceMap q Y) := by
  have h := congrArg (fun f => (iso T n' m' X Y).inv ≫ f ≫ (iso T n m X Y).inv)
    (iso_source T p q X Y)
  simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] using h.symm

/-- The original two free functors followed by the original Day bifunctor. -/
def dayPairFunctor (n : C) (m : D) : V × V ⥤ EnrichedFunctorCat V K :=
  (Free.functor n).prod (Free.functor m) ⋙ Input.bifunctor T

/-- The original ambient tensor functor followed by the original target free functor. -/
def freePairFunctor (n : C) (m : D) : V × V ⥤ EnrichedFunctorCat V K :=
  MonoidalCategory.tensor V ⋙ Free.functor (T.obj (n, m))

/-- The complete comparison is an actual natural Iso in both original coefficient variables. -/
def functorIso (n : C) (m : D) : dayPairFunctor T n m ≅ freePairFunctor T n m :=
  NatIso.ofComponents (fun P => iso T n m P.1 P.2)
    (fun f => iso_coefficient T n m f.1 f.2)

/-- Every forward component retains the original full three-map Day/Kan/free comparison. -/
theorem functorIso_hom_app (n : C) (m : D) (P : V × V) :
    (functorIso T n m).hom.app P = (iso T n m P.1 P.2).hom := rfl

/-- Every inverse component retains its original generators and full output-Hom extension. -/
theorem functorIso_inv_app (n : C) (m : D) (P : V × V) :
    (functorIso T n m).inv.app P = (iso T n m P.1 P.2).inv := rfl

end Day
end CategoryTheory.EnrichedDayKernel.FreePairComparison
