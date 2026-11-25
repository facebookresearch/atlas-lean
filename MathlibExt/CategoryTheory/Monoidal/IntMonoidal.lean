/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Tensor structure on the Int construction

The tensor combines positive objects covariantly and negative objects in reversed
order. Source: Joyal, Street and Verity, Traced monoidal categories (1996),
Proposition 4.2, https://doi.org/10.1017/S0305004100074338, in the symmetric case.

This module constructs a symmetric monoidal category from an arbitrary supplied
symmetric trace, and makes the fully faithful embedding strong symmetric monoidal.
It does not assume rigidity of the source. Compact closure of Int, preservation
of trace by the embedding, and the universal property are subsequent results.
-/

@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory
open scoped MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
namespace IntConstruction
variable (T : SymmetricTrace C)

private theorem trace_pre' {A B D U : C} (f : A ⟶ B) (g : B ⊗ U ⟶ D ⊗ U) :
    T.trace (f ▷ U ≫ g) = f ≫ T.trace g := by
  simpa using T.naturality g f (𝟙 D)

private theorem trace_post' {A B D U : C} (f : A ⊗ U ⟶ B ⊗ U) (g : B ⟶ D) :
    T.trace (f ≫ g ▷ U) = T.trace f ≫ g := by
  simpa using T.naturality f (𝟙 A) g

@[reassoc] theorem exchange_middle {U V : C} (A W : C) (b : V ⟶ U) :
    (A ◁ b) ▷ W ≫ exchange A U W = exchange A V W ≫ (A ⊗ W) ◁ b := by
  simp only [exchange, Category.assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left,
    whiskerLeft_comp, associator_inv_naturality_right]

@[reassoc] theorem exchange_right {U V : C} (A W : C) (b : V ⟶ U) :
    (A ⊗ W) ◁ b ≫ exchange A W U = exchange A W V ≫ (A ◁ b) ▷ W := by
  simp only [exchange, Category.assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp, associator_inv_naturality_middle]

/-- Composition with separate positive and negative maps does not leave feedback. -/
theorem compose_tensor_left {A B D U V W : C}
    (a : A ⟶ B) (b : V ⟶ U) (f : B ⊗ W ⟶ D ⊗ V) :
    compose T (a ⊗ₘ b) f = a ▷ W ≫ f ≫ D ◁ b := by
  simp only [compose, tensorHom_def, comp_whiskerRight, Category.assoc]
  rw [← exchange_naturality_assoc]
  rw [trace_pre']
  congr 1
  rw [exchange_middle_assoc, whisker_exchange_assoc, exchange_right]
  simp only [exchange_exchange_assoc]
  rw [← Category.assoc, trace_post']
  have h : T.trace (f ▷ V ≫ exchange D V V) = f := by
    simpa [compose, Category.assoc, exchange_exchange_assoc] using id_compose T f
  simp only [h]

/-- The analogous formula when the second morphism has separate components. -/
theorem compose_tensor_right {A B D U V W : C}
    (f : A ⊗ V ⟶ B ⊗ U) (a : B ⟶ D) (b : W ⟶ V) :
    compose T f (a ⊗ₘ b) = A ◁ b ≫ f ≫ a ▷ U := by
  simp only [compose, tensorHom_def', comp_whiskerRight, Category.assoc]
  rw [exchange_naturality]
  simp only [← Category.assoc]
  rw [trace_post']
  congr 1
  simp only [Category.assoc]
  rw [← exchange_right_assoc, ← whisker_exchange_assoc, ← exchange_middle_assoc]
  simp only [exchange_exchange]
  rw [trace_pre']
  have h : T.trace (exchange A V V ≫ f ▷ V) = f := by
    simpa [compose, Category.assoc, exchange_exchange_assoc] using compose_id T f
  simp only [Category.comp_id, h]

/-- A pair of source morphisms gives a separated Int morphism. -/
def mapPair {X Y : IntConstruction T}
    (f : X.positive ⟶ Y.positive) (g : Y.negative ⟶ X.negative) : X ⟶ Y :=
  ofHom T (f ⊗ₘ g)

@[simp] theorem hom_mapPair {X Y : IntConstruction T}
    (f : X.positive ⟶ Y.positive) (g : Y.negative ⟶ X.negative) :
    hom T (mapPair T f g) = f ⊗ₘ g := rfl

@[simp] theorem mapPair_id (X : IntConstruction T) :
    mapPair T (𝟙 X.positive) (𝟙 X.negative) = 𝟙 X := by
  apply hom_ext T
  change (𝟙 X.positive) ⊗ₘ (𝟙 X.negative) = 𝟙 _
  simp

@[simp] theorem mapPair_comp {X Y Z : IntConstruction T}
    (f : X.positive ⟶ Y.positive) (g : Y.negative ⟶ X.negative)
    (h : Y.positive ⟶ Z.positive) (k : Z.negative ⟶ Y.negative) :
    mapPair T f g ≫ mapPair T h k = mapPair T (f ≫ h) (k ≫ g) := by
  apply hom_ext T
  change compose T (f ⊗ₘ g) (h ⊗ₘ k) = (f ≫ h) ⊗ₘ (k ≫ g)
  rw [compose_tensor_left]
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc]

/-- Component isomorphisms induce an isomorphism of Int objects. -/
def pairIso {X Y : IntConstruction T}
    (f : X.positive ≅ Y.positive) (g : Y.negative ≅ X.negative) : X ≅ Y where
  hom := mapPair T f.hom g.hom
  inv := mapPair T f.inv g.inv
  hom_inv_id := by rw [mapPair_comp]; simp
  inv_hom_id := by rw [mapPair_comp]; simp

/-- Tensor positive components and reverse the order of negative components. -/
abbrev tensorObject (X Y : IntConstruction T) : IntConstruction T :=
  ⟨X.positive ⊗ Y.positive, Y.negative ⊗ X.negative⟩

/-- Group the two crossed pairs for the tensor of Int morphisms. -/
def tensorShuffle (A B U V : C) :
    (A ⊗ B) ⊗ (V ⊗ U) ≅ (A ⊗ U) ⊗ (B ⊗ V) :=
  whiskerLeftIso (A ⊗ B) (β_ V U) ≪≫
    { hom := tensorμ A B U V
      inv := tensorδ A B U V
      hom_inv_id := tensorμ_tensorδ A B U V
      inv_hom_id := tensorδ_tensorμ A B U V }

/-- Tensor crossed morphisms by grouping their inputs, tensoring, and ungrouping outputs. -/
def tensorMap {X₁ X₂ Y₁ Y₂ : IntConstruction T} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObject T X₁ X₂ ⟶ tensorObject T Y₁ Y₂ :=
  ofHom T ((tensorShuffle X₁.positive X₂.positive Y₁.negative Y₂.negative).hom ≫
    (hom T f ⊗ₘ hom T g) ≫
    (tensorShuffle Y₁.positive Y₂.positive X₁.negative X₂.negative).inv)

@[simp] theorem tensorMap_id (X Y : IntConstruction T) :
    tensorMap T (𝟙 X) (𝟙 Y) = 𝟙 (tensorObject T X Y) := by
  apply hom_ext T
  change (tensorShuffle _ _ _ _).hom ≫ (𝟙 _ ⊗ₘ 𝟙 _) ≫
    (tensorShuffle _ _ _ _).inv = 𝟙 _
  simp

/-- Naturality of the grouping isomorphism in all four wires. -/
@[reassoc] theorem tensorShuffle_natural {A B U V A' B' U' V' : C}
    (a : A ⟶ A') (b : B ⟶ B') (u : U ⟶ U') (v : V ⟶ V') :
    ((a ⊗ₘ b) ⊗ₘ (v ⊗ₘ u)) ≫ (tensorShuffle A' B' U' V').hom =
      (tensorShuffle A B U V).hom ≫ ((a ⊗ₘ u) ⊗ₘ (b ⊗ₘ v)) := by
  simp only [tensorShuffle, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    BraidedCategory.braiding_naturality]
  rw [← Category.id_comp (a ⊗ₘ b), ← tensorHom_comp_tensorHom_assoc, id_tensorHom]
  rw [tensorμ_natural]

@[simp] theorem tensorMap_mapPair {X₁ X₂ Y₁ Y₂ : IntConstruction T}
    (f : X₁.positive ⟶ Y₁.positive) (g : Y₁.negative ⟶ X₁.negative)
    (h : X₂.positive ⟶ Y₂.positive) (k : Y₂.negative ⟶ X₂.negative) :
    tensorMap T (mapPair T f g) (mapPair T h k) =
      mapPair T (f ⊗ₘ h) (k ⊗ₘ g) := by
  apply hom_ext T
  change (tensorShuffle _ _ _ _).hom ≫ ((f ⊗ₘ g) ⊗ₘ (h ⊗ₘ k)) ≫
      (tensorShuffle _ _ _ _).inv = (f ⊗ₘ h) ⊗ₘ (k ⊗ₘ g)
  rw [← tensorShuffle_natural_assoc]
  simp

/-- Superposing on the right with a general morphism. -/
theorem trace_tensor_right {A B U W Z : C}
    (f : A ⊗ U ⟶ B ⊗ U) (g : W ⟶ Z) :
    T.trace (exchange A W U ≫ (f ⊗ₘ g) ≫ exchange B U Z) =
      T.trace f ⊗ₘ g := by
  simp only [tensorHom_def, Category.assoc]
  rw [exchange_right]
  simp only [← Category.assoc]
  rw [trace_post']
  simp only [Category.assoc]
  rw [trace_whiskerRight]

/-- Two disjoint feedback networks can be traced independently. -/
theorem trace_tensor {A B D E U V : C}
    (f : A ⊗ U ⟶ D ⊗ U) (g : B ⊗ V ⟶ E ⊗ V) :
    T.trace (tensorμ A B U V ≫ (f ⊗ₘ g) ≫ tensorδ D E U V) =
      T.trace f ⊗ₘ T.trace g := by
  rw [T.vanishing_tensor]
  have h : (α_ (A ⊗ B) U V).hom ≫ tensorμ A B U V ≫
      (f ⊗ₘ g) ≫ tensorδ D E U V ≫ (α_ (D ⊗ E) U V).inv =
      exchange A B U ▷ V ≫ (α_ (A ⊗ U) B V).hom ≫ (f ⊗ₘ g) ≫
        (α_ (D ⊗ U) E V).inv ≫ exchange D U E ▷ V := by
    simp only [tensorμ, tensorδ, exchange,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding]
    monoidal
  simp only [Category.assoc]
  rw [h]
  simp only [← Category.assoc]
  rw [trace_post']
  simp only [Category.assoc]
  rw [trace_pre', T.superposing]
  simpa only [Category.assoc] using trace_tensor_right T f (T.trace g)

@[instance_reducible] private def productSymmetric : SymmetricCategory (C × C) where
  braiding X Y := (β_ X.1 Y.1).prod (β_ X.2 Y.2)
  braiding_naturality_right X _ _ f := Prod.ext
    (BraidedCategory.braiding_naturality_right X.1 f.1)
    (BraidedCategory.braiding_naturality_right X.2 f.2)
  braiding_naturality_left f Z := Prod.ext
    (BraidedCategory.braiding_naturality_left f.1 Z.1)
    (BraidedCategory.braiding_naturality_left f.2 Z.2)
  hexagon_forward X Y Z := Prod.ext
    (BraidedCategory.hexagon_forward X.1 Y.1 Z.1)
    (BraidedCategory.hexagon_forward X.2 Y.2 Z.2)
  hexagon_reverse X Y Z := Prod.ext
    (BraidedCategory.hexagon_reverse X.1 Y.1 Z.1)
    (BraidedCategory.hexagon_reverse X.2 Y.2 Z.2)
  symmetry X Y := Prod.ext (SymmetricCategory.symmetry X.1 Y.1)
    (SymmetricCategory.symmetry X.2 Y.2)

attribute [local instance] productSymmetric

private def productTrace : SymmetricTrace (C × C) where
  trace f := (T.trace f.1, T.trace f.2)
  naturality f g h := Prod.ext (T.naturality f.1 g.1 h.1) (T.naturality f.2 g.2 h.2)
  dinaturality f g := Prod.ext (T.dinaturality f.1 g.1) (T.dinaturality f.2 g.2)
  vanishing_unit f := Prod.ext (T.vanishing_unit f.1) (T.vanishing_unit f.2)
  vanishing_tensor f := Prod.ext (T.vanishing_tensor f.1) (T.vanishing_tensor f.2)
  superposing f g := Prod.ext (T.superposing f.1 g.1) (T.superposing f.2 g.2)
  yanking X := Prod.ext (T.yanking X.1) (T.yanking X.2)

@[instance_reducible] private def tensorBraided : (tensor C).Braided where
  braided X Y := by
    change tensorμ X.1 X.2 Y.1 Y.2 ≫ ((β_ X.1 Y.1).hom ⊗ₘ (β_ X.2 Y.2).hom) =
      (β_ (X.1 ⊗ X.2) (Y.1 ⊗ Y.2)).hom ≫ tensorμ Y.1 Y.2 X.1 X.2
    simp [tensorμ, tensorHom_def]
    simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc,
      SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id, whiskerLeft_id]

attribute [local instance] tensorBraided

private theorem tensor_preserves : (productTrace T).Preserves T (tensor C) := by
  intro X Y U f
  exact (trace_tensor T f.1 f.2).symm

private theorem tensorMapStraight_compose {A B E U V W A' B' E' U' V' W' : C}
    (f : A ⊗ V ⟶ B ⊗ U) (g : B ⊗ W ⟶ E ⊗ V)
    (f' : A' ⊗ V' ⟶ B' ⊗ U') (g' : B' ⊗ W' ⟶ E' ⊗ V') :
    tensorμ A A' W W' ≫ (compose T f g ⊗ₘ compose T f' g') ≫ tensorδ E E' U U' =
      compose T (tensorμ A A' V V' ≫ (f ⊗ₘ f') ≫ tensorδ B B' U U')
        (tensorμ B B' W W' ≫ (g ⊗ₘ g') ≫ tensorδ E E' V V') :=
  mapCrossed_compose (productTrace T) T (tensor C) (tensor_preserves T) (A := (A, A'))
    (B := (B, B')) (E := (E, E'))
    (U := (U, U')) (V := (V, V')) (W := (W, W')) (f, f') (g, g')

private abbrev straightTensorObject (X Y : IntConstruction T) : IntConstruction T :=
  ⟨X.positive ⊗ Y.positive, X.negative ⊗ Y.negative⟩

private abbrev straightTensorFunctor :
    (IntConstruction T × IntConstruction T) ⥤ IntConstruction T where
  obj X := straightTensorObject T X.1 X.2
  map {X Y} f := ofHom T (tensorμ X.1.positive X.2.positive Y.1.negative Y.2.negative ≫
    (hom T f.1 ⊗ₘ hom T f.2) ≫ tensorδ Y.1.positive Y.2.positive X.1.negative X.2.negative)
  map_id X := by
    apply hom_ext T
    change tensorμ _ _ _ _ ≫ (𝟙 _ ⊗ₘ 𝟙 _) ≫ tensorδ _ _ _ _ = 𝟙 _
    simp
  map_comp f g := tensorMapStraight_compose T (hom T f.1) (hom T g.1)
    (hom T f.2) (hom T g.2)

private abbrev reverseNegative (X Y : IntConstruction T) :
    tensorObject T X Y ≅ straightTensorObject T X Y :=
  pairIso T (Iso.refl _) (β_ X.negative Y.negative)

private theorem tensorMap_conjugate {X₁ X₂ Y₁ Y₂ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorMap T f g = (reverseNegative T X₁ X₂).hom ≫
      (straightTensorFunctor T).map (X := (X₁, X₂)) (Y := (Y₁, Y₂)) (f, g) ≫
        (reverseNegative T Y₁ Y₂).inv := by
  apply hom_ext T
  change _ = compose T (_ ⊗ₘ _) (compose T _ (_ ⊗ₘ _))
  rw [compose_tensor_left, compose_tensor_right]
  simp only [tensorMap, hom_ofHom, tensorShuffle, Iso.trans_hom, Iso.trans_inv,
    whiskerLeftIso_hom, whiskerLeftIso_inv, Iso.refl_hom, Iso.refl_inv,
    id_whiskerRight, Category.id_comp, Category.comp_id, Category.assoc,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [ofHom, Category.assoc]

/-- Tensoring Int morphisms preserves their feedback composition. -/
theorem tensorMap_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : Y₁ ⟶ Z₁) (k : Y₂ ⟶ Z₂) :
    tensorMap T f g ≫ tensorMap T h k = tensorMap T (f ≫ h) (g ≫ k) := by
  rw [tensorMap_conjugate, tensorMap_conjugate, tensorMap_conjugate]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hmap := (straightTensorFunctor T).map_comp
    (X := (X₁, X₂)) (Y := (Y₁, Y₂)) (Z := (Z₁, Z₂)) (f, g) (h, k)
  simpa only [Category.assoc, CategoryTheory.prod_comp_fst, CategoryTheory.prod_comp_snd] using
    congrArg (fun q =>
    (reverseNegative T X₁ X₂).hom ≫ q ≫ (reverseNegative T Z₁ Z₂).inv) hmap.symm

private theorem tensorShuffle_assoc (A B D U V W : C) :
    (tensorShuffle (A ⊗ B) D (V ⊗ U) W).hom ≫
      (tensorShuffle A B U V).hom ▷ (D ⊗ W) ≫
        (α_ (A ⊗ U) (B ⊗ V) (D ⊗ W)).hom =
      (α_ A B D).hom ▷ (W ⊗ (V ⊗ U)) ≫
        (A ⊗ (B ⊗ D)) ◁ (α_ W V U).inv ≫
          (tensorShuffle A (B ⊗ D) U (W ⊗ V)).hom ≫
            (A ⊗ U) ◁ (tensorShuffle B D V W).hom := by
  have h := congrArg (fun q =>
    𝟙 (((A ⊗ B) ⊗ D) ⊗ (W ⊗ (V ⊗ U))) ⊗≫ A ◁ q ⊗≫
      𝟙 ((A ⊗ U) ⊗ ((B ⊗ V) ⊗ (D ⊗ W))))
    (BraidedCategory.braiding_naturality_left (B ◁ (β_ (D ⊗ W) V).hom) U)
  convert h using 1
  · let wrap (q : (D ⊗ V) ⊗ (W ⊗ U) ⟶ (V ⊗ D) ⊗ (U ⊗ W)) :
        ((A ⊗ B) ⊗ D) ⊗ (W ⊗ (V ⊗ U)) ⟶
          (A ⊗ U) ⊗ ((B ⊗ V) ⊗ (D ⊗ W)) :=
      𝟙 _ ⊗≫ A ◁ (B ◁ ((D ◁ (β_ W V).hom) ▷ U)) ⊗≫ A ◁ B ◁ q ⊗≫
        A ◁ (B ◁ ((V ◁ (β_ D U).hom) ▷ W)) ⊗≫
          A ◁ (B ◁ ((β_ V U).hom ▷ (D ⊗ W))) ⊗≫
            A ◁ ((β_ B U).hom ▷ (V ⊗ (D ⊗ W))) ⊗≫ 𝟙 _
    have e := congrArg wrap (whisker_exchange (β_ D V).hom (β_ W U).hom)
    convert e using 1 <;>
      (dsimp only [wrap];
       simp only [tensorShuffle, Iso.trans_hom, whiskerLeftIso_hom, tensorμ,
         BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom];
       monoidal)
  · simp only [tensorShuffle, Iso.trans_hom, whiskerLeftIso_hom, tensorμ,
      BraidedCategory.braiding_tensor_left_hom]
    monoidal

private def leftGrouping (A B D U V W : C) :
    ((A ⊗ B) ⊗ D) ⊗ (W ⊗ (V ⊗ U)) ≅ ((A ⊗ U) ⊗ (B ⊗ V)) ⊗ (D ⊗ W) :=
  tensorShuffle (A ⊗ B) D (V ⊗ U) W ≪≫
    (tensorShuffle A B U V ⊗ᵢ Iso.refl (D ⊗ W))

private def rightGrouping (A B D U V W : C) :
    (A ⊗ (B ⊗ D)) ⊗ ((W ⊗ V) ⊗ U) ≅ (A ⊗ U) ⊗ ((B ⊗ V) ⊗ (D ⊗ W)) :=
  tensorShuffle A (B ⊗ D) U (W ⊗ V) ≪≫
    (Iso.refl (A ⊗ U) ⊗ᵢ tensorShuffle B D V W)

private theorem rightGrouping_eq (A B D U V W : C) :
    rightGrouping A B D U V W =
      ((α_ A B D) ⊗ᵢ (α_ W V U).symm).symm ≪≫ leftGrouping A B D U V W ≪≫
        α_ (A ⊗ U) (B ⊗ V) (D ⊗ W) := by
  apply Iso.ext
  apply (cancel_epi (((α_ A B D) ⊗ᵢ (α_ W V U).symm).hom)).1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  simpa only [rightGrouping, leftGrouping, Iso.trans_hom, tensorIso_hom,
    Iso.refl_hom, Iso.symm_hom, tensorHom_id, id_tensorHom, tensorHom_def,
    Category.assoc, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id] using
      (tensorShuffle_assoc A B D U V W).symm

private theorem tensorMap_assoc {X₁ X₂ X₃ Y₁ Y₂ Y₃ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    hom T (tensorMap T (tensorMap T f g) h) =
      (leftGrouping X₁.positive X₂.positive X₃.positive Y₁.negative Y₂.negative Y₃.negative).hom ≫
        ((hom T f ⊗ₘ hom T g) ⊗ₘ hom T h) ≫
      (leftGrouping Y₁.positive Y₂.positive Y₃.positive X₁.negative
        X₂.negative X₃.negative).inv := by
  simp only [tensorMap, hom_ofHom, leftGrouping, Iso.trans_hom, Iso.trans_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

private theorem tensorMap_assoc' {X₁ X₂ X₃ Y₁ Y₂ Y₃ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    hom T (tensorMap T f (tensorMap T g h)) =
      (rightGrouping X₁.positive X₂.positive X₃.positive Y₁.negative Y₂.negative Y₃.negative).hom ≫
        (hom T f ⊗ₘ (hom T g ⊗ₘ hom T h)) ≫
      (rightGrouping Y₁.positive Y₂.positive Y₃.positive X₁.negative
        X₂.negative X₃.negative).inv := by
  simp only [tensorMap, hom_ofHom, rightGrouping, Iso.trans_hom, Iso.trans_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

/-- Tensor data, before verifying the coherence laws. -/
instance monoidalStruct : MonoidalCategoryStruct (IntConstruction T) where
  tensorObj := tensorObject T
  tensorHom := tensorMap T
  whiskerLeft X _ _ g := tensorMap T (𝟙 X) g
  whiskerRight f X := tensorMap T f (𝟙 X)
  tensorUnit := ⟨𝟙_ C, 𝟙_ C⟩
  associator X Y Z := pairIso T (α_ X.positive Y.positive Z.positive)
    (α_ Z.negative Y.negative X.negative)
  leftUnitor X := pairIso T (λ_ X.positive) (ρ_ X.negative).symm
  rightUnitor X := pairIso T (ρ_ X.positive) (λ_ X.negative).symm

@[simp] theorem tensorUnit_positive : (𝟙_ (IntConstruction T)).positive = 𝟙_ C := rfl
@[simp] theorem tensorUnit_negative : (𝟙_ (IntConstruction T)).negative = 𝟙_ C := rfl

private theorem tensor_pentagon (W X Y Z : IntConstruction T) :
    ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫
      (𝟙 W ⊗ₘ (α_ X Y Z).hom) =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  change tensorMap T (mapPair T _ _) (𝟙 Z) ≫ mapPair T _ _ ≫
    tensorMap T (𝟙 W) (mapPair T _ _) = mapPair T _ _ ≫ mapPair T _ _
  rw [← mapPair_id T Z, ← mapPair_id T W, tensorMap_mapPair, tensorMap_mapPair,
    mapPair_comp, mapPair_comp, mapPair_comp]
  congr 1 <;> (dsimp; monoidal)

private theorem tensor_triangle (X Y : IntConstruction T) :
    (α_ X (𝟙_ (IntConstruction T)) Y).hom ≫
      (𝟙 X ⊗ₘ (λ_ Y).hom) = (ρ_ X).hom ⊗ₘ 𝟙 Y := by
  change mapPair T _ _ ≫ tensorMap T (𝟙 X) (mapPair T _ _) =
    tensorMap T (mapPair T _ _) (𝟙 Y)
  rw [← mapPair_id T X, ← mapPair_id T Y, tensorMap_mapPair, tensorMap_mapPair,
    mapPair_comp]
  congr 1 <;> (dsimp; monoidal)

private theorem tensor_associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  apply hom_ext T
  change compose T (hom T (tensorMap T (tensorMap T f g) h)) (_ ⊗ₘ _) =
    compose T (_ ⊗ₘ _) (hom T (tensorMap T f (tensorMap T g h)))
  rw [compose_tensor_right, compose_tensor_left, tensorMap_assoc, tensorMap_assoc']
  rw [rightGrouping_eq, rightGrouping_eq]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, tensorIso_inv, tensorHom_def]
  monoidal

private theorem tensor_leftUnitor_naturality {X Y : IntConstruction T} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (IntConstruction T)) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  apply hom_ext T
  change compose T (hom T (tensorMap T (𝟙 _) f)) (_ ⊗ₘ _) =
    compose T (_ ⊗ₘ _) (hom T f)
  rw [compose_tensor_right, compose_tensor_left]
  dsimp
  simp only [tensorMap, hom_ofHom, hom_id, tensorShuffle, Iso.trans_hom, Iso.trans_inv,
    whiskerLeftIso_hom, whiskerLeftIso_inv, tensorμ, tensorδ,
    tensorObject, tensorUnit_positive, tensorUnit_negative, braiding_tensorUnit_right,
    braiding_inv_tensorUnit_right]
  monoidal

private theorem tensor_rightUnitor_naturality {X Y : IntConstruction T} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ (IntConstruction T))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  apply hom_ext T
  change compose T (hom T (tensorMap T f (𝟙 _))) (_ ⊗ₘ _) =
    compose T (_ ⊗ₘ _) (hom T f)
  rw [compose_tensor_right, compose_tensor_left]
  dsimp
  simp only [tensorMap, hom_ofHom, hom_id, tensorShuffle, Iso.trans_hom, Iso.trans_inv,
    whiskerLeftIso_hom, whiskerLeftIso_inv, tensorμ, tensorδ,
    tensorObject, tensorUnit_positive, tensorUnit_negative, braiding_tensorUnit_left,
    braiding_inv_tensorUnit_left]
  monoidal

/-- The tensor uses the reversed order on the negative objects. -/
instance monoidalCategory : MonoidalCategory (IntConstruction T) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensorMap_id T)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := tensorMap_comp T)
    (associator_naturality := by exact tensor_associator_naturality T)
    (leftUnitor_naturality := by exact tensor_leftUnitor_naturality T)
    (rightUnitor_naturality := by exact tensor_rightUnitor_naturality T)
    (pentagon := by exact tensor_pentagon T)
    (triangle := by exact tensor_triangle T)

private theorem tensorShuffle_braiding (A B U V : C) :
    (tensorShuffle A B U V).hom ≫ (β_ (A ⊗ U) (B ⊗ V)).hom =
      ((β_ A B).hom ⊗ₘ (β_ V U).hom) ≫ (tensorShuffle B A V U).hom := by
  have h : (A ⊗ B) ◁ (β_ V U).hom ≫ (β_ A B).hom ▷ (U ⊗ V) ≫
      (B ⊗ A) ◁ (β_ U V).hom ≫ tensorμ B A V U =
      (β_ A B).hom ▷ (V ⊗ U) ≫ tensorμ B A V U := by
    rw [← Category.assoc, ← Category.assoc, whisker_exchange]
    simp only [Category.assoc, ← whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
      whiskerLeft_id, Category.id_comp]
  convert h using 1
  · simp [tensorShuffle, tensorμ,
      SymmetricCategory.braiding_swap_eq_inv_braiding U B]
  · simp only [tensorShuffle, Iso.trans_hom, whiskerLeftIso_hom, tensorHom_def,
      Category.assoc, ← whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
      whiskerLeft_id, Category.id_comp]

private theorem tensorShuffle_swap_eq (A B U V : C) :
    tensorShuffle B A V U =
      ((β_ A B) ⊗ᵢ (β_ V U)).symm ≪≫ tensorShuffle A B U V ≪≫
        β_ (A ⊗ U) (B ⊗ V) := by
  apply Iso.ext
  apply (cancel_epi (((β_ A B) ⊗ᵢ (β_ V U)).hom)).1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact (tensorShuffle_braiding A B U V).symm

private theorem tensor_braiding_naturality {X₁ X₂ Y₁ Y₂ : IntConstruction T}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorMap T f g ≫ mapPair T (β_ Y₁.positive Y₂.positive).hom
      (β_ Y₁.negative Y₂.negative).hom =
    mapPair T (β_ X₁.positive X₂.positive).hom
      (β_ X₁.negative X₂.negative).hom ≫ tensorMap T g f := by
  apply hom_ext T
  change compose T (hom T (tensorMap T f g)) (_ ⊗ₘ _) =
    compose T (_ ⊗ₘ _) (hom T (tensorMap T g f))
  rw [compose_tensor_right, compose_tensor_left]
  simp only [tensorMap, hom_ofHom]
  rw [tensorShuffle_swap_eq X₁.positive X₂.positive Y₁.negative Y₂.negative,
    tensorShuffle_swap_eq Y₁.positive Y₂.positive X₁.negative X₂.negative]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, tensorIso_inv]
  simp only [Category.assoc, ← BraidedCategory.braiding_naturality_assoc,
    Iso.hom_inv_id_assoc]
  simp only [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc,
    id_whiskerRight, Category.id_comp,
    SymmetricCategory.symmetry,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [← whiskerLeft_comp, SymmetricCategory.symmetry, whiskerLeft_id,
    Category.comp_id]

@[simp] theorem tensorObj_positive (X Y : IntConstruction T) :
    (X ⊗ Y).positive = X.positive ⊗ Y.positive := rfl
@[simp] theorem tensorObj_negative (X Y : IntConstruction T) :
    (X ⊗ Y).negative = Y.negative ⊗ X.negative := rfl

/-- The source symmetry acts on both components, contravariantly on the negative one. -/
instance symmetricCategory : SymmetricCategory (IntConstruction T) where
  braiding X Y := pairIso T (β_ X.positive Y.positive) (β_ X.negative Y.negative)
  braiding_naturality_left f Z := by exact tensor_braiding_naturality T f (𝟙 Z)
  braiding_naturality_right X _ _ f := by exact tensor_braiding_naturality T (𝟙 X) f
  hexagon_forward X Y Z := by
    change mapPair T _ _ ≫ mapPair T _ _ ≫ mapPair T _ _ =
      tensorMap T (mapPair T _ _) (𝟙 Z) ≫ mapPair T _ _ ≫
        tensorMap T (𝟙 Y) (mapPair T _ _)
    rw [← mapPair_id T Z, ← mapPair_id T Y, tensorMap_mapPair, tensorMap_mapPair]
    simp only [mapPair_comp]
    congr 1 <;> simp only [tensorObj_positive, tensorObj_negative,
      tensorHom_id, id_tensorHom, Category.assoc, BraidedCategory.hexagon_forward]
  hexagon_reverse X Y Z := by
    change mapPair T _ _ ≫ mapPair T _ _ ≫ mapPair T _ _ =
      tensorMap T (𝟙 X) (mapPair T _ _) ≫ mapPair T _ _ ≫
        tensorMap T (mapPair T _ _) (𝟙 Y)
    rw [← mapPair_id T X, ← mapPair_id T Y, tensorMap_mapPair, tensorMap_mapPair]
    simp only [mapPair_comp]
    congr 1 <;> simp only [tensorObj_positive, tensorObj_negative,
      tensorHom_id, id_tensorHom, Category.assoc, BraidedCategory.hexagon_reverse]
  symmetry X Y := by
    change mapPair T _ _ ≫ mapPair T _ _ = 𝟙 _
    rw [mapPair_comp]
    simpa only [SymmetricCategory.symmetry, tensorObj_positive, tensorObj_negative] using
      mapPair_id T (X ⊗ Y)

/-- Express an embedded map as a pair with an identity negative component. -/
theorem embedding_map_eq_mapPair {X Y : C} (f : X ⟶ Y) :
    (embedding T).map f = mapPair T f (𝟙 (𝟙_ C)) := by
  apply hom_ext T
  change f ▷ (𝟙_ C) = f ⊗ₘ 𝟙 (𝟙_ C)
  simp

/-- Explicit unit and tensor comparison isomorphisms for the Int embedding. -/
def embeddingCoreMonoidal : (embedding T).CoreMonoidal where
  εIso := pairIso T (Iso.refl _) (Iso.refl _)
  μIso X Y := pairIso T (Iso.refl (X ⊗ Y)) (λ_ (𝟙_ C)).symm
  μIso_hom_natural_left f X' := by
    change tensorMap T ((embedding T).map f) (𝟙 _) ≫ mapPair T _ _ =
      mapPair T _ _ ≫ (embedding T).map _
    simp only [embedding_map_eq_mapPair]
    rw [← mapPair_id T]
    dsimp only [embedding]
    rw [tensorMap_mapPair, mapPair_comp, mapPair_comp]
    congr 1 <;> simp
  μIso_hom_natural_right X' f := by
    change tensorMap T (𝟙 _) ((embedding T).map f) ≫ mapPair T _ _ =
      mapPair T _ _ ≫ (embedding T).map _
    simp only [embedding_map_eq_mapPair]
    rw [← mapPair_id T]
    dsimp only [embedding]
    rw [tensorMap_mapPair, mapPair_comp, mapPair_comp]
    congr 1 <;> simp
  associativity X Y Z := by
    change tensorMap T (mapPair T _ _) (𝟙 _) ≫ mapPair T _ _ ≫
      (embedding T).map _ = mapPair T _ _ ≫ tensorMap T (𝟙 _) (mapPair T _ _) ≫ mapPair T _ _
    rw [← mapPair_id T, ← mapPair_id T, tensorMap_mapPair, tensorMap_mapPair,
      embedding_map_eq_mapPair]
    dsimp only [embedding]
    simp only [mapPair_comp]
    congr 1 <;> (dsimp; monoidal)
  left_unitality X := by
    change mapPair T _ _ = tensorMap T (mapPair T _ _) (𝟙 _) ≫
      mapPair T _ _ ≫ (embedding T).map _
    rw [← mapPair_id T, tensorMap_mapPair, embedding_map_eq_mapPair]
    dsimp only [embedding]
    simp only [mapPair_comp]
    congr 1 <;> (dsimp; monoidal)
  right_unitality X := by
    change mapPair T _ _ = tensorMap T (𝟙 _) (mapPair T _ _) ≫
      mapPair T _ _ ≫ (embedding T).map _
    rw [← mapPair_id T, tensorMap_mapPair, embedding_map_eq_mapPair]
    dsimp only [embedding]
    simp only [mapPair_comp]
    congr 1 <;> (dsimp; monoidal)

/-- The fully faithful Int embedding is strong monoidal. -/
instance embeddingMonoidal : (embedding T).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (by exact embeddingCoreMonoidal T)

/-- The tensor comparison inserts the unit on the negative component. -/
theorem embedding_μ (X Y : C) :
    Functor.LaxMonoidal.μ (embedding T) X Y =
      mapPair T (𝟙 (X ⊗ Y)) (λ_ (𝟙_ C)).inv := rfl

@[simp] theorem hom_embedding_μ (X Y : C) :
    hom T (Functor.LaxMonoidal.μ (embedding T) X Y) =
      𝟙 (X ⊗ Y) ⊗ₘ (λ_ (𝟙_ C)).inv := rfl

@[simp] theorem embedding_ε : Functor.LaxMonoidal.ε (embedding T) =
    mapPair T (𝟙 (𝟙_ C)) (𝟙 (𝟙_ C)) := rfl

/-- The strong monoidal embedding preserves the symmetry. -/
instance embeddingBraided : (embedding T).Braided where
  braided X Y := by
    change mapPair T _ _ ≫ (embedding T).map (β_ X Y).hom =
      mapPair T _ _ ≫ mapPair T _ _
    rw [embedding_map_eq_mapPair]
    dsimp only [embedding]
    simp only [mapPair_comp]
    congr 1
    · simp
    · dsimp
      simp only [braiding_tensorUnit_right]
      monoidal

end IntConstruction
end CategoryTheory
