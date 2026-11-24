/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.Traced

/-!
# The category underlying the Int construction

Objects are positive/negative pairs. A morphism from `(A, U)` to `(B, V)` is
an arrow `A ⊗ V ⟶ B ⊗ U`, and composition closes the intermediate negative
wire using the supplied symmetric trace. No dual objects in the source are
assumed.

Source: Joyal, Street and Verity, Traced monoidal categories (1996),
Proposition 4.1, https://doi.org/10.1017/S0305004100074338, specialized to
symmetric monoidal categories.
-/

@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory
open scoped MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- A positive object together with a formal negative object. -/
structure IntConstruction (T : SymmetricTrace C) where
  /-- The forward-facing object. -/
  positive : C
  /-- The backward-facing object. -/
  negative : C

namespace IntConstruction

/-- Exchange the two right-hand wires, retaining explicit associators. -/
def exchange (A U V : C) : (A ⊗ U) ⊗ V ⟶ (A ⊗ V) ⊗ U :=
  (α_ A U V).hom ≫ A ◁ (β_ U V).hom ≫ (α_ A V U).inv

@[simp, reassoc] theorem exchange_exchange (A U V : C) :
    exchange A U V ≫ exchange A V U = 𝟙 _ := by
  simp only [exchange, Category.assoc, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id]

@[reassoc] theorem exchange_naturality {A B : C} (f : A ⟶ B) (U V : C) :
    (f ▷ U) ▷ V ≫ exchange B U V = exchange A U V ≫ (f ▷ V) ▷ U := by
  simp only [exchange, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left]

@[reassoc] theorem exchange_braid (A U V W : C) :
    exchange (A ⊗ U) V W ≫ exchange A U W ▷ V ≫ exchange (A ⊗ W) U V =
      exchange A U V ▷ W ≫ exchange (A ⊗ V) U W ≫ exchange A V W ▷ U := by
  have h := congrArg (fun k =>
    (α_ (A ⊗ U) V W).hom ≫ (α_ A U (V ⊗ W)).hom ≫ A ◁ k ≫
      (α_ A W (V ⊗ U)).inv ≫ (α_ (A ⊗ W) V U).inv)
    (BraidedCategory.yang_baxter U V W)
  convert h.symm using 1 <;> (unfold exchange; monoidal)

variable (T : SymmetricTrace C)

private theorem trace_pre {A B D U : C} (f : A ⟶ B) (g : B ⊗ U ⟶ D ⊗ U) :
    T.trace (f ▷ U ≫ g) = f ≫ T.trace g := by
  simpa using T.naturality g f (𝟙 D)

private theorem trace_post {A B D U : C} (f : A ⊗ U ⟶ B ⊗ U) (g : B ⟶ D) :
    T.trace (f ≫ g ▷ U) = T.trace f ≫ g := by
  simpa using T.naturality f (𝟙 A) g

private theorem trace_exchange (A U : C) : T.trace (exchange A U U) = 𝟙 _ := by
  simpa [exchange, T.yanking] using T.superposing (β_ U U).hom (𝟙 A)

private theorem exchange_as_braid (A W U : C) :
    exchange A W U = (β_ A W).hom ▷ U ≫ (α_ W A U).hom ≫ (β_ W (A ⊗ U)).hom := by
  simp [exchange, BraidedCategory.braiding_tensor_right_hom,
    ← comp_whiskerRight_assoc]

private theorem braid_exchange (B W U : C) :
    (β_ W (B ⊗ U)).hom ≫ exchange B U W =
      (α_ W B U).inv ≫ (β_ W B).hom ▷ U := by
  simp [exchange, BraidedCategory.braiding_tensor_right_hom, Category.assoc,
    ← whiskerLeft_comp_assoc]

/-- An untouched wire on the right can be moved outside feedback. -/
theorem trace_whiskerRight {A B U : C} (f : A ⊗ U ⟶ B ⊗ U) (W : C) :
    T.trace (exchange A W U ≫ f ▷ W ≫ exchange B U W) = T.trace f ▷ W := by
  have h := T.superposing f (𝟙 W)
  simp only [id_tensorHom] at h
  rw [exchange_as_braid]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_right_assoc, braid_exchange]
  rw [trace_pre]
  rw [← Category.assoc, ← Category.assoc, trace_post]
  simp only [Category.assoc, h]
  rw [BraidedCategory.braiding_naturality_right]
  simp

/-- Two feedback wires can be closed in either order, with the corresponding exchange. -/
theorem trace_trace_exchange {A B U V : C} (f : (A ⊗ U) ⊗ V ⟶ (B ⊗ U) ⊗ V) :
    T.trace (T.trace f) =
      T.trace (T.trace (exchange A V U ≫ f ≫ exchange B U V)) := by
  let g := (α_ A U V).inv ≫ f ≫ (α_ B U V).hom
  have h := T.dinaturality (A ◁ (β_ V U).hom ≫ g) (β_ U V).hom
  simp only [id_tensorHom, Category.assoc, ← whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp] at h
  rw [T.vanishing_tensor] at h
  rw [T.vanishing_tensor] at h
  simpa [g, exchange, Category.assoc] using h.symm

/-- The feedback network defining Int composition. -/
def compose {A B D U V W : C} (f : A ⊗ V ⟶ B ⊗ U) (g : B ⊗ W ⟶ D ⊗ V) :
    A ⊗ W ⟶ D ⊗ U :=
  T.trace (exchange A W V ≫ f ▷ W ≫ exchange B U W ≫ g ▷ U ≫ exchange D V U)

@[simp] theorem compose_id {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    compose T f (𝟙 (B ⊗ V)) = f := by
  simp only [compose, id_whiskerRight, Category.id_comp, exchange_exchange,
    Category.comp_id]
  rw [trace_post, trace_exchange, Category.id_comp]

@[simp] theorem id_compose {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    compose T (𝟙 (A ⊗ U)) f = f := by
  simp only [compose, id_whiskerRight, Category.id_comp, exchange_exchange_assoc]
  rw [trace_pre, trace_exchange, Category.comp_id]

/-- Closing the two intermediate negative wires gives associative composition. -/
theorem compose_assoc {A B D E U V W R : C}
    (f : A ⊗ V ⟶ B ⊗ U) (g : B ⊗ W ⟶ D ⊗ V) (h : D ⊗ R ⟶ E ⊗ W) :
    compose T (compose T f g) h = compose T f (compose T g h) := by
  simp only [compose]
  rw [← trace_whiskerRight, ← trace_whiskerRight]
  simp only [← trace_pre, ← trace_post]
  conv_rhs => rw [trace_trace_exchange]
  congr 2
  simp only [comp_whiskerRight, Category.assoc]
  rw [← exchange_braid_assoc A R W V,
    ← exchange_naturality_assoc f R W,
    ← exchange_braid_assoc B U R W,
    ← exchange_naturality_assoc g U R,
    ← exchange_braid_assoc D V U R,
    ← exchange_naturality_assoc h V U,
    ← exchange_braid_assoc E W V U]
  simp

/-- Objects with trivial negative part compose without feedback. -/
@[simp] theorem compose_unit {A B D : C}
    (f : A ⊗ 𝟙_ C ⟶ B ⊗ 𝟙_ C) (g : B ⊗ 𝟙_ C ⟶ D ⊗ 𝟙_ C) :
    compose T f g = f ≫ g := by
  simp only [compose, T.vanishing_unit, exchange, braiding_tensorUnit_left]
  monoidal

instance : Category (IntConstruction T) where
  Hom X Y := X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative
  id X := 𝟙 (X.positive ⊗ X.negative)
  comp f g := compose T f g
  id_comp f := id_compose T f
  comp_id f := compose_id T f
  assoc f g h := compose_assoc T f g h

/-- View an Int morphism as its underlying crossed morphism in the source category. -/
def hom {X Y : IntConstruction T} (f : X ⟶ Y) :
    X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative := f

/-- Regard a crossed source morphism as an Int morphism. -/
def ofHom {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) : X ⟶ Y := f

@[simp] theorem hom_ofHom {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) :
    hom T (ofHom T f) = f := rfl

@[simp] theorem ofHom_hom {X Y : IntConstruction T} (f : X ⟶ Y) :
    ofHom T (hom T f) = f := rfl

@[ext] theorem hom_ext {X Y : IntConstruction T} {f g : X ⟶ Y}
    (h : hom T f = hom T g) : f = g := h

@[simp] theorem hom_id (X : IntConstruction T) :
    hom T (𝟙 X) = 𝟙 (X.positive ⊗ X.negative) := rfl

@[simp] theorem hom_comp {X Y Z : IntConstruction T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom T (f ≫ g) = compose T (hom T f) (hom T g) := rfl

/-- The fully faithful inclusion of the source as objects with trivial negative part. -/
def embedding : C ⥤ IntConstruction T where
  obj X := ⟨X, 𝟙_ C⟩
  map f := f ▷ 𝟙_ C
  map_id X := id_whiskerRight X (𝟙_ C)
  map_comp f g := by
    change (f ≫ g) ▷ 𝟙_ C = compose T (f ▷ 𝟙_ C) (g ▷ 𝟙_ C)
    rw [compose_unit, comp_whiskerRight]

instance : (embedding T).Full where
  map_surjective {X Y} f := by
    change X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C at f
    refine ⟨(ρ_ X).inv ≫ f ≫ (ρ_ Y).hom, ?_⟩
    change ((ρ_ X).inv ≫ f ≫ (ρ_ Y).hom) ▷ 𝟙_ C = f
    monoidal

instance : (embedding T).Faithful where
  map_injective {X Y} {f g} h := by
    change f ▷ 𝟙_ C = g ▷ 𝟙_ C at h
    have k := congrArg (fun q => (ρ_ X).inv ≫ q ≫ (ρ_ Y).hom) h
    simpa using k

end IntConstruction
end CategoryTheory
