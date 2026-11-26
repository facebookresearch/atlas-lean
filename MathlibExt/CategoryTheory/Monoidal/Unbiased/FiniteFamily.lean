/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Basic.Finite.Sigma

/-!
# Finite families in a category

A finite family in `C` is a finite index type together with a family of objects
of `C`. Morphisms consist of an equivalence of the index types and a family of
morphisms in `C`. This is the underlying category for an unbiased finite-tensor
structure.
-/

@[expose] public section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂ v₃ u₃

/-- A finite family of objects of `C`, indexed by a bundled finite type.

We keep the index in `FintypeCat.{0}` (small) and not in a larger universe;
consequently `FiniteFamily C` lives in `Type (max u₁ 1)` when `C : Type u₁`,
i.e. there is a universe bump of at most one due to the `FintypeCat` bundle.
-/
structure FiniteFamily (C : Type u₁) : Type (max u₁ 1) where
  /-- The bundled finite index type. -/
  index : FintypeCat.{0}
  /-- The family of objects. -/
  obj : index → C

namespace FiniteFamily

variable {C : Type u} [Category.{v} C]

/-- A morphism of finite families: an equivalence of indices and component morphisms. -/
structure Hom (X Y : FiniteFamily C) where
  /-- Equivalence between the index types. -/
  equiv : X.index ≃ Y.index
  /-- Component morphisms. -/
  hom : (x : X.index) → X.obj x ⟶ Y.obj (equiv x)

/-- Identity morphism of finite families. -/
def Hom.id (X : FiniteFamily C) : Hom X X where
  equiv := Equiv.refl X.index
  hom _ := 𝟙 _

/-- Composition of morphisms of finite families. -/
def Hom.comp {X Y Z : FiniteFamily C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  equiv := f.equiv.trans g.equiv
  hom x := f.hom x ≫ g.hom (f.equiv x)

/-- Extensionality for morphisms of finite families. -/
theorem Hom_ext {X Y : FiniteFamily C} {f g : Hom X Y}
    (h_equiv : f.equiv = g.equiv)
    (h_hom : ∀ x, HEq (f.hom x) (g.hom x)) : f = g := by
  cases f with
  | mk equiv hom =>
    cases g with
    | mk equiv_1 hom_1 =>
      simp only at h_equiv h_hom
      subst h_equiv
      have h : hom = hom_1 := by
        funext x
        exact eq_of_heq (h_hom x)
      subst h
      rfl

@[simp]
theorem Hom_id_equiv (X : FiniteFamily C) : (Hom.id X).equiv = Equiv.refl X.index := rfl

@[simp]
theorem Hom_id_hom (X : FiniteFamily C) (x : X.index) : (Hom.id X).hom x = 𝟙 (X.obj x) := rfl

@[simp]
theorem Hom_comp_equiv {X Y Z : FiniteFamily C} (f : Hom X Y) (g : Hom Y Z) :
    (Hom.comp f g).equiv = f.equiv.trans g.equiv := rfl

@[simp]
theorem Hom_comp_hom {X Y Z : FiniteFamily C} (f : Hom X Y) (g : Hom Y Z) (x : X.index) :
    (Hom.comp f g).hom x = f.hom x ≫ g.hom (f.equiv x) := rfl

instance : CategoryStruct (FiniteFamily C) where
  Hom := Hom
  id X := Hom.id X
  comp f g := Hom.comp f g

instance : Category (FiniteFamily C) where
  id_comp f := by
    apply Hom_ext
    · exact Equiv.refl_trans _
    · intro x
      have h1 : (Hom.comp (Hom.id _) f).hom x = 𝟙 _ ≫ f.hom x := rfl
      have h2 : (𝟙 _ : _ ⟶ _) ≫ f.hom x = f.hom x := by simp
      exact heq_of_eq (h1.trans h2)
  comp_id f := by
    apply Hom_ext
    · exact Equiv.trans_refl _
    · intro x
      have h1 : (Hom.comp f (Hom.id _)).hom x = f.hom x ≫ 𝟙 _ := rfl
      have h2 : f.hom x ≫ (𝟙 _ : _ ⟶ _) = f.hom x := by simp
      exact heq_of_eq (h1.trans h2)
  assoc f g h := by
    apply Hom_ext
    · exact Equiv.trans_assoc _ _ _
    · intro x
      have h1 : (Hom.comp (Hom.comp f g) h).hom x =
          (f.hom x ≫ g.hom (f.equiv x)) ≫ h.hom (g.equiv (f.equiv x)) := rfl
      have h2 : (f.hom x ≫ g.hom (f.equiv x)) ≫ h.hom (g.equiv (f.equiv x)) =
          f.hom x ≫ g.hom (f.equiv x) ≫ h.hom (g.equiv (f.equiv x)) := by
        simp only [Category.assoc]
      exact heq_of_eq (h1.trans h2)

/-- Assemble an isomorphism of finite families from an equivalence of index types and a family of
component isomorphisms.

The inverse component includes the transport identifying `e (e.symm j)` with `j`.  Keeping this
transport here prevents downstream constructions from repeatedly rebuilding the same dependent
`HEq` argument. -/
def isoOfComponents {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (f : ∀ i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom :=
    { equiv := e
      hom := fun i => (f i).hom }
  inv :=
    { equiv := e.symm
      hom := fun j =>
        eqToHom (congrArg Y.obj (e.apply_symm_apply j).symm) ≫
          (f (e.symm j)).inv }
  hom_inv_id := by
    apply Hom_ext
    · exact e.self_trans_symm
    · intro i
      change HEq
        ((f i).hom ≫
          (eqToHom (congrArg Y.obj (e.apply_symm_apply (e i)).symm) ≫
            (f (e.symm (e i))).inv))
        (𝟙 (X.obj i))
      have h₁ :
          HEq
            (eqToHom (congrArg Y.obj (e.apply_symm_apply (e i)).symm) ≫
              (f (e.symm (e i))).inv)
            (f (e.symm (e i))).inv :=
        eqToHom_comp_heq _ _
      have h₂ : HEq (f (e.symm (e i))).inv (f i).inv := by
        rw [e.symm_apply_apply]
      have h₃ := h₁.trans h₂
      have h₄ := heq_comp rfl rfl
        (congrArg X.obj (e.symm_apply_apply i))
        (HEq.rfl : HEq (f i).hom _) h₃
      exact h₄.trans (heq_of_eq (f i).hom_inv_id)
  inv_hom_id := by
    apply Hom_ext
    · exact e.symm_trans_self
    · intro j
      change HEq
        ((eqToHom (congrArg Y.obj (e.apply_symm_apply j).symm) ≫
            (f (e.symm j)).inv) ≫
          (f (e.symm j)).hom)
        (𝟙 (Y.obj j))
      have h₁ :
          HEq
            (eqToHom (congrArg Y.obj (e.apply_symm_apply j).symm) ≫
              (f (e.symm j)).inv)
            (f (e.symm j)).inv :=
        eqToHom_comp_heq _ _
      have h₂ := heq_comp
        (congrArg Y.obj (e.apply_symm_apply j).symm) rfl rfl
        h₁ (HEq.rfl : HEq (f (e.symm j)).hom _)
      have h₃ : HEq (𝟙 (Y.obj (e (e.symm j)))) (𝟙 (Y.obj j)) := by
        rw [e.apply_symm_apply]
      exact h₂.trans <| (heq_of_eq (f (e.symm j)).inv_hom_id).trans h₃

@[simp]
theorem isoOfComponents_hom_equiv {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (f : ∀ i, X.obj i ≅ Y.obj (e i)) :
    (isoOfComponents e f).hom.equiv = e :=
  rfl

@[simp]
theorem isoOfComponents_hom_hom {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (f : ∀ i, X.obj i ≅ Y.obj (e i)) (i : X.index) :
    (isoOfComponents e f).hom.hom i = (f i).hom :=
  rfl

@[simp]
theorem isoOfComponents_inv_equiv {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (f : ∀ i, X.obj i ≅ Y.obj (e i)) :
    (isoOfComponents e f).inv.equiv = e.symm :=
  rfl

@[simp]
theorem isoOfComponents_inv_hom {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (f : ∀ i, X.obj i ≅ Y.obj (e i)) (j : Y.index) :
    (isoOfComponents e f).inv.hom j =
      eqToHom (congrArg Y.obj (e.apply_symm_apply j).symm) ≫
        (f (e.symm j)).inv :=
  rfl

/-- The reindexing isomorphism of an index equivalence plus object
agreements: identity transport components, with the inverse packaged
by `isoOfComponents`. -/
def isoOfReindex {X Y : FiniteFamily C} (e : X.index ≃ Y.index)
    (hobj : ∀ i : X.index, X.obj i = Y.obj (e i)) : X ≅ Y :=
  isoOfComponents e (fun i => eqToIso (hobj i))

/-- The index equivalence of a reindexing iso is the given one. -/
@[simp]
theorem isoOfReindex_hom_equiv {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index)
    (hobj : ∀ i : X.index, X.obj i = Y.obj (e i)) :
    (isoOfReindex e hobj).hom.equiv = e :=
  isoOfComponents_hom_equiv e _

/-- The hom components of a reindexing iso are identity transports. -/
@[simp]
theorem isoOfReindex_hom_hom {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index)
    (hobj : ∀ i : X.index, X.obj i = Y.obj (e i)) (i : X.index) :
    (isoOfReindex e hobj).hom.hom i = eqToHom (hobj i) :=
  rfl

/-- The inverse index equivalence of a reindexing iso. -/
@[simp]
theorem isoOfReindex_inv_equiv {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index)
    (hobj : ∀ i : X.index, X.obj i = Y.obj (e i)) :
    (isoOfReindex e hobj).inv.equiv = e.symm :=
  isoOfComponents_inv_equiv e _

/-- Composition of reindexing-iso homs is the hom of the composed
reindexing. -/
theorem isoOfReindex_hom_comp {X Y Z : FiniteFamily C}
    {e₁ : X.index ≃ Y.index} {e₂ : Y.index ≃ Z.index}
    {h₁ : ∀ i : X.index, X.obj i = Y.obj (e₁ i)}
    {h₂ : ∀ j : Y.index, Y.obj j = Z.obj (e₂ j)} :
    (isoOfReindex e₁ h₁).hom ≫ (isoOfReindex e₂ h₂).hom =
      (isoOfReindex (e₁.trans e₂)
        (fun i => (h₁ i).trans (h₂ (e₁ i)))).hom := by
  apply Hom_ext
  · rfl
  · intro x
    have hEq : ((isoOfReindex e₁ h₁).hom ≫
          (isoOfReindex e₂ h₂).hom).hom x =
        eqToHom (h₁ x) ≫ eqToHom (h₂ (e₁ x)) :=
      rfl
    have hRhs : ((isoOfReindex (e₁.trans e₂)
          (fun i => (h₁ i).trans (h₂ (e₁ i)))).hom).hom x =
        eqToHom ((h₁ x).trans (h₂ (e₁ x))) :=
      rfl
    rw [hEq, hRhs]
    exact heq_of_eq (eqToHom_trans (h₁ x) (h₂ (e₁ x)))

/-- Functorial action of a functor on finite families. -/
def map {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D]
    (F : C₁ ⥤ D) : FiniteFamily C₁ ⥤ FiniteFamily D where
  obj X := ⟨X.index, fun i => F.obj (X.obj i)⟩
  map {X Y} f :=
    { equiv := f.equiv
      hom := fun x => F.map (f.hom x) }
  map_id X := by
    apply Hom_ext
    · rfl
    · intro x
      have h : F.map (𝟙 (X.obj x)) = 𝟙 (F.obj (X.obj x)) := by simp
      exact heq_of_eq h
  map_comp {X Y Z} f g := by
    apply Hom_ext
    · rfl
    · intro x
      have h : F.map (f.hom x ≫ g.hom (f.equiv x)) =
          F.map (f.hom x) ≫ F.map (g.hom (f.equiv x)) := by simp
      exact heq_of_eq h

/-- Naturality of the `map` construction with respect to natural transformations.

For `α : F ⟶ G`, the component at `X : FiniteFamily C₁` has index equivalence
`refl` and components `α.app (X.obj i)`. -/
def mapNatTrans {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D]
    {F G : C₁ ⥤ D} (α : F ⟶ G) : FiniteFamily.map F ⟶ FiniteFamily.map G where
  app X :=
    { equiv := Equiv.refl X.index
      hom := fun i => α.app (X.obj i) }
  naturality X Y f := by
    apply Hom_ext
    · exact Eq.trans (Equiv.trans_refl f.equiv) (Equiv.refl_trans f.equiv).symm
    · intro x
      exact heq_of_eq (α.naturality (f.hom x))

@[simp]
theorem mapNatTrans_app_equiv {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D]
    {F G : C₁ ⥤ D} (α : F ⟶ G) (X : FiniteFamily C₁) :
    ((mapNatTrans α).app X).equiv = Equiv.refl X.index := rfl

@[simp]
theorem mapNatTrans_app_hom {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D]
    {F G : C₁ ⥤ D} (α : F ⟶ G) (X : FiniteFamily C₁) (i : X.index) :
    ((mapNatTrans α).app X).hom i = α.app (X.obj i) := rfl

/-- Functoriality of `FiniteFamily.map` in the functor argument.

`mapFunctor` sends `F : C₁ ⥤ D` to `FiniteFamily.map F` and `α : F ⟶ G` to
`mapNatTrans α`. This reuses `map` and `mapNatTrans` without duplicating data.
-/
def mapFunctor {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D] :
    (C₁ ⥤ D) ⥤ (FiniteFamily C₁ ⥤ FiniteFamily D) where
  obj F := FiniteFamily.map F
  map α := mapNatTrans α
  map_id _ := by
    ext X
    apply Hom_ext
    · rfl
    · intro x
      rfl
  map_comp _ _ := by
    ext X
    apply Hom_ext
    · rfl
    · intro x
      rfl

/-- Mapping finite families along the identity functor is naturally isomorphic to the identity. -/
def mapIdIso (C : Type u₁) [Category.{v₁} C] :
    FiniteFamily.map (𝟭 C) ≅ 𝟭 (FiniteFamily C) :=
  NatIso.ofComponents
    (fun X => Iso.refl X)
    (by
      intro X Y f
      apply Hom_ext
      · rfl
      · intro i
        with_unfolding_all
          exact heq_of_eq (by
            change (f.hom i ≫ 𝟙 _) = (𝟙 _ ≫ f.hom i)
            simp))

@[simp]
theorem mapIdIso_hom_app (C : Type u₁) [Category.{v₁} C]
    (X : FiniteFamily C) :
    (mapIdIso C).hom.app X = 𝟙 X :=
  rfl

@[simp]
theorem mapIdIso_inv_app (C : Type u₁) [Category.{v₁} C]
    (X : FiniteFamily C) :
    (mapIdIso C).inv.app X = 𝟙 X :=
  rfl

/-- The canonical isomorphism `map (F ⋙ G) ≅ map F ⋙ map G`.

It is definitionally `Iso.refl` because `FiniteFamily.map` acts pointwise. -/
def mapCompIso {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ D) :
    FiniteFamily.map (F ⋙ G) ≅ FiniteFamily.map F ⋙ FiniteFamily.map G :=
  Iso.refl _

@[simp]
theorem mapCompIso_hom_app {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ D) (X : FiniteFamily C₁) :
    (mapCompIso F G).hom.app X = 𝟙 _ := rfl

@[simp]
theorem mapCompIso_inv_app {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ D) (X : FiniteFamily C₁) :
    (mapCompIso F G).inv.app X = 𝟙 _ := rfl

/-- Singleton functor `C ⥤ FiniteFamily C`. -/
def singleton : C ⥤ FiniteFamily C where
  obj c := ⟨FintypeCat.of PUnit, fun _ => c⟩
  map {X Y} f :=
    { equiv := Equiv.refl PUnit
      hom := fun _ => f }
  map_id X := by
    apply Hom_ext
    · rfl
    · intro x
      rfl
  map_comp {X Y Z} f g := by
    apply Hom_ext
    · rfl
    · intro x
      rfl

/-- The empty finite family. -/
def empty {C : Type u₁} : FiniteFamily C where
  index := FintypeCat.of Empty
  obj := fun e => e.elim

/-- Mapping the empty finite family along a functor yields the empty finite family. -/
def mapEmptyIso {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D]
    (F : C₁ ⥤ D) :
    (FiniteFamily.map F).obj (FiniteFamily.empty : FiniteFamily C₁) ≅
      (FiniteFamily.empty : FiniteFamily D) where
  hom :=
    { equiv := Equiv.refl Empty
      hom := fun e => e.elim }
  inv :=
    { equiv := Equiv.refl Empty
      hom := fun e => e.elim }
  hom_inv_id := by
    apply Hom_ext
    · rfl
    · intro x
      cases x
  inv_hom_id := by
    apply Hom_ext
    · rfl
    · intro x
      cases x

/-- Flattening functor `FiniteFamily (FiniteFamily C) ⥤ FiniteFamily C`
indexed by dependent sums. -/
def flatten : FiniteFamily (FiniteFamily C) ⥤ FiniteFamily C where
  obj X :=
    let total : Type := (a : X.index) × (X.obj a).index
    haveI : Finite X.index := X.index.property
    haveI : (a : X.index) → Finite (X.obj a).index := fun a => (X.obj a).index.property
    haveI : Finite total := by infer_instance
    ⟨FintypeCat.of total, fun p => (X.obj p.1).obj p.2⟩
  map {X Y} f :=
    { equiv := Equiv.sigmaCongr f.equiv (fun a => (f.hom a).equiv)
      hom := fun p => (f.hom p.1).hom p.2 }
  map_id X := by
    apply Hom_ext
    · apply Equiv.ext
      intro x
      cases x with
      | mk _ _ => rfl
    · intro x
      cases x with
      | mk _ _ => rfl
  map_comp {X Y Z} f g := by
    apply Hom_ext
    · apply Equiv.ext
      intro x
      cases x with
      | mk _ _ => rfl
    · intro x
      cases x with
      | mk _ _ => rfl

@[simp]
theorem flatten_map_equiv {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    ((flatten (C := C)).map f).equiv = Equiv.sigmaCongr f.equiv (fun a => (f.hom a).equiv) :=
  rfl

@[simp]
theorem flatten_map_hom {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (p : (FiniteFamily.flatten (C := C)).obj X |>.index) :
    ((flatten (C := C)).map f).hom p = (f.hom p.1).hom p.2 :=
  rfl

end FiniteFamily

end CategoryTheory
