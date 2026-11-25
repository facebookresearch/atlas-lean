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

public import MathlibExt.CategoryTheory.Operad.Colored.Collection
public import MathlibExt.CategoryTheory.Operad.OperadObj.Indexing

/-!
# Color-matching substitution data

A colored substitution datum is a root output color together with a finite family of inner
profiles. The outer profile is derived by using the inner output colors as its input colors, so all
color-matching conditions hold definitionally.

This family-normal form reuses the existing `FiniteFamily` category and flattening APIs. It is the
indexing layer for colored operadic substitution and has no monoidal, simplicial, or model-category
hypotheses.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe u v

/-- A color-matched simultaneous-substitution shape. -/
structure ColoredSubstitutionData (Color : Type u) where
  /-- The output color of the outer profile. -/
  outputColor : Color
  /-- The finite family of inner profiles. Their output colors determine the outer input colors. -/
  inner : FiniteFamily (ColoredProfile Color)

namespace ColoredSubstitutionData

variable {Color : Type u} {Color' : Type v}

/-- The outer profile determined by the inner output colors. -/
def outerProfile (d : ColoredSubstitutionData Color) : ColoredProfile Color where
  inputs := d.inner.index
  inputColor i := (d.inner.obj i).outputColor
  outputColor := d.outputColor

/-- Forget the colors from a colored substitution datum. -/
def toSubstitutionData (d : ColoredSubstitutionData Color) : SubstitutionData where
  index := d.inner.index
  obj i := ⟨(d.inner.obj i).inputs⟩

/-- The profile obtained by replacing every outer input by the inputs of its inner profile. -/
def totalProfile (d : ColoredSubstitutionData Color) : ColoredProfile Color where
  inputs := substitutionTotalObj d.toSubstitutionData
  inputColor p := (d.inner.obj p.1).inputColor p.2
  outputColor := d.outputColor

@[simp]
theorem outerProfile_inputColor (d : ColoredSubstitutionData Color) (i : d.inner.index) :
    d.outerProfile.inputColor i = (d.inner.obj i).outputColor :=
  rfl

@[simp]
theorem outerProfile_outputColor (d : ColoredSubstitutionData Color) :
    d.outerProfile.outputColor = d.outputColor :=
  rfl

@[simp]
theorem totalProfile_inputColor (d : ColoredSubstitutionData Color)
    (i : d.inner.index) (j : (d.inner.obj i).inputs) :
    d.totalProfile.inputColor ⟨i, j⟩ = (d.inner.obj i).inputColor j :=
  rfl

@[simp]
theorem totalProfile_outputColor (d : ColoredSubstitutionData Color) :
    d.totalProfile.outputColor = d.outputColor :=
  rfl

/-- Morphisms preserve the root output color and relabel the finite family of inner profiles. -/
@[ext]
structure Hom (d e : ColoredSubstitutionData Color) where
  /-- Equality of root output colors. -/
  outputColor_eq : d.outputColor = e.outputColor
  /-- Relabelling of the inner profiles. -/
  innerHom : d.inner ⟶ e.inner

namespace Hom

variable {d e f : ColoredSubstitutionData Color}

/-- Identity morphism of colored substitution data. -/
def refl (d : ColoredSubstitutionData Color) : Hom d d where
  outputColor_eq := rfl
  innerHom := 𝟙 d.inner

/-- Composition of morphisms of colored substitution data. -/
def trans (p : Hom d e) (q : Hom e f) : Hom d f where
  outputColor_eq := p.outputColor_eq.trans q.outputColor_eq
  innerHom := p.innerHom ≫ q.innerHom

end Hom

instance instCategory : Category (ColoredSubstitutionData Color) where
  Hom := Hom
  id := Hom.refl
  comp := Hom.trans
  id_comp := by
    intro d e f
    apply Hom.ext
    exact Category.id_comp f.innerHom
  comp_id := by
    intro d e f
    apply Hom.ext
    exact Category.comp_id f.innerHom
  assoc := by
    intro a b c d f g h
    apply Hom.ext
    exact Category.assoc f.innerHom g.innerHom h.innerHom

@[simp]
theorem id_innerHom (d : ColoredSubstitutionData Color) :
    (𝟙 d : d ⟶ d).innerHom = 𝟙 d.inner :=
  rfl

@[simp]
theorem comp_innerHom {d e f : ColoredSubstitutionData Color} (p : d ⟶ e) (q : e ⟶ f) :
    (p ≫ q).innerHom = p.innerHom ≫ q.innerHom :=
  rfl

/-- The morphism induced on outer profiles. -/
def outerProfileMap {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    d.outerProfile ⟶ e.outerProfile where
  inputEquiv := f.innerHom.equiv
  inputColor_eq := fun i => (f.innerHom.hom i).outputColor_eq
  outputColor_eq := f.outputColor_eq

/-- The outer profile is functorial. -/
def outerProfileFunctor : ColoredSubstitutionData Color ⥤ ColoredProfile Color where
  obj := outerProfile
  map := outerProfileMap
  map_id _ := by
    apply ColoredProfile.Hom.ext
    rfl
  map_comp _ _ := by
    apply ColoredProfile.Hom.ext
    rfl

@[simp]
theorem outerProfileFunctor_obj (d : ColoredSubstitutionData Color) :
    outerProfileFunctor.obj d = d.outerProfile :=
  rfl

@[simp]
theorem outerProfileFunctor_map_inputEquiv {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (outerProfileFunctor.map f).inputEquiv = f.innerHom.equiv :=
  rfl

theorem outerProfileMap_comp {d e f : ColoredSubstitutionData Color}
    (p : d ⟶ e) (q : e ⟶ f) :
    outerProfileMap (p ≫ q) = outerProfileMap p ≫ outerProfileMap q := by
  apply ColoredProfile.Hom.ext
  rfl

/-- Forgetting all colors is functorial. -/
abbrev toSubstitutionDataFunctor : ColoredSubstitutionData Color ⥤ SubstitutionData where
  obj := toSubstitutionData
  map f :=
    { equiv := f.innerHom.equiv
      hom := fun i => FinBijGroupoid.homOfEquiv (f.innerHom.hom i).inputEquiv }
  map_id d := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      rfl
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      rfl

@[simp]
theorem toSubstitutionDataFunctor_obj (d : ColoredSubstitutionData Color) :
    toSubstitutionDataFunctor.obj d = d.toSubstitutionData :=
  rfl

/-- The morphism induced on flattened total profiles. -/
def totalProfileMap {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    d.totalProfile ⟶ e.totalProfile where
  inputEquiv := Equiv.sigmaCongr f.innerHom.equiv
    (fun i => (f.innerHom.hom i).inputEquiv)
  inputColor_eq := fun p => (f.innerHom.hom p.1).inputColor_eq p.2
  outputColor_eq := f.outputColor_eq

/-- Flattening a substitution datum is functorial. -/
def totalProfileFunctor : ColoredSubstitutionData Color ⥤ ColoredProfile Color where
  obj := totalProfile
  map := totalProfileMap
  map_id d := by
    apply ColoredProfile.Hom.ext
    rfl
  map_comp f g := by
    apply ColoredProfile.Hom.ext
    apply Equiv.ext
    intro p
    rcases p with ⟨i, j⟩
    rfl

@[simp]
theorem totalProfileFunctor_obj (d : ColoredSubstitutionData Color) :
    totalProfileFunctor.obj d = d.totalProfile :=
  rfl

@[simp]
theorem totalProfileFunctor_map {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    totalProfileFunctor.map f = totalProfileMap f :=
  rfl

@[simp]
theorem totalProfileFunctor_map_inputEquiv {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (totalProfileFunctor.map f).inputEquiv =
      Equiv.sigmaCongr f.innerHom.equiv (fun i => (f.innerHom.hom i).inputEquiv) :=
  rfl

@[simp]
theorem totalProfileMap_id (d : ColoredSubstitutionData Color) :
    totalProfileMap (𝟙 d) = 𝟙 d.totalProfile := by
  apply ColoredProfile.Hom.ext
  rfl

theorem totalProfileMap_comp {d e f : ColoredSubstitutionData Color}
    (p : d ⟶ e) (q : e ⟶ f) :
    totalProfileMap (p ≫ q) = totalProfileMap p ≫ totalProfileMap q := by
  apply ColoredProfile.Hom.ext
  apply Equiv.ext
  rintro ⟨i, j⟩
  rfl

/-- The finite family of inner profiles is functorial. -/
def innerFamilyFunctor :
    ColoredSubstitutionData Color ⥤ FiniteFamily (ColoredProfile Color) where
  obj d := d.inner
  map f := f.innerHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The finite index type consisting of the outer profile and all inner profiles. -/
def factorIndex (d : ColoredSubstitutionData Color) : FintypeCat.{0} :=
  substitutionFactorIndex d.toSubstitutionData

/-- The outer profile together with all inner profiles. -/
def factorFamily (d : ColoredSubstitutionData Color) : FiniteFamily (ColoredProfile Color) where
  index := d.factorIndex
  obj
    | none => d.outerProfile
    | some i => d.inner.obj i

/-- The outer factor index. -/
def factorOuterIndex (d : ColoredSubstitutionData Color) : d.factorFamily.index :=
  none

/-- The inner factor index corresponding to an outer input. -/
def factorInnerIndex (d : ColoredSubstitutionData Color) (i : d.inner.index) :
    d.factorFamily.index :=
  some i

/-- The outer profile and all inner profiles, functorially in substitution data. -/
def factorFamilyFunctor :
    ColoredSubstitutionData Color ⥤ FiniteFamily (ColoredProfile Color) where
  obj := factorFamily
  map f :=
    { equiv := Equiv.optionCongr f.innerHom.equiv
      hom := fun o =>
        match o with
        | none => outerProfileMap f
        | some i => f.innerHom.hom i }
  map_id d := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o <;> rfl
    · intro o
      cases o <;> exact heq_of_eq (by
        apply ColoredProfile.Hom.ext
        rfl)
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o <;> rfl
    · intro o
      cases o with
      | none => exact heq_of_eq (outerProfileMap_comp f g)
      | some i => exact heq_of_eq rfl

@[simp]
theorem factorFamilyFunctor_map_equiv {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (factorFamilyFunctor.map f).equiv = Equiv.optionCongr f.innerHom.equiv :=
  rfl

@[simp]
theorem factorFamilyFunctor_map_outer {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (factorFamilyFunctor.map f).hom (factorOuterIndex d) = outerProfileMap f :=
  rfl

@[simp]
theorem factorFamilyFunctor_map_inner {d e : ColoredSubstitutionData Color} (f : d ⟶ e)
    (i : d.inner.index) :
    (factorFamilyFunctor.map f).hom (factorInnerIndex d i) = f.innerHom.hom i :=
  rfl

/-- Apply a function to every color in a substitution datum. -/
def mapColors (f : Color → Color') (d : ColoredSubstitutionData Color) :
    ColoredSubstitutionData Color' where
  outputColor := f d.outputColor
  inner := (FiniteFamily.map (ColoredProfile.mapColorsFunctor f)).obj d.inner

/-- Apply a function to every color in a morphism of substitution data. -/
def Hom.mapColors (f : Color → Color') {d e : ColoredSubstitutionData Color} (g : d ⟶ e) :
    d.mapColors f ⟶ e.mapColors f where
  outputColor_eq := congrArg f g.outputColor_eq
  innerHom := (FiniteFamily.map (ColoredProfile.mapColorsFunctor f)).map g.innerHom

/-- Applying a function to every color is functorial on substitution data. -/
def mapColorsFunctor (f : Color → Color') :
    ColoredSubstitutionData Color ⥤ ColoredSubstitutionData Color' where
  obj d := d.mapColors f
  map g := g.mapColors f
  map_id d := by
    apply Hom.ext
    exact (FiniteFamily.map (ColoredProfile.mapColorsFunctor f)).map_id d.inner
  map_comp g h := by
    apply Hom.ext
    exact (FiniteFamily.map (ColoredProfile.mapColorsFunctor f)).map_comp g.innerHom h.innerHom

@[simp]
theorem mapColorsFunctor_obj (f : Color → Color') (d : ColoredSubstitutionData Color) :
    (mapColorsFunctor f).obj d = d.mapColors f :=
  rfl

@[simp]
theorem mapColorsFunctor_id : mapColorsFunctor (id : Color → Color) = 𝟭 _ :=
  rfl

@[simp]
theorem mapColorsFunctor_comp {Color'' : Type*} (f : Color → Color') (g : Color' → Color'') :
    mapColorsFunctor f ⋙ mapColorsFunctor g = mapColorsFunctor (g ∘ f) :=
  rfl

@[simp]
theorem mapColors_outerProfileFunctor (f : Color → Color') :
    mapColorsFunctor f ⋙ outerProfileFunctor =
      outerProfileFunctor ⋙ ColoredProfile.mapColorsFunctor f :=
  rfl

@[simp]
theorem mapColors_totalProfileFunctor (f : Color → Color') :
    mapColorsFunctor f ⋙ totalProfileFunctor =
      totalProfileFunctor ⋙ ColoredProfile.mapColorsFunctor f :=
  rfl

end ColoredSubstitutionData

end CategoryTheory.Operad
