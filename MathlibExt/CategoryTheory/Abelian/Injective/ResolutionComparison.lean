/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/- Proof implementation note.
# Bundled comparison maps of injective resolutions

This file packages Mathlib's comparison map between injective resolutions
together with its augmentation equation. Identity, composition, transport,
and coherence are operations on already chosen comparison maps. The canonical
`descHom` remains noncanonical and no strict identity or composition law is
asserted for that choice.
-/

/-!
# Comparison morphisms of injective resolutions

In a category `C` with a zero object and zero morphisms, augmentation-compatible
cochain maps between injective resolutions form identity and composite
resolution morphisms. In an abelian category, every map between resolved
objects lifts to a comparison morphism between their chosen resolutions.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.InjectiveResolution

section HomAlgebra

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C]
  [Limits.HasZeroMorphisms C]

namespace Hom

/-- In a category `C` with a zero object and zero morphisms, two
injective-resolution morphisms `φ,ψ : I → I′` over the same
map `f : X → Y` are equal if their underlying cochain maps are equal. -/
@[ext]
theorem ext {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f : Z ⟶ Z'} {φ ψ : Hom I I' f}
    (h : φ.hom = ψ.hom) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- For a injective resolution `I` of `Z` in a category `C` with
a zero object and zero morphisms, the identity cochain map is an
augmentation-compatible resolution morphism over `𝟙 Z`. -/
def id {Z : C} (I : InjectiveResolution Z) : Hom I I (𝟙 Z) where
  hom := 𝟙 I.cocomplex
  ι_f_zero_comp_hom_f_zero := by
    rw [HomologicalComplex.id_f, Functor.map_id,
      HomologicalComplex.id_f, Category.comp_id, Category.id_comp]

@[simp]
theorem id_hom {Z : C} (I : InjectiveResolution Z) :
    (Hom.id I).hom = 𝟙 I.cocomplex :=
  rfl

/-- In a category `C` with a zero object and zero morphisms,
injective-resolution maps `φ : I → I′` over `f : Z → Z′`
and `ψ : I′ → I″` over `g : Z′ → Z″` compose to a
resolution map over `f ≫ g` with the composite cochain map. -/
def comp {Z Z' Z'' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {I'' : InjectiveResolution Z''}
    {f : Z ⟶ Z'} {g : Z' ⟶ Z''}
    (φ : Hom I I' f) (ψ : Hom I' I'' g) : Hom I I'' (f ≫ g) where
  hom := φ.hom ≫ ψ.hom
  ι_f_zero_comp_hom_f_zero := by
    rw [HomologicalComplex.comp_f, ← Category.assoc,
      φ.ι_f_zero_comp_hom_f_zero, Category.assoc,
      ψ.ι_f_zero_comp_hom_f_zero, ← Category.assoc,
      ← HomologicalComplex.comp_f, ← Functor.map_comp]

@[simp]
theorem comp_hom {Z Z' Z'' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {I'' : InjectiveResolution Z''}
    {f : Z ⟶ Z'} {g : Z' ⟶ Z''}
    (φ : Hom I I' f) (ψ : Hom I' I'' g) :
    (φ.comp ψ).hom = φ.hom ≫ ψ.hom :=
  rfl

/-- For injective resolutions `I`, `I′` in a category `C` with
a zero object and zero morphisms, identifying equal resolved maps
`f=f′ : Z → Z′` transports a resolution map over `f` to one over
`f′`, without changing its underlying cochain map. -/
def cast {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f f' : Z ⟶ Z'}
    (φ : Hom I I' f) (h : f = f') : Hom I I' f' where
  hom := φ.hom
  ι_f_zero_comp_hom_f_zero := by
    rw [← h]
    exact φ.ι_f_zero_comp_hom_f_zero

@[simp]
theorem cast_hom {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f f' : Z ⟶ Z'}
    (φ : Hom I I' f) (h : f = f') :
    (φ.cast h).hom = φ.hom :=
  rfl

@[simp]
theorem cast_rfl {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f : Z ⟶ Z'} (φ : Hom I I' f) :
    φ.cast rfl = φ :=
  rfl

@[simp]
theorem cast_cast {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f f' f'' : Z ⟶ Z'}
    (φ : Hom I I' f) (h : f = f') (h' : f' = f'') :
    (φ.cast h).cast h' = φ.cast (h.trans h') := by
  ext
  simp

/-- For injective-resolution maps in a category `C` with a zero
object and zero morphisms, composing the identity of the source
resolution with a map `φ` gives `φ`, after identifying the
resolved map `𝟙 ≫ f` with `f`. -/
theorem id_comp {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f : Z ⟶ Z'} (φ : Hom I I' f) :
    ((Hom.id I).comp φ).cast (Category.id_comp f) = φ := by
  ext
  simp

/-- For injective-resolution maps in a category `C` with a zero
object and zero morphisms, composing a map `φ` with the identity
of its target resolution gives `φ`, after identifying `f ≫ 𝟙` with `f`. -/
theorem comp_id {Z Z' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {f : Z ⟶ Z'} (φ : Hom I I' f) :
    (φ.comp (Hom.id I')).cast (Category.comp_id f) = φ := by
  ext
  simp

/-- In a category `C` with a zero object and zero morphisms,
composition of three injective-resolution morphisms is associative
after the canonical identification of `(f ≫ g) ≫ h` with
`f ≫ (g ≫ h)` on resolved objects. -/
theorem assoc {Z Z' Z'' Z''' : C} {I : InjectiveResolution Z}
    {I' : InjectiveResolution Z'} {I'' : InjectiveResolution Z''}
    {I''' : InjectiveResolution Z'''} {f : Z ⟶ Z'} {g : Z' ⟶ Z''}
    {h : Z'' ⟶ Z'''} (φ : Hom I I' f) (ψ : Hom I' I'' g)
    (χ : Hom I'' I''' h) :
    ((φ.comp ψ).comp χ).cast (Category.assoc f g h) =
      φ.comp (ψ.comp χ) := by
  ext
  simp

end Hom

end HomAlgebra

section DescHom

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
Mathlib's chosen comparison map, bundled with its augmentation equation.

This choice is not asserted to preserve identities or composition strictly.
-/

/-- In an abelian category `C`, a map `f : X → Y` lifts to an
augmentation-compatible cochain comparison between any chosen
injective resolution of `X` and injective resolution of `Y`. -/
noncomputable def descHom
    {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    InjectiveResolution.Hom I J f where
  hom := InjectiveResolution.desc f J I
  ι_f_zero_comp_hom_f_zero := by
    simpa only [CochainComplex.single₀_map_f_zero] using
      InjectiveResolution.desc_commutes_zero f J I

@[simp]
theorem descHom_hom {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    (descHom f I J).hom = InjectiveResolution.desc f J I :=
  rfl

end DescHom

end CategoryTheory.InjectiveResolution

end
