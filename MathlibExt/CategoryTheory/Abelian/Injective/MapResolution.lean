/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import MathlibExt.CategoryTheory.Abelian.Injective.ResolutionComparison

/-!
# Mapping injective resolutions

Let `C`, `D` be preadditive categories with zero objects, and suppose `D`
has homology. An additive functor `F : C → D` preserving homology and
injective objects carries an injective resolution of `Z` to one of `F(Z)`.
It also carries augmentation-compatible resolution morphisms to such morphisms.
-/

/-
Authorship of the adapted portions: @toskua, Avocado.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]

/-- Let `C`, `D` be preadditive categories with zero objects and with
homology in `D`. If additive `F : C → D` preserves homology and
injective objects, an injective resolution `I` of `Z ∈ C` maps to
an injective resolution of `F(Z)` in `D`. -/
@[simps cocomplex ι]
noncomputable def mapInjectiveResolution (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {Z : C} (I : InjectiveResolution Z) : InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex _).obj I.cocomplex
  injective n := PreservesInjectiveObjects.injective_obj (I.injective n)
  hasHomology _ := inferInstance
  ι := (HomologicalComplex.singleMapHomologicalComplex _ _ _).inv.app _ ≫
    (F.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- For preadditive `C`, `D` with zero objects and homology in `D`, let
additive `F : C → D` preserve homology and injectives. A resolution
map `φ : I → J` over `f : X → Y` then gives an injective-resolution
map `F(I) → F(J)` over `F(f)`, with the mapped cochain map and augmentation. -/
noncomputable def mapInjectiveResolutionHom (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {X Y : C} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    {f : X ⟶ Y} (φ : InjectiveResolution.Hom I J f) :
    InjectiveResolution.Hom (F.mapInjectiveResolution I)
      (F.mapInjectiveResolution J) (F.map f) where
  hom := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    have hφ := φ.ι_comp_hom
    change I.ι ≫ φ.hom =
      (HomologicalComplex.single C (ComplexShape.up ℕ) 0).map f ≫ J.ι at hφ
    have hn := (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℕ) 0).inv.naturality f
    change (HomologicalComplex.single D (ComplexShape.up ℕ) 0).map (F.map f) ≫
        (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℕ) 0).inv.app Y =
      (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℕ) 0).inv.app X ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map f) at hn
    have h : ((HomologicalComplex.singleMapHomologicalComplex F
        (ComplexShape.up ℕ) 0).inv.app X ≫
          (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom =
      (HomologicalComplex.single D (ComplexShape.up ℕ) 0).map (F.map f) ≫
        ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℕ) 0).inv.app Y ≫
          (F.mapHomologicalComplex (ComplexShape.up ℕ)).map J.ι) := by
      rw [Category.assoc, ← Functor.map_comp,
        hφ, Functor.map_comp, ← Category.assoc,
        ← hn,
        Category.assoc]
    change (((HomologicalComplex.singleMapHomologicalComplex F
        (ComplexShape.up ℕ) 0).inv.app X ≫
          (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom).f 0 =
      ((HomologicalComplex.single D (ComplexShape.up ℕ) 0).map (F.map f) ≫
        ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℕ) 0).inv.app Y ≫
          (F.mapHomologicalComplex (ComplexShape.up ℕ)).map J.ι)).f 0
    exact HomologicalComplex.congr_hom h 0

@[simp]
theorem mapInjectiveResolutionHom_hom (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {X Y : C} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    {f : X ⟶ Y} (φ : InjectiveResolution.Hom I J f) :
    (F.mapInjectiveResolutionHom φ).hom =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom :=
  rfl

@[simp]
theorem mapInjectiveResolutionHom_id (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {X : C} (I : InjectiveResolution X) :
    (F.mapInjectiveResolutionHom (InjectiveResolution.Hom.id I)).cast
        (F.map_id X) =
      InjectiveResolution.Hom.id (F.mapInjectiveResolution I) := by
  apply InjectiveResolution.Hom.ext
  exact (F.mapHomologicalComplex (ComplexShape.up ℕ)).map_id I.cocomplex

@[simp]
theorem mapInjectiveResolutionHom_comp (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {X Y Z : C} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    {K : InjectiveResolution Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    (φ : InjectiveResolution.Hom I J f)
    (ψ : InjectiveResolution.Hom J K g) :
    (F.mapInjectiveResolutionHom (φ.comp ψ)).cast (F.map_comp f g) =
      (F.mapInjectiveResolutionHom φ).comp (F.mapInjectiveResolutionHom ψ) := by
  apply InjectiveResolution.Hom.ext
  exact (F.mapHomologicalComplex (ComplexShape.up ℕ)).map_comp φ.hom ψ.hom

end CategoryTheory.Functor

end
