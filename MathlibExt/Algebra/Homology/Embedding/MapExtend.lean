/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Functoriality of zero extension of complexes

A functor preserving zero morphisms commutes, up to a natural isomorphism,
with zero extension along an embedding of complex shapes. The component
comparison is the identity on retained degrees and the zero-object
comparison outside the embedding image.
-/

public section

open CategoryTheory Category Limits

universe v u v' u'

namespace CategoryTheory.Functor

private noncomputable def mapExtendAuxIso
    {ι : Type u} {c : ComplexShape ι}
    {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (x : Option ι) :
    HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) x ≅
      F.obj (HomologicalComplex.extend.X K x) :=
  match x with
  | some _ => Iso.refl _
  | none => F.mapZeroObject.symm

private theorem mapExtendAuxDEq
    {ι : Type u} {c : ComplexShape ι}
    {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (x y : Option ι) :
    (mapExtendAuxIso F K x).hom ≫ F.map (HomologicalComplex.extend.d K x y) =
      HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) x y ≫
        (mapExtendAuxIso F K y).hom := by
  match x with
  | none =>
    exact (Limits.isZero_zero D).eq_of_src _ _
  | some _ =>
    match y with
    | none =>
      exact (F.map_isZero (Limits.isZero_zero C)).eq_of_tgt _ _
    | some _ =>
      simp only [mapExtendAuxIso, HomologicalComplex.extend.X,
        HomologicalComplex.extend.d, mapHomologicalComplex,
        Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem mapExtendAuxMapEq
    {ι : Type u} {c : ComplexShape ι}
    {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (x : Option ι) :
    HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) x ≫
        (mapExtendAuxIso F L x).hom =
      (mapExtendAuxIso F K x).hom ≫ F.map (HomologicalComplex.extend.mapX φ x) := by
  match x with
  | none =>
    exact (Limits.isZero_zero D).eq_of_src _ _
  | some _ =>
    simp only [mapExtendAuxIso, HomologicalComplex.extend.X,
      HomologicalComplex.extend.mapX, mapHomologicalComplex,
      Iso.refl_hom, Category.id_comp, Category.comp_id]

private noncomputable def mapExtendObjIso
    {ι : Type u} {ι' : Type u'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (e : c.Embedding c') (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c ⋙ e.extendFunctor D).obj K ≅
      (e.extendFunctor C ⋙ F.mapHomologicalComplex c').obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i' => by
      change HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) (e.r i') ≅
        F.obj (HomologicalComplex.extend.X K (e.r i'))
      exact mapExtendAuxIso F K (e.r i'))
    (fun i' j' _ => by
      change (mapExtendAuxIso F K (e.r i')).hom ≫
          F.map (HomologicalComplex.extend.d K (e.r i') (e.r j')) =
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) (e.r i')
          (e.r j') ≫ (mapExtendAuxIso F K (e.r j')).hom
      exact mapExtendAuxDEq F K (e.r i') (e.r j'))

/-- A functor `F` preserving zero morphisms between categories with zero objects
and zero morphisms gives a natural isomorphism from applying `F` degreewise
and then extending by zero along `e` to extending by zero along `e` and then
applying `F` degreewise. Its components use the identity in degrees in the
image of `e` and the zero-object comparison outside that image. -/
noncomputable def mapHomologicalComplexExtendIso
    {ι : Type u} {ι' : Type u'} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {C : Type v} [Category C]
    [HasZeroMorphisms C] [HasZeroObject C] {D : Type v'} [Category D]
    [HasZeroMorphisms D] [HasZeroObject D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (e : c.Embedding c') :
    F.mapHomologicalComplex c ⋙ e.extendFunctor D ≅
      e.extendFunctor C ⋙ F.mapHomologicalComplex c' :=
  NatIso.ofComponents
    (fun K => mapExtendObjIso F e K)
    (fun {K L} φ => by
      ext i'
      change HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ)
          (e.r i') ≫ (mapExtendAuxIso F L (e.r i')).hom =
        (mapExtendAuxIso F K (e.r i')).hom ≫
          F.map (HomologicalComplex.extend.mapX φ (e.r i'))
      exact mapExtendAuxMapEq F φ (e.r i'))

private theorem mapExtendAuxIso_hom_comp
    {ι : Type u} {c : ComplexShape ι}
    {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (x : Option ι) (j : ι)
    (h : x = some j) :
    (mapExtendAuxIso F K x).hom ≫
        F.map (HomologicalComplex.extend.XIso K h).hom =
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) h).hom := by
  cases h
  change 𝟙 (F.obj (K.X j)) ≫ F.map (𝟙 (K.X j)) = 𝟙 (F.obj (K.X j))
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- In a degree `j'` in the image of `j` under `e`, composing the forward
comparison on `K` with the image under `F` of the zero-extension component
identification for `K` gives the component identification for the complex
obtained by applying `F` to `K` degreewise. -/
theorem mapHomologicalComplexExtendIso_hom_app_f
    {ι : Type u} {ι' : Type u'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (e : c.Embedding c') (K : HomologicalComplex C c)
    (j : ι) (j' : ι') (hj : e.f j = j') :
    ((mapHomologicalComplexExtendIso F e).hom.app K).f j' ≫
        F.map (K.extendXIso e hj).hom =
      (((F.mapHomologicalComplex c).obj K).extendXIso e hj).hom := by
  subst j'
  change (mapExtendAuxIso F K (e.r (e.f j))).hom ≫
      F.map (HomologicalComplex.extend.XIso K (e.r_eq_some rfl)).hom =
    (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K)
      (e.r_eq_some rfl)).hom
  exact mapExtendAuxIso_hom_comp F K (e.r (e.f j)) j (e.r_eq_some rfl)

end CategoryTheory.Functor
