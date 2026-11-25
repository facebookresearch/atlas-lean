/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Bifunctor/Basic.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.Algebra.Homology.Bifunctor

/-!
# Functoriality of bifunctor totalizations

Fixing a left complex needs totalizations only for that complex and the right arguments.
`CategoryTheory.Functor.mapBifunctorLeft` and its maps in the left variable use Mathlib's
pairwise totalization and its existing maps. When all totalizations exist, this is the left
component of Mathlib's totalized bifunctor. The totalized bifunctor preserves zero morphisms.

The identity and composition calculations were previously in
`TauCeti.Algebra.Homology.Bifunctor.Homotopy` (not ported here); that module reuses them for
homotopy equivalences.
All constructions use Joël Riou's Mathlib bifunctor totalization in
`Mathlib.Algebra.Homology.Bifunctor` and `Mathlib.Algebra.Homology.TotalComplex`.
-/

public section
noncomputable section

open CategoryTheory Limits

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace HomologicalComplex

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- `mapBifunctorMap` sends the pair of identities to the identity. -/
@[simp]
lemma mapBifunctorMap_id (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
    [HasMapBifunctor K₁ K₂ F c] :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 _ := by
  ext
  simp

/-- `mapBifunctorMap` is compatible with composition in both variables simultaneously. -/
@[reassoc]
lemma mapBifunctorMap_comp {K₁ L₁ M₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ M₂ : HomologicalComplex C₂ c₂} [HasMapBifunctor K₁ K₂ F c]
    [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor M₁ M₂ F c]
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c =
      mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c := by
  ext
  simp [NatTrans.naturality_assoc]

/-- Totalization sends a zero morphism in the left argument to zero. -/
@[simp]
theorem mapBifunctorMap_zero_left (K L : HomologicalComplex C₁ c₁)
    {N N' : HomologicalComplex C₂ c₂} (g : N ⟶ N')
    [HasMapBifunctor K N F c] [HasMapBifunctor L N' F c] :
    mapBifunctorMap (0 : K ⟶ L) g F c = 0 := by
  apply Hom.ext
  funext j
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [ι_mapBifunctorMap, zero_f, Functor.map_zero, NatTrans.app_zero,
    zero_comp, comp_zero]

/-- Totalization sends a zero morphism in the right argument to zero. -/
@[simp]
theorem mapBifunctorMap_zero_right {K L : HomologicalComplex C₁ c₁} (f : K ⟶ L)
    (N N' : HomologicalComplex C₂ c₂)
    [HasMapBifunctor K N F c] [HasMapBifunctor L N' F c] :
    mapBifunctorMap f (0 : N ⟶ N') F c = 0 := by
  apply Hom.ext
  funext j
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [ι_mapBifunctorMap, zero_f, Functor.map_zero, comp_zero, zero_comp]


end HomologicalComplex


namespace CategoryTheory.Functor

open HomologicalComplex

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  (c₂ : ComplexShape I₂) (c : ComplexShape J)
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- Totalization against a fixed left complex, requiring only its own totalizations. -/
-- The structural abbreviation keeps its object assignment equal to mapBifunctor, so its
-- morphisms have the existing pairwise totalization-map types without object transports.
abbrev mapBifunctorLeft (K : HomologicalComplex C₁ c₁)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c] :
    HomologicalComplex C₂ c₂ ⥤ HomologicalComplex D c where
  obj N := mapBifunctor K N F c
  map g := mapBifunctorMap (𝟙 K) g F c
  map_id N := mapBifunctorMap_id F c K N
  map_comp f g := by
    simpa only [Category.id_comp] using mapBifunctorMap_comp F c (𝟙 K) (𝟙 K) f g

/-- The object of a fixed-left totalization is the corresponding pairwise total complex. -/
@[simp]
theorem mapBifunctorLeft_obj (K : HomologicalComplex C₁ c₁)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c]
    (N : HomologicalComplex C₂ c₂) :
    (F.mapBifunctorLeft c₂ c K).obj N = mapBifunctor K N F c := (rfl)

/-- Maps of a fixed-left totalization use the identity on the left complex. -/
@[simp]
theorem mapBifunctorLeft_map (K : HomologicalComplex C₁ c₁)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c]
    {N N' : HomologicalComplex C₂ c₂} (g : N ⟶ N') :
    (F.mapBifunctorLeft c₂ c K).map g = mapBifunctorMap (𝟙 K) g F c := (rfl)

/-- The fixed-left totalization preserves zero morphisms in its right argument. -/
instance mapBifunctorLeft_preservesZeroMorphisms (K : HomologicalComplex C₁ c₁)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c] :
    (F.mapBifunctorLeft c₂ c K).PreservesZeroMorphisms where
  map_zero N N' := HomologicalComplex.mapBifunctorMap_zero_right F c (𝟙 K) N N'

/-- A map of the chosen left complexes induces a natural map of their totalizations. -/
def mapBifunctorLeftMap {K L : HomologicalComplex C₁ c₁} (f : K ⟶ L)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c]
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor L N F c] :
    F.mapBifunctorLeft c₂ c K ⟶ F.mapBifunctorLeft c₂ c L where
  app N := mapBifunctorMap f (𝟙 N) F c
  naturality N N' g := by
    dsimp only [mapBifunctorLeft]
    rw [← mapBifunctorMap_comp, ← mapBifunctorMap_comp]
    simp only [Category.id_comp, Category.comp_id]

/-- The component of a map between fixed-left totalizations is the pairwise totalization map. -/
@[simp]
theorem mapBifunctorLeftMap_app {K L : HomologicalComplex C₁ c₁} (f : K ⟶ L)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c]
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor L N F c]
    (N : HomologicalComplex C₂ c₂) :
    (F.mapBifunctorLeftMap c₂ c f).app N = mapBifunctorMap f (𝟙 N) F c := (rfl)

/-- Maps between fixed-left totalizations preserve composition in the left argument. -/
@[reassoc]
theorem mapBifunctorLeftMap_comp {K L M : HomologicalComplex C₁ c₁}
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c]
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor L N F c]
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor M N F c]
    (f : K ⟶ L) (g : L ⟶ M) :
    F.mapBifunctorLeftMap c₂ c (f ≫ g) =
      F.mapBifunctorLeftMap c₂ c f ≫ F.mapBifunctorLeftMap c₂ c g := by
  apply NatTrans.ext
  funext N
  simpa only [mapBifunctorLeftMap_app, NatTrans.comp_app, Category.id_comp] using
    mapBifunctorMap_comp F c f g (𝟙 N) (𝟙 N)

/-- A zero left map induces the zero natural transformation. -/
@[simp]
theorem mapBifunctorLeftMap_zero (K L : HomologicalComplex C₁ c₁)
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor K N F c]
    [∀ N : HomologicalComplex C₂ c₂, HasMapBifunctor L N F c] :
    F.mapBifunctorLeftMap c₂ c (0 : K ⟶ L) = 0 := by
  apply NatTrans.ext
  funext N
  simp only [mapBifunctorLeftMap_app]
  exact HomologicalComplex.mapBifunctorMap_zero_left F c K L (𝟙 N)

variable [∀ (K : HomologicalComplex C₁ c₁) (N : HomologicalComplex C₂ c₂),
  HasMapBifunctor K N F c]

/-- The fixed-left construction agrees with the corresponding component of the full bifunctor. -/
@[simp]
theorem mapBifunctorLeft_eq_map₂HomologicalComplex_obj (K : HomologicalComplex C₁ c₁) :
    F.mapBifunctorLeft c₂ c K = (F.map₂HomologicalComplex c₁ c₂ c).obj K := (rfl)

/-- The full totalized bifunctor preserves zero morphisms in its left argument.
In particular this supplies zero preservation for `F.map₂CochainComplex`. -/
instance map₂HomologicalComplex_preservesZeroMorphisms :
    (F.map₂HomologicalComplex c₁ c₂ c).PreservesZeroMorphisms where
  map_zero K L := by
    apply NatTrans.ext
    funext N
    exact HomologicalComplex.mapBifunctorMap_zero_left F c K L (𝟙 N)

end CategoryTheory.Functor
