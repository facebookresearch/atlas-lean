/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationFunctor

/-!
# The finite total-homology filtered-object functor

The finite image filtration on total homology is functorial in the
first-quadrant bicomplex.  This file packages its underlying total-homology
map and its stagewise image maps as morphisms of filtered objects.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Total homology with its finite image filtration, functorial in the
first-quadrant bicomplex. -/
noncomputable def horizontalFiniteTotalHomologyFilteredObjectFunctor
    (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject C ℕ where
  obj K :=
    { X := (K.total (ComplexShape.down ℕ)).homology n
      filtration := horizontalFiniteTotalHomologyFiltration K n }
  map f :=
    CategoryTheory.FilteredObject.homMk
      (HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) n)
      (fun i ↦
        ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor n).map f).app i)
      (horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app_ι n f)
  map_id K := by
    apply CategoryTheory.FilteredObject.hom_ext
    change HomologicalComplex.homologyMap
      (total.map (𝟙 K) (ComplexShape.down ℕ)) n = 𝟙 _
    rw [total.map_id, HomologicalComplex.homologyMap_id]
  map_comp f g := by
    apply CategoryTheory.FilteredObject.hom_ext
    change HomologicalComplex.homologyMap
      (total.map (f ≫ g) (ComplexShape.down ℕ)) n =
        HomologicalComplex.homologyMap
            (total.map f (ComplexShape.down ℕ)) n ≫
          HomologicalComplex.homologyMap
            (total.map g (ComplexShape.down ℕ)) n
    rw [total.map_comp, HomologicalComplex.homologyMap_comp]

@[simp]
theorem horizontalFiniteTotalHomologyFilteredObjectFunctor_obj_X
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).obj K).X =
      (K.total (ComplexShape.down ℕ)).homology n :=
  rfl

@[simp]
theorem horizontalFiniteTotalHomologyFilteredObjectFunctor_obj_filtration
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).obj K).filtration =
      horizontalFiniteTotalHomologyFiltration K n :=
  rfl

@[simp]
theorem horizontalFiniteTotalHomologyFilteredObjectFunctor_map_hom
    (n : ℕ) (f : K ⟶ L) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).map f).hom =
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) n :=
  rfl

@[simp]
theorem horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).map f).natTrans.app i =
      horizontalFiniteHomologyImageMapOfBicomplex f n i :=
  rfl

end HomologicalComplex₂

end
