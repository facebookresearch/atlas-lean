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
# Filtered total homology of a first-quadrant bicomplex

Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). Its total complex T
has horizontal stages G_i for i ∈ ℕ, retaining columns with horizontal index at most i. For n
∈ ℕ, the images F_iH_n(T) = im(H_n(G_i) → H_n(T)) form an increasing filtration that is
exhaustive by stage n.

The assignment K ↦ (H_n(T),F_•H_n(T)) is a functor to filtered objects of C indexed by ℕ. A
bicomplex map f induces H_n(Tot(f)) on the underlying object and the corresponding image map
on each filtration stage. Object and morphism universes of C are independent.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category and n ∈ ℕ. For a bicomplex K of shape (down ℕ,down ℕ), let T =
Tot(K) and G_i its horizontal subcomplex retaining columns at most i. The object H_n(T), with
stages F_i = im(H_n(G_i) → H_n(T)), defines an ℕ-indexed filtered object of C. This assignment
is functorial in K: a bicomplex map f acts by H_n(Tot(f)) on the underlying homology and by
the induced image map F_i(K) → F_i(L) on each stage. Those stage maps commute with inclusions
into total homology. The filtration is exhaustive for i ≥ n. -/
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
