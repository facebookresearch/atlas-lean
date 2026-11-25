/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.ComposableArrows.One
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import MathlibExt.CategoryTheory.ComposableArrows.Arrow

@[expose] public section

namespace CategoryTheory

open Limits
open CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

namespace ShortComplex

noncomputable def cokernelCompFunctor : ComposableArrows C 2 ⥤ ShortComplex C :=
  let coker01Functor : ComposableArrows C 2 ⥤ C :=
    ComposableArrows.functorArrows C 0 1 2 ⋙ ComposableArrows.arrowFunctor ⋙ coker C
  let coker02Functor : ComposableArrows C 2 ⥤ C :=
    ComposableArrows.functorArrows C 0 2 2 ⋙ ComposableArrows.arrowFunctor ⋙ coker C
  let coker12Functor : ComposableArrows C 2 ⥤ C :=
    ComposableArrows.functorArrows C 1 2 2 ⋙ ComposableArrows.arrowFunctor ⋙ coker C
  let cokerMap01_02 : coker01Functor ⟶ coker02Functor :=
    whiskerRight
      (whiskerRight
        (ComposableArrows.mapFunctorArrows (C := C) 0 1 0 2 2)
        ComposableArrows.arrowFunctor)
      (coker C)
  let cokerMap02_12 : coker02Functor ⟶ coker12Functor :=
    whiskerRight
      (whiskerRight
        (ComposableArrows.mapFunctorArrows (C := C) 0 2 1 2 2)
        ComposableArrows.arrowFunctor)
      (coker C)
  let cokerCompAsFunctorCategory : ShortComplex (ComposableArrows C 2 ⥤ C) :=
    { X₁ := coker01Functor
      X₂ := coker02Functor
      X₃ := coker12Functor
      f := cokerMap01_02
      g := cokerMap02_12
      zero := by
        ext S
        let f01 := S.map' 0 1
        let f02 := S.map' 0 2
        let g12 := S.map' 1 2
        have h02eq : f01 ≫ g12 = f02 := by
          have h := ComposableArrows.map'_comp S 0 1 2
          exact h.symm
        have h01_zero : f01 ≫ (g12 ≫ cokernel.π f02) = 0 := by
          calc f01 ≫ (g12 ≫ cokernel.π f02) =
              (f01 ≫ g12) ≫ cokernel.π f02 := by rw [← Category.assoc]
            _ = f02 ≫ cokernel.π f02 := by rw [h02eq]
            _ = 0 := cokernel.condition _
        have h02_zero : f02 ≫ cokernel.π g12 = 0 := by
          calc f02 ≫ cokernel.π g12 =
              (f01 ≫ g12) ≫ cokernel.π g12 := by rw [← h02eq]
            _ = f01 ≫ (g12 ≫ cokernel.π g12) := by rw [Category.assoc]
            _ = f01 ≫ 0 := by rw [cokernel.condition _]
            _ = 0 := by rw [comp_zero]
        have h02_zero' : f02 ≫ (S.map' 2 2 ≫ cokernel.π g12) = 0 := by
          have h22 : S.map' 2 2 = 𝟙 _ := ComposableArrows.map'_self S 2
          calc f02 ≫ (S.map' 2 2 ≫ cokernel.π g12) =
              f02 ≫ (𝟙 _ ≫ cokernel.π g12) := by rw [h22]
            _ = f02 ≫ cokernel.π g12 := by rw [Category.id_comp]
            _ = 0 := h02_zero
        have hπ01 : cokernel.π f01 ≫ cokerMap01_02.app S = g12 ≫ cokernel.π f02 := by
          dsimp
          exact cokernel.π_desc f01 (g12 ≫ cokernel.π f02) h01_zero
        have hπ02 : cokernel.π f02 ≫ cokerMap02_12.app S =
            S.map' 2 2 ≫ cokernel.π g12 := by
          dsimp
          exact cokernel.π_desc f02 (S.map' 2 2 ≫ cokernel.π g12) h02_zero'
        have h22 : S.map' 2 2 = 𝟙 _ := ComposableArrows.map'_self S 2
        have hπ02' : cokernel.π f02 ≫ cokerMap02_12.app S = cokernel.π g12 := by
          rw [hπ02, h22, Category.id_comp]
        have h_zero : g12 ≫ cokernel.π g12 = 0 := cokernel.condition _
        have h1 : cokernel.π f01 ≫ ((cokerMap01_02.app S) ≫ (cokerMap02_12.app S)) =
            (cokernel.π f01 ≫ (cokerMap01_02.app S)) ≫ (cokerMap02_12.app S) :=
          (Category.assoc _ _ _).symm
        have h2 : (cokernel.π f01 ≫ (cokerMap01_02.app S)) ≫ (cokerMap02_12.app S) =
            (g12 ≫ cokernel.π f02) ≫ (cokerMap02_12.app S) :=
          congrArg (· ≫ (cokerMap02_12.app S)) hπ01
        have h3 : (g12 ≫ cokernel.π f02) ≫ (cokerMap02_12.app S) =
            g12 ≫ (cokernel.π f02 ≫ (cokerMap02_12.app S)) :=
          Category.assoc _ _ _
        have h4 : g12 ≫ (cokernel.π f02 ≫ (cokerMap02_12.app S)) =
            g12 ≫ cokernel.π g12 :=
          congrArg (g12 ≫ ·) hπ02'
        have h_comp : cokernel.π f01 ≫
            ((cokerMap01_02.app S) ≫ (cokerMap02_12.app S)) = 0 :=
          (h1.trans (h2.trans (h3.trans (h4.trans h_zero))))
        have h_eq : cokernel.π f01 ≫
            ((cokerMap01_02.app S) ≫ (cokerMap02_12.app S)) =
            cokernel.π f01 ≫ (0 : _ ⟶ _) := by
          rw [h_comp, comp_zero]
        exact (cancel_epi (cokernel.π f01)).1 h_eq }
  (ShortComplex.functorEquivalence (ComposableArrows C 2) C).functor.obj cokerCompAsFunctorCategory

@[simp]
lemma cokernelCompFunctor_obj_X₁ (S : ComposableArrows C 2) :
    (cokernelCompFunctor (C := C).obj S).X₁ = cokernel (S.map' 0 1) := rfl

@[simp]
lemma cokernelCompFunctor_obj_X₂ (S : ComposableArrows C 2) :
    (cokernelCompFunctor (C := C).obj S).X₂ = cokernel (S.map' 0 2) := rfl

@[simp]
lemma cokernelCompFunctor_obj_X₃ (S : ComposableArrows C 2) :
    (cokernelCompFunctor (C := C).obj S).X₃ = cokernel (S.map' 1 2) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma cokernelCompFunctor_map_τ₁
    {S T : ComposableArrows C 2} (φ : S ⟶ T) :
    cokernel.π (S.map' 0 1) ≫
        (cokernelCompFunctor (C := C) |>.map φ).τ₁ =
      ComposableArrows.app' φ 1 ≫ cokernel.π (T.map' 0 1) := by
  change cokernel.π (S.map' 0 1) ≫
      cokernel.map (S.map' 0 1) (T.map' 0 1)
        (ComposableArrows.app' φ 0) (ComposableArrows.app' φ 1)
        (ComposableArrows.naturality' φ 0 1) = _
  rw [cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma cokernelCompFunctor_map_τ₃
    {S T : ComposableArrows C 2} (φ : S ⟶ T) :
    cokernel.π (S.map' 1 2) ≫
        (cokernelCompFunctor (C := C) |>.map φ).τ₃ =
      ComposableArrows.app' φ 2 ≫ cokernel.π (T.map' 1 2) := by
  change cokernel.π (S.map' 1 2) ≫
      cokernel.map (S.map' 1 2) (T.map' 1 2)
        (ComposableArrows.app' φ 1) (ComposableArrows.app' φ 2)
        (ComposableArrows.naturality' φ 1 2) = _
  rw [cokernel.π_desc]

lemma cokernelCompFunctor_obj_f (S : ComposableArrows C 2) :
    cokernel.π (S.map' 0 1) ≫ (cokernelCompFunctor (C := C).obj S).f =
      S.map' 1 2 ≫ cokernel.π (S.map' 0 2) := by
  dsimp [cokernelCompFunctor]
  let f01 := S.map' 0 1
  let f02 := S.map' 0 2
  let g12 := S.map' 1 2
  have h02eq : f01 ≫ g12 = f02 := by
    have h := ComposableArrows.map'_comp S 0 1 2
    exact h.symm
  have h01_zero : f01 ≫ (g12 ≫ cokernel.π f02) = 0 := by
    calc f01 ≫ (g12 ≫ cokernel.π f02) =
        (f01 ≫ g12) ≫ cokernel.π f02 := by rw [← Category.assoc]
      _ = f02 ≫ cokernel.π f02 := by rw [h02eq]
      _ = 0 := cokernel.condition _
  have : cokernel.π f01 ≫
      (cokernel.desc f01 (g12 ≫ cokernel.π f02) h01_zero) = g12 ≫ cokernel.π f02 :=
    cokernel.π_desc _ _ _
  exact this

lemma cokernelCompFunctor_obj_g (S : ComposableArrows C 2) :
    cokernel.π (S.map' 0 2) ≫ (cokernelCompFunctor (C := C).obj S).g =
      cokernel.π (S.map' 1 2) := by
  dsimp [cokernelCompFunctor]
  let f01 := S.map' 0 1
  let f02 := S.map' 0 2
  let g12 := S.map' 1 2
  have h02eq : f01 ≫ g12 = f02 := by
    have h := ComposableArrows.map'_comp S 0 1 2
    exact h.symm
  have h02_zero : f02 ≫ cokernel.π g12 = 0 := by
    calc f02 ≫ cokernel.π g12 =
        (f01 ≫ g12) ≫ cokernel.π g12 := by rw [← h02eq]
      _ = f01 ≫ (g12 ≫ cokernel.π g12) := by rw [Category.assoc]
      _ = f01 ≫ 0 := by rw [cokernel.condition _]
      _ = 0 := by rw [comp_zero]
  have h02_zero' : f02 ≫ (S.map' 2 2 ≫ cokernel.π g12) = 0 := by
    have h22 : S.map' 2 2 = 𝟙 _ := ComposableArrows.map'_self S 2
    calc f02 ≫ (S.map' 2 2 ≫ cokernel.π g12) =
        f02 ≫ (𝟙 _ ≫ cokernel.π g12) := by rw [h22]
      _ = f02 ≫ cokernel.π g12 := by rw [Category.id_comp]
      _ = 0 := h02_zero
  have h22 : S.map' 2 2 = 𝟙 _ := ComposableArrows.map'_self S 2
  have hπ : cokernel.π f02 ≫
      (cokernel.desc f02 (S.map' 2 2 ≫ cokernel.π g12) h02_zero') =
      S.map' 2 2 ≫ cokernel.π g12 :=
    cokernel.π_desc _ _ _
  have h : cokernel.π f02 ≫
      (cokernel.desc f02 (S.map' 2 2 ≫ cokernel.π g12) h02_zero') = cokernel.π g12 := by
    calc cokernel.π f02 ≫ (cokernel.desc f02 (S.map' 2 2 ≫ cokernel.π g12) h02_zero') =
        S.map' 2 2 ≫ cokernel.π g12 := hπ
      _ = 𝟙 _ ≫ cokernel.π g12 := by rw [h22]
      _ = cokernel.π g12 := by simp
  exact h

end ShortComplex

end CategoryTheory
