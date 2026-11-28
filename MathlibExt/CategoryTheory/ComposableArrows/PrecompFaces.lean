/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarConstruction
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Faces of prepended composable-arrow chains

A face after the new first vertex of a prepended chain is the same as
prepending the corresponding face of its tail. Equality follows from the
head object, the first arrow and the complete tail; thinness is used for the
finite indexing ordinals.
-/

@[expose] public section

open CategoryTheory CategoryTheory.CategoryHomology

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C]

/-- A later face prepends the arrow composed with the face endpoint map. -/
theorem nerve_δ_succ_precomp {n : ℕ} (F : ComposableArrows C (n + 1))
    {X : C} (f : X ⟶ F.left) (i : Fin (n + 2)) :
    (nerve C).δ i.succ (F.precomp f) =
      ((nerve C).δ i F).precomp (f ≫ faceLeftHom i F) := by
  have h₀ : ((nerve C).δ i.succ (F.precomp f)).obj' 0 =
      (((nerve C).δ i F).precomp (f ≫ faceLeftHom i F)).obj' 0 := by
    change (F.precomp f).obj (i.succ.succAbove 0) = X
    rw [Fin.succ_succAbove_zero]
    rfl
  have ht : ((nerve C).δ i.succ (F.precomp f)).δ₀ =
      (((nerve C).δ i F).precomp (f ≫ faceLeftHom i F)).δ₀ := by
    change (nerve C).δ (0 : Fin (n + 2))
        ((nerve C).δ i.succ (F.precomp f)) = (nerve C).δ i F
    have e : (nerve C).δ ((0 : Fin (n + 2)).castSucc) (F.precomp f) = F := by
      change (F.precomp f).δ₀ = F
      exact precomp_δ₀ F f
    exact (SSet.δ_comp_δ_apply (S := nerve C) (i := (0 : Fin (n + 2)))
      (j := i) (Fin.zero_le i) (F.precomp f)).trans
        (congrArg (fun G : ComposableArrows C (n + 1) ↦ (nerve C).δ i G) e)
  apply ComposableArrows.ext_succ h₀ ht
  cases i using Fin.cases with
  | zero =>
    change f ≫ F.map' 0 1 = 𝟙 X ≫ (f ≫ F.map' 0 1) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  | succ i =>
    change f = 𝟙 X ≫ (f ≫ F.map (𝟙 (0 : Fin (n + 1 + 1)))) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    have h := congrArg (fun g : F.left ⟶ F.left ↦ f ≫ g)
      (F.map_id (0 : Fin (n + 1 + 1)))
    exact (h.trans (Category.comp_id f)).symm

end CategoryTheory.ComposableArrows
