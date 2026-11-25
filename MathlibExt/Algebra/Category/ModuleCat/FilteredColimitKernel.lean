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

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Kernels of maps on filtered module colimits

If two natural transformations of filtered diagrams of modules have the
same pointwise kernels, their induced maps on colimits have the same kernel.

For an element represented at a stage, vanishing of its image in the target
colimit means that image becomes literally zero at a common later stage.
Naturality moves the source representative to that stage, where pointwise
kernel equality transfers the vanishing to the second transformation.  The
same later-stage witness then proves vanishing in the second colimit.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {F A B : J ⥤ ModuleCat.{u} R}

/-- Pointwise equality of kernels for natural transformations of filtered
module diagrams passes to the induced colimit maps. -/
theorem colimMap_apply_eq_zero_iff_of_app
    (η : F ⟶ A) (θ : F ⟶ B)
    (hker : ∀ (j : J) (x : F.obj j),
      η.app j x = 0 ↔ θ.app j x = 0)
    (x : (CategoryTheory.Limits.colimit F : ModuleCat.{u} R)) :
    colimMap η x = 0 ↔ colimMap θ x = 0 := by
  have forward
      {A' B' : J ⥤ ModuleCat.{u} R}
      (η' : F ⟶ A') (θ' : F ⟶ B')
      (h : ∀ (j : J) (x : F.obj j),
        η'.app j x = 0 → θ'.app j x = 0) :
      ∀ x : (CategoryTheory.Limits.colimit F : ModuleCat.{u} R),
        colimMap η' x = 0 → colimMap θ' x = 0 := by
    intro y hy
    obtain ⟨j, z, rfl⟩ := Concrete.colimit_exists_rep F y
    have hηgen := ConcreteCategory.congr_hom (ι_colimMap η' j) z
    have hηrep :
        colimit.ι A' j (η'.app j z) = colimit.ι A' j 0 := by
      calc
        colimit.ι A' j (η'.app j z) =
            colimMap η' (colimit.ι F j z) := hηgen.symm
        _ = 0 := hy
        _ = colimit.ι A' j 0 := (map_zero _).symm
    obtain ⟨k, f, g, hstage⟩ :=
      Concrete.colimit_exists_of_rep_eq A'
        (η'.app j z) (0 : A'.obj j) hηrep
    have hηzero : η'.app k (F.map f z) = 0 := by
      calc
        η'.app k (F.map f z) = A'.map f (η'.app j z) :=
          ConcreteCategory.congr_hom (η'.naturality f) z
        _ = A'.map g 0 := hstage
        _ = 0 := map_zero _
    have hθzero : θ'.app k (F.map f z) = 0 := h k _ hηzero
    have hθrep :
        colimit.ι B' j (θ'.app j z) = colimit.ι B' j 0 := by
      apply Concrete.colimit_rep_eq_of_exists B'
      refine ⟨k, f, g, ?_⟩
      calc
        B'.map f (θ'.app j z) = θ'.app k (F.map f z) :=
          (ConcreteCategory.congr_hom (θ'.naturality f) z).symm
        _ = 0 := hθzero
        _ = B'.map g 0 := (map_zero _).symm
    have hθgen := ConcreteCategory.congr_hom (ι_colimMap θ' j) z
    calc
      colimMap θ' (colimit.ι F j z) =
          colimit.ι B' j (θ'.app j z) := hθgen
      _ = colimit.ι B' j 0 := hθrep
      _ = 0 := map_zero _
  constructor
  · exact forward η θ (fun j y hy => (hker j y).mp hy) x
  · exact forward θ η (fun j y hy => (hker j y).mpr hy) x

end ModuleCat
