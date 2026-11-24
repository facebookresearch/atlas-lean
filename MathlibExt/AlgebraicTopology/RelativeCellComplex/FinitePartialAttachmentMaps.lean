/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachment
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The SAME finite original attachment cells form their genuine under-root diagram

Every subset inclusion acts by the full original root and cell maps.
Their actual pushout universal property proves identity, composition
and source naturality. All original occurrences and category universes
remain unchanged, including the empty finite family.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace HomotopicalAlgebra.FinitePartialAttachment

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {I : Type w} {A B : I → C} (g : ∀ i, A i ⟶ B i) {X : C} (a : ∀ i, A i ⟶ X)

/-- The SAME original occurrence included in a larger original finite family. -/
abbrev occurrence {s t : Finset I} (h : s ⊆ t) (i : s) : t := ⟨i.1, h i.2⟩

/-- The actual full original partial-attachment comparison at a subset inclusion. -/
def map {s t : Finset I} (h : s ⊆ t) : object g a s ⟶ object g a t :=
  desc g a s (root g a t) (fun i => cell g a t (occurrence h i))
    (fun i => boundary g a t (occurrence h i))

/-- Every original comparison retains the SAME full original source root. -/
theorem root_map {s t : Finset I} (h : s ⊆ t) :
    root g a s ≫ map g a h = root g a t := root_desc g a s _ _ _

/-- Every original comparison retains the SAME complete selected cell. -/
theorem cell_map {s t : Finset I} (h : s ⊆ t) (i : s) :
    cell g a s i ≫ map g a h = cell g a t (occurrence h i) :=
  cell_desc g a s _ _ _ i

/-- The SAME actual original finite-family identity comparison is the entire original
identity map. -/
theorem map_id (s : Finset I) : map g a (Finset.Subset.refl s) = 𝟙 (object g a s) :=
  hom_ext g a s ((root_map g a _).trans (Category.comp_id _).symm)
    (fun i => (cell_map g a _ i).trans (Category.comp_id _).symm)

/-- The complete original subset comparisons compose to the SAME whole original comparison. -/
theorem map_comp {s t z : Finset I} (h : s ⊆ t) (k : t ⊆ z) :
    map g a (h.trans k) = map g a h ≫ map g a k := by
  apply hom_ext g a s
  · exact (root_map g a (h.trans k)).trans
      ((root_map g a k).symm.trans
        ((congrArg (fun f => f ≫ map g a k) (root_map g a h).symm).trans (Category.assoc _ _ _)))
  · intro i
    exact (cell_map g a (h.trans k) i).trans
      ((cell_map g a k (occurrence h i)).symm.trans
        ((congrArg (fun f => f ≫ map g a k) (cell_map g a h i).symm).trans (Category.assoc _ _ _)))

/-- The SAME entire original finite-attachment diagram under its actual original source. -/
def diagram : Finset I ⥤ Under X where
  obj s := Under.mk (root g a s)
  map f := Under.homMk (map g a (leOfHom f)) (root_map g a (leOfHom f))
  map_id s := by
    apply Under.UnderMorphism.ext
    exact map_id g a s
  map_comp f h := by
    apply Under.UnderMorphism.ext
    exact map_comp g a (leOfHom f) (leOfHom h)

/-- Read every actual original root of the full finite-attachment diagram literally. -/
theorem diagram_root (s : Finset I) : ((diagram g a).obj s).hom = root g a s := rfl

/-- Read every complete original diagram comparison as the SAME original partial pushout map. -/
theorem diagram_map {s t : Finset I} (f : s ⟶ t) :
    ((diagram g a).map f).right = map g a (leOfHom f) := rfl

end HomotopicalAlgebra.FinitePartialAttachment
