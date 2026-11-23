/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveEquiv

/-!
# A category maps to the fundamental groupoid of its nerve

For any small category `C`, each object determines a nerve vertex and each
morphism determines a nerve edge.  Passing an edge to its generator in the
simplicial fundamental groupoid gives the canonical functor

`C ⟶ FundamentalGroupoid (nerve C)`.

Identity and composition follow from the corresponding nerve degeneracy and
2-simplex relations.  No groupoid hypothesis on `C` is needed; when `C` is a
groupoid this is the section used by the nerve-counit equivalence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u

namespace SSet

/-- The canonical functor from a category to the fundamental groupoid of its
nerve. -/
noncomputable def categoryNerveUnit
    (C : Type u) [Category.{v} C] :
    C ⥤ SSet.FundamentalGroupoid (CategoryTheory.nerve C) where
  obj x := SSet.FundamentalGroupoid.mk
    (X := CategoryTheory.nerve C)
    (CategoryTheory.nerveEquiv.symm x)
  map {x y} f := SSet.FundamentalGroupoid.homMk
    (X := CategoryTheory.nerve C)
    (CategoryTheory.nerve.edgeMk f)
  map_id x := by
    rw [CategoryTheory.nerve.edgeMk_id]
    exact SSet.FundamentalGroupoid.homMk_id _
  map_comp {x y z} f g := by
    obtain ⟨h⟩ :=
      (CategoryTheory.nerve.nonempty_compStruct_iff
        f g (f ≫ g)).2 rfl
    exact h.homMk_comp.symm

@[simp]
theorem categoryNerveUnit_obj
    (C : Type u) [Category.{v} C] (x : C) :
    (categoryNerveUnit C).obj x =
      SSet.FundamentalGroupoid.mk
        (X := CategoryTheory.nerve C)
        (CategoryTheory.nerveEquiv.symm x) :=
  rfl

@[simp]
theorem categoryNerveUnit_map
    (C : Type u) [Category.{v} C]
    {x y : C} (f : x ⟶ y) :
    (categoryNerveUnit C).map f =
      SSet.FundamentalGroupoid.homMk
        (X := CategoryTheory.nerve C)
        (CategoryTheory.nerve.edgeMk f) :=
  rfl

end SSet

end
