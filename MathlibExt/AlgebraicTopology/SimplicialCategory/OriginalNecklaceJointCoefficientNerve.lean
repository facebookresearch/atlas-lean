/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientIso
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The entire original joint coefficient is its full path-poset nerve

Every original flag retains all its vertices and contains all original
joints in every member. The complete joint-coefficient complex is the
nerve of the full original interval-subset category containing those
joints. Both inverse maps retain every original scalar operator.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace

/-- The original interval subsets containing all SAME original necklace joints. -/
def jointPathProperty (T : Data) : ObjectProperty
    (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (T.dimension + 1)))
      (ULift.up.{u} (Fin.last T.dimension))) :=
  fun p => ∀ j ∈ T.joints, ULift.up.{u} j ∈ p.I

/-- The entire original joint-containing path category, with all its original inclusion arrows. -/
abbrev jointPathCategory (T : Data) := (jointPathProperty.{u} T).FullSubcategory

/-- The complete original path-category nerve maps into the SAME full joint-coefficient complex. -/
def jointNerveToCoefficient (T : Data) : nerve (jointPathCategory.{u} T) ⟶ fullCoefficient.{u} T where
  app q := ↾fun F => ⟨F ⋙ (jointPathProperty T).ι, (F.obj 0).property⟩
  naturality _q _r _θ := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    rfl

/-- Every complete original joint flag is the SAME full chain in its original path category. -/
def jointCoefficientChain (T : Data) {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (nerve (jointPathCategory T)).obj q where
  obj i := ⟨p.val.obj i, coefficient_joint_all T p i⟩
  map f := ObjectProperty.homMk (p.val.map f)
  map_id i := by
    apply ObjectProperty.hom_ext
    exact p.val.map_id i
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact p.val.map_comp f g

/-- The SAME complete original coefficient maps to its full original path-poset nerve. -/
def jointCoefficientToNerve (T : Data) : fullCoefficient.{u} T ⟶ nerve (jointPathCategory.{u} T) where
  app q := ↾jointCoefficientChain T
  naturality _q _r _θ := by
    apply ConcreteCategory.hom_ext
    intro p
    refine Functor.ext (fun _i => rfl) ?_
    intro i j f
    apply ObjectProperty.hom_ext
    change p.val.map _ = 𝟙 _ ≫ p.val.map _ ≫ 𝟙 _
    simp

/-- Both inverse maps identify the SAME whole original joint coefficient with its full original path-poset nerve. -/
def jointCoefficientNerveIso (T : Data) : fullCoefficient.{u} T ≅ nerve (jointPathCategory.{u} T) where
  hom := jointCoefficientToNerve T
  inv := jointNerveToCoefficient T
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine Functor.ext (fun _i => rfl) ?_
    intro i j f
    change p.val.map f = 𝟙 _ ≫ p.val.map f ≫ 𝟙 _
    simp
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro F
    refine Functor.ext (fun _i => rfl) ?_
    intro i j f
    apply ObjectProperty.hom_ext
    change (F.map f).hom = 𝟙 _ ≫ (F.map f).hom ≫ 𝟙 _
    simp

/-- Every vertex of the SAME full original nerve comparison retains its literal whole original flag. -/
theorem jointCoefficientNerveIso_vertex (T : Data) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) (i : Fin (q.unop.len + 1)) :
    (((jointCoefficientNerveIso T).hom.app q p).obj i).obj = p.val.obj i := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
