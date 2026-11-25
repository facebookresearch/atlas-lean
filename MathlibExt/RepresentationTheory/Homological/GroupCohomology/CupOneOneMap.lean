/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneNaturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductLowDegree

/-!
# Coefficient naturality of the descended degree-`(1, 1)` cup product

The representative-level naturality square for the degree-one cup product
descends to group-cohomology classes.  Thus mapping a cup through the tensor
of two equivariant coefficient morphisms agrees with cupping the two mapped
`H¹` classes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable {A B A' B' : Rep k G}

/-- The descended degree-`(1, 1)` cup product is natural in both
coefficient representations. -/
theorem map_cupOneOne
    (f : A ⟶ A') (g : B ⟶ B') (x : H1 A) (y : H1 B) :
    map (MonoidHom.id G) (f ⊗ₘ g) 2 (cupOneOne A B x y) =
      cupOneOne A' B'
        (map (MonoidHom.id G) f 1 x)
        (map (MonoidHom.id G) g 1 y) := by
  set_option backward.isDefEq.respectTransparency false in
  have h := ConcreteCategory.congr_hom
    (cup_naturality f g 1 1) (x ⊗ₜ[k] y)
  simp only [Nat.reduceAdd, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, cup_one_one_eq_cupOneOne,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h
  exact h

end groupCohomology
