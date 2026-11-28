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
# Coefficient naturality of degree-one cohomology cups

For a group `G` and a commutative ring `k`, equivariant coefficient maps `f : A → A'` and `g :
B → B'` carry the cup `H¹(G,A) × H¹(G,B) → H²(G,A ⊗ B)` to the cup with coefficients `A' ⊗
B'`. Thus `(f ⊗ g)_*(x ∪ y) = f_*x ∪ g_*y`, with the group homomorphism equal to the identity
of `G`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable {A B A' B' : Rep k G}

/-- Let `k` be a commutative ring, `G` a group, and `f : A → A'`, `g : B → B'` morphisms of
`k`-representations of `G`. For `x ∈ H¹(G,A)` and `y ∈ H¹(G,B)`, `map (id G) (f ⊗ g) 2
(cupOneOne A B x y) = cupOneOne A' B' (map (id G) f 1 x) (map (id G) g 1 y)`. -/
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
