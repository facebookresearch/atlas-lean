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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOne
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Coefficient naturality of one-cocycle cups

Let `G` be a group, `k` a commutative ring, and `f : A → A'`, `g : B → B'` equivariant
coefficient maps. For one-cocycles `x,y`, applying `f ⊗ g` to the two-cocycle `(p,q) ↦ x(p) ⊗
p·y(q)` gives the cup of `f ∘ x` and `g ∘ y`, with values in `A' ⊗ B'`.
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
representations. For `x ∈ Z¹(G,A)` and `y ∈ Z¹(G,B)`, `mapCocycles₂ (id G) (f ⊗ g)
(cupCocycleOneOne A B x y) = cupCocycleOneOne A' B' (mapCocycles₁ (id G) f x) (mapCocycles₁
(id G) g y)` in `Z²(G,A' ⊗ B')`. -/
theorem mapCocycles₂_cupCocycleOneOne
    (f : A ⟶ A') (g : B ⟶ B')
    (x : cocycles₁ A) (y : cocycles₁ B) :
    mapCocycles₂ (MonoidHom.id G) (f ⊗ₘ g)
        (cupCocycleOneOne A B x y) =
      cupCocycleOneOne A' B'
        (mapCocycles₁ (MonoidHom.id G) f x)
        (mapCocycles₁ (MonoidHom.id G) g y) := by
  apply cocycles₂_ext
  intro p q
  change (f ⊗ₘ g).hom
      (x p ⊗ₜ[k] B.ρ p (y q)) =
    f.hom (x p) ⊗ₜ[k] B'.ρ p (g.hom (y q))
  rw [Rep.hom_tensorHom, Representation.IntertwiningMap.tensor_apply,
    Rep.hom_comm_apply]

end groupCohomology
