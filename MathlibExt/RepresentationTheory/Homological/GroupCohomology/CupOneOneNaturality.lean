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
# Coefficient naturality of the degree-one cup product

The cup of two degree-one cocycles commutes with equivariant coefficient
maps.  This is the representative-level naturality square needed to
transport explicit cup classes across coefficient isomorphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable {A B A' B' : Rep k G}

/-- Mapping a cup cocycle through the tensor of two coefficient morphisms is
the cup of the mapped one-cocycles. -/
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
