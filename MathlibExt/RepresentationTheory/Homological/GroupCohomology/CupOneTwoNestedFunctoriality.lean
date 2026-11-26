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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneMap
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwoFunctoriality

/-!
# Naturality of right-associated triple cups

Let `k,G : Type`, with `k` a commutative ring and `G` a group. An equivariant map `φ : C → D`
preserves the right-associated cup `x ∪ (y ∪ z)` of three degree-one classes after applying `φ
⊗ (φ ⊗ φ)` to its coefficients. The same equation holds for the explicit three-cocycles, whose
value is `x(g) ⊗ (g·y(h) ⊗ (gh)·z(j))`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {G : Type} [Group G]

/-- For `k,G : Type` with `k` a commutative ring and `G` a group, let `C,D : Rep k G`, `φ : C →
D`, and `x,y,z ∈ H¹(G,C)`. Then `(φ ⊗ (φ ⊗ φ))_* (x ∪ (y ∪ z)) = (φ_*x) ∪ ((φ_*y) ∪ (φ_*z))`
in `H³(G,D ⊗ (D ⊗ D))`, with the inner cup `cupOneOne` and outer cup `cupOneTwo`. -/
theorem map_nestedCupOneOne
    {k : Type} [CommRing k] {C D : Rep k G}
    (phi : C ⟶ D) (x y z : H1 C) :
    map (MonoidHom.id G) (phi ⊗ₘ (phi ⊗ₘ phi)) 3
        (cupOneTwo C (C ⊗ C) x (cupOneOne C C y z)) =
      cupOneTwo D (D ⊗ D)
        (map (MonoidHom.id G) phi 1 x)
        (cupOneOne D D
          (map (MonoidHom.id G) phi 1 y)
          (map (MonoidHom.id G) phi 1 z)) := by
  rw [map_cupOneTwo_of_hom, map_cupOneOne]

/-- For `k,G : Type` with `k` a commutative ring and `G` a group, let `C,D : Rep k G`, `φ : C →
D`, and `x,y,z ∈ Z¹(G,C)`. Applying `mapCocycles₃ (id G) (φ ⊗ (φ ⊗ φ))` to `cupCocycleOneTwo C
(C ⊗ C) x (cupCocycleOneOne C C y z)` equals the same right-associated cocycle cup formed from
the three images under `mapCocycles₁ (id G) φ`. -/
theorem mapCocycles₃_nestedCupOneOne
    {k : Type} [CommRing k] {C D : Rep k G}
    (phi : C ⟶ D) (x y z : cocycles₁ C) :
    mapCocycles₃ (MonoidHom.id G) (phi ⊗ₘ (phi ⊗ₘ phi))
        (cupCocycleOneTwo C (C ⊗ C) x (cupCocycleOneOne C C y z)) =
      cupCocycleOneTwo D (D ⊗ D)
        (mapCocycles₁ (MonoidHom.id G) phi x)
        (cupCocycleOneOne D D
          (mapCocycles₁ (MonoidHom.id G) phi y)
          (mapCocycles₁ (MonoidHom.id G) phi z)) := by
  rw [mapCocycles₃_cupCocycleOneTwo_of_hom,
    mapCocycles₂_cupCocycleOneOne]

end groupCohomology
