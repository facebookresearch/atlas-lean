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
# Functoriality of right-associated triple cups

The right-associated triple cup formed from three degree-one classes, and its
explicit cocycle representative, commute with one coefficient morphism
applied in all three inputs.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {G : Type} [Group G]

/-- A right-associated triple cup is natural under one coefficient
morphism applied in all three inputs. -/
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

/-- The explicit right-associated triple-cup cocycle is natural under one
coefficient morphism applied in all three inputs. -/
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
