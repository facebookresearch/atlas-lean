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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneFunctoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneMap

/-!
# Functoriality of the descended degree-`(1, 1)` cup product

The joint group-and-coefficient naturality theorem for explicit cup
cocycles descends to genuine group-cohomology classes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A B : Rep k H} {A' B' : Rep k G}

set_option backward.isDefEq.respectTransparency false in
/-- The descended degree-`(1, 1)` cup product is jointly natural in a group
homomorphism and two compatible coefficient morphisms. -/
theorem map_cupOneOne_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (x : H1 A) (y : H1 B) :
    map f (phi ⊗ₘ psi) 2 (cupOneOne A B x y) =
      cupOneOne A' B' (map f phi 1 x) (map f psi 1 y) := by
  induction x using H1_induction_on with
  | _ x =>
      induction y using H1_induction_on with
      | _ y =>
          rw [cupOneOne_H1π_H1π,
            ← ConcreteCategory.comp_apply, H2π_comp_map,
            ← ConcreteCategory.comp_apply, H1π_comp_map,
            ← ConcreteCategory.comp_apply, H1π_comp_map]
          simp only [ConcreteCategory.comp_apply]
          rw [cupOneOne_H1π_H1π,
            mapCocycles₂_cupCocycleOneOne_of_hom]

end groupCohomology
