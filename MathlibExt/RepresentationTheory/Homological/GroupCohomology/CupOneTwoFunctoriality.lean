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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwo
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality

/-!
# Functoriality of the degree-(1,2) cup product

The explicit and descended degree-`(1,2)` cup products commute with a group
homomorphism and compatible coefficient morphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A B : Rep k H} {A' B' : Rep k G}

/-- Joint naturality of explicit `(1,2)` cup cocycles. -/
theorem mapCocycles₃_cupCocycleOneTwo_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A')
    (psi : Rep.res f B ⟶ B')
    (x : cocycles₁ A) (y : cocycles₂ B) :
    mapCocycles₃ f (phi ⊗ₘ psi) (cupCocycleOneTwo A B x y) =
      cupCocycleOneTwo A' B'
        (mapCocycles₁ f phi x) (mapCocycles₂ f psi y) := by
  apply cocycles₃_ext
  intro g h j
  change (phi ⊗ₘ psi).hom
      (x (f g) ⊗ₜ[k] B.ρ (f g) (y (f h, f j))) =
    phi.hom (x (f g)) ⊗ₜ[k]
      B'.ρ g (psi.hom (y (f h, f j)))
  rw [Rep.hom_tensorHom, Representation.IntertwiningMap.tensor_apply]
  congr 1
  exact Rep.hom_comm_apply psi g _

set_option backward.isDefEq.respectTransparency false in
/-- Joint naturality of the descended `(1,2)` cup product. -/
theorem map_cupOneTwo_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A')
    (psi : Rep.res f B ⟶ B')
    (x : H1 A) (y : H2 B) :
    map f (phi ⊗ₘ psi) 3 (cupOneTwo A B x y) =
      cupOneTwo A' B' (map f phi 1 x) (map f psi 2 y) := by
  induction x using H1_induction_on with
  | _ x =>
    induction y using H2_induction_on with
    | _ y =>
      rw [cupOneTwo_H1π_H2π,
        ← ConcreteCategory.comp_apply, H3π_comp_map,
        ← ConcreteCategory.comp_apply, H1π_comp_map,
        ← ConcreteCategory.comp_apply, H2π_comp_map]
      simp only [ConcreteCategory.comp_apply]
      rw [cupOneTwo_H1π_H2π,
        mapCocycles₃_cupCocycleOneTwo_of_hom]

end groupCohomology
