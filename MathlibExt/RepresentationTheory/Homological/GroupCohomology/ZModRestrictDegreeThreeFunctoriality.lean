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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictDegreeThree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality

/-!
# Functoriality of the degree-three scalar-restriction comparison

The explicit degree-three cochain/cocycle comparisons and the H3 additive
equivalence commute with restriction of the acting group and an equivariant
coefficient morphism.  The statements include `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G H : Type} [Group G] [Group H]
variable (n : ℕ) {A : Rep (ZMod n) H} {B : Rep (ZMod n) G}

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with the explicit degree-three cochain
map. -/
theorem cochains₃ZModRestrictIntEquiv_cochainsMap₃
    (f : G →* H) (phi : Rep.res f A ⟶ B)
    (z : H × H × H → A) :
    cochains₃ZModRestrictIntEquiv n B
        ((cochainsMap₃ f phi).hom z) =
      (cochainsMap₃ f (Rep.zmodRestrictIntMap phi)).hom
        (cochains₃ZModRestrictIntEquiv n A z) := by
  funext p
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with the explicit degree-three cocycle
map. -/
theorem cocycles₃ZModRestrictIntEquiv_mapCocycles₃
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₃ A) :
    cocycles₃ZModRestrictIntEquiv n B (mapCocycles₃ f phi z) =
      mapCocycles₃ f (Rep.zmodRestrictIntMap phi)
        (cocycles₃ZModRestrictIntEquiv n A z) := by
  apply cocycles₃_ext
  intro g h i
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The degree-three scalar-restriction equivalence is natural. -/
theorem H3ZModRestrictIntAddEquiv_map_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ B) (x : H3 A) :
    H3ZModRestrictIntAddEquiv n B (map f phi 3 x) =
      map f (Rep.zmodRestrictIntMap phi) 3
        (H3ZModRestrictIntAddEquiv n A x) := by
  induction x using H3_induction_on with
  | _ z =>
      rw [← ConcreteCategory.comp_apply, H3π_comp_map]
      rw [ConcreteCategory.comp_apply, H3ZModRestrictIntAddEquiv_H3π]
      rw [H3ZModRestrictIntAddEquiv_H3π]
      rw [← ConcreteCategory.comp_apply, H3π_comp_map]
      exact congrArg (H3π (Rep.zmodRestrictInt n B))
        (cocycles₃ZModRestrictIntEquiv_mapCocycles₃ n f phi z)

end groupCohomology
