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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictLowDegree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Functoriality of low-degree scalar restriction

The low-degree comparisons from `ZMod n` coefficients to integral
scalar-restricted coefficients commute with simultaneous restriction of the
acting group and an equivariant coefficient morphism.

The statements include `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G H : Type} [Group G] [Group H]
variable (n : ℕ) {A : Rep (ZMod n) H} {B : Rep (ZMod n) G}

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with the representative map on degree-one
cocycles for an arbitrary group homomorphism. -/
theorem cocycles₁ZModRestrictIntEquiv_mapCocycles₁
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₁ A) :
    cocycles₁ZModRestrictIntEquiv n B (mapCocycles₁ f phi z) =
      mapCocycles₁ f (Rep.zmodRestrictIntMap phi)
        (cocycles₁ZModRestrictIntEquiv n A z) := by
  apply cocycles₁_ext
  intro g
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with the representative map on degree-two
cocycles for an arbitrary group homomorphism. -/
theorem cocycles₂ZModRestrictIntEquiv_mapCocycles₂
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₂ A) :
    cocycles₂ZModRestrictIntEquiv n B (mapCocycles₂ f phi z) =
      mapCocycles₂ f (Rep.zmodRestrictIntMap phi)
        (cocycles₂ZModRestrictIntEquiv n A z) := by
  apply cocycles₂_ext
  intro g h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The degree-one scalar-restriction equivalence is natural for an
arbitrary group homomorphism and compatible coefficient map. -/
theorem H1ZModRestrictIntAddEquiv_map_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ B) (x : H1 A) :
    H1ZModRestrictIntAddEquiv n B (map f phi 1 x) =
      map f (Rep.zmodRestrictIntMap phi) 1
        (H1ZModRestrictIntAddEquiv n A x) := by
  induction x using H1_induction_on with
  | _ z =>
      rw [← ConcreteCategory.comp_apply, H1π_comp_map]
      rw [ConcreteCategory.comp_apply, H1ZModRestrictIntAddEquiv_H1π]
      rw [H1ZModRestrictIntAddEquiv_H1π]
      rw [← ConcreteCategory.comp_apply, H1π_comp_map]
      exact congrArg (H1π (Rep.zmodRestrictInt n B))
        (cocycles₁ZModRestrictIntEquiv_mapCocycles₁ n f phi z)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-two scalar-restriction equivalence is natural for an
arbitrary group homomorphism and compatible coefficient map. -/
theorem H2ZModRestrictIntAddEquiv_map_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ B) (x : H2 A) :
    H2ZModRestrictIntAddEquiv n B (map f phi 2 x) =
      map f (Rep.zmodRestrictIntMap phi) 2
        (H2ZModRestrictIntAddEquiv n A x) := by
  induction x using H2_induction_on with
  | _ z =>
      rw [← ConcreteCategory.comp_apply, H2π_comp_map]
      rw [ConcreteCategory.comp_apply, H2ZModRestrictIntAddEquiv_H2π]
      rw [H2ZModRestrictIntAddEquiv_H2π]
      rw [← ConcreteCategory.comp_apply, H2π_comp_map]
      exact congrArg (H2π (Rep.zmodRestrictInt n B))
        (cocycles₂ZModRestrictIntEquiv_mapCocycles₂ n f phi z)

end groupCohomology
