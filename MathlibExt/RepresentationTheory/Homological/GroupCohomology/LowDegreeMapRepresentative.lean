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

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Representative formulas for low-degree cohomology maps

Elementwise forms of the naturality squares for `H1π` and `H2π`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A : Rep k H} {B : Rep k G}

set_option backward.isDefEq.respectTransparency false in
/-- A degree-one cohomology map computes on a cocycle representative by
mapping that representative. -/
theorem map_H1π
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₁ A) :
    map f phi 1 (H1π A z) = H1π B (mapCocycles₁ f phi z) := by
  rw [← ConcreteCategory.comp_apply, H1π_comp_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A degree-two cohomology map computes on a cocycle representative by
mapping that representative. -/
theorem map_H2π
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₂ A) :
    map f phi 2 (H2π A z) = H2π B (mapCocycles₂ f phi z) := by
  rw [← ConcreteCategory.comp_apply, H2π_comp_map]
  rfl

end groupCohomology
