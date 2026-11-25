/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionSylow
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionArbitrary

/-!
# Arbitrary-degree restriction to Sylow subgroups

For a finite group and a Sylow `p`-subgroup, restriction is injective on
group cohomology in every degree with coefficients over a positive
prime-power `ZMod`.  This is the arbitrary-degree consequence of the
restriction--corestriction index formula.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [hp : Fact p.Prime]

/-- Restriction to a Sylow subgroup is injective in every degree with
coefficients over a positive prime-power `ZMod`. -/
theorem restriction_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (n : ℕ) :
    Function.Injective
      (map (A := A)
        (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n) := by
  exact restriction_injective_of_isUnit_index (H := (P : Subgroup G)) A n
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- A class in any degree is zero exactly when its restriction to a Sylow
subgroup is zero. -/
theorem restriction_sylow_eq_zero_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (n : ℕ) (x : groupCohomology A n) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n x = 0 ↔
      x = 0 := by
  constructor
  · intro hx
    apply restriction_injective_sylow_primePower A P hd n
    simpa using hx
  · rintro rfl
    exact map_zero _

/-- Two classes in any degree are equal exactly when their restrictions to
a Sylow subgroup are equal. -/
theorem restriction_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (n : ℕ) (x y : groupCohomology A n) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n y ↔
      x = y :=
  (restriction_injective_sylow_primePower A P hd n).eq_iff

end groupCohomology
