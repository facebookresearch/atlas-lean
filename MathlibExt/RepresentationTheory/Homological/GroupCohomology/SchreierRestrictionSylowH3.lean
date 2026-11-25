/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionH3
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionSylow

/-!
# Degree-three restriction to Sylow subgroups

For a finite group and coefficients over `ZMod (p ^ d)` with positive `d`,
restriction to a Sylow `p`-subgroup is injective on `H³`.  The proof chooses
a right transversal internally and uses the chosen-transversal degree-three
restriction/corestriction index formula.

No canonical degree-three corestriction, non-prime-power modulus statement,
Kummer generation theorem, or Bloch--Kato claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [Fact p.Prime]

/-- Restriction to a Sylow subgroup is injective on `H³` with coefficients
over a positive prime-power `ZMod`. -/
theorem restrictionH3_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3) :=
  restrictionH3_injective_of_isUnit_index A
    (default : (P : Subgroup G).RightTransversal)
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- A degree-three class is zero exactly when its restriction to a Sylow
subgroup is zero. -/
theorem restrictionH3_sylow_eq_zero_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x : H3 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restrictionH3_injective_sylow_primePower A P hd
    simpa using hx
  · rintro rfl
    exact map_zero _

/-- Two degree-three classes are equal exactly when their restrictions to a
Sylow subgroup are equal. -/
theorem restrictionH3_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H3 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 y ↔
      x = y :=
  (restrictionH3_injective_sylow_primePower A P hd).eq_iff

end groupCohomology
