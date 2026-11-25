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

public import Mathlib.GroupTheory.Sylow
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestriction

/-!
# Low-degree restriction to Sylow subgroups

For a finite group and a Sylow `p`-subgroup, the subgroup index is prime to
`p`.  It is therefore a unit in `ZMod (p ^ d)` for positive `d`.  The
restriction/corestriction formula makes restriction injective on `H¹` and
`H²` with arbitrary `ZMod (p ^ d)`-linear coefficients.

These results are restricted to positive prime-power moduli.  No assertion
is made for a composite modulus with several prime factors, and no
degree-three restriction theorem is claimed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [hp : Fact p.Prime]

/-- The index of a Sylow `p`-subgroup is a unit modulo every positive power
of `p`. -/
theorem sylowIndex_isUnit_zmod_primePower
    (P : Sylow p G) (hd : 0 < d) :
    IsUnit (P.index : ZMod (p ^ d)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp.out hd).2 P.not_dvd_index

/-- Restriction to a Sylow subgroup is injective on `H¹` with coefficients
over a positive prime-power `ZMod`. -/
theorem restrictionH1_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1) :=
  restrictionH1_injective_of_isUnit_index A
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Restriction to a Sylow subgroup is injective on `H²` with coefficients
over a positive prime-power `ZMod`. -/
theorem restrictionH2_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2) :=
  restrictionH2_injective_of_isUnit_index A
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- A degree-one class is zero exactly when its restriction to a Sylow
subgroup is zero. -/
theorem restrictionH1_sylow_eq_zero_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x : H1 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1 x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restrictionH1_injective_sylow_primePower A P hd
    simpa using hx
  · rintro rfl
    exact map_zero _

/-- Two degree-one classes are equal exactly when their restrictions to a
Sylow subgroup are equal. -/
theorem restrictionH1_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H1 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1 y ↔
      x = y :=
  (restrictionH1_injective_sylow_primePower A P hd).eq_iff

/-- A degree-two class is zero exactly when its restriction to a Sylow
subgroup is zero. -/
theorem restrictionH2_sylow_eq_zero_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x : H2 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2 x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restrictionH2_injective_sylow_primePower A P hd
    simpa using hx
  · rintro rfl
    exact map_zero _

/-- Two degree-two classes are equal exactly when their restrictions to a
Sylow subgroup are equal. -/
theorem restrictionH2_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H2 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2 y ↔
      x = y :=
  (restrictionH2_injective_sylow_primePower A P hd).eq_iff

end groupCohomology
