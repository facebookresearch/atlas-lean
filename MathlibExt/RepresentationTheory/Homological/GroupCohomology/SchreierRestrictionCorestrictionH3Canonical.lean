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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionH3
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionSylow

/-!
# Canonical degree-three restriction/corestriction consequences

Transversal independence upgrades the chosen-transversal degree-three index
formula to canonical corestriction.  Restriction is consequently injective
when the subgroup index is a unit, in particular for a Sylow subgroup with
positive prime-power coefficients.

The explicit prism homotopy remains in the chosen-transversal module; it is
not duplicated here.  No Kummer, generation, norm-residue, or Bloch--Kato
claim is made.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Canonical degree-three corestriction after restriction is multiplication
by the subgroup index. -/
theorem corestrictionH3_restriction
    (A : Rep k G) [H.FiniteIndex] (x : H3 A) :
    corestrictionH3 A
        (map (Subgroup.subtype H) (𝟙 _) 3 x) =
      (H.index : k) • x := by
  let T : H.RightTransversal := default
  rw [corestrictionH3_eq_of_rightTransversal A T]
  exact corestrictionH3OfRightTransversal_restriction A T x

/-- Linear-map form of the canonical degree-three
restriction/corestriction composite. -/
theorem corestrictionH3_comp_restriction
    (A : Rep k G) [H.FiniteIndex] :
    (corestrictionH3 A).comp
        (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
          (Subgroup.subtype H) (𝟙 _) 3).hom =
      (H.index : k) • LinearMap.id := by
  ext x
  exact corestrictionH3_restriction A x

/-- Canonical degree-three restriction is injective when the subgroup index
is a unit in the coefficient ring. -/
theorem restrictionH3_injective_of_isUnit_index_canonical
    (A : Rep k G) [H.FiniteIndex]
    (hindex : IsUnit (H.index : k)) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
        (Subgroup.subtype H) (𝟙 _) 3) := by
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  rw [← corestrictionH3_restriction A x,
    ← corestrictionH3_restriction A y, hxy]

section Sylow

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [Fact p.Prime]

/-- Canonical proof that restriction to a Sylow subgroup is injective on
`H3` over a positive prime-power `ZMod`. -/
theorem restrictionH3_injective_sylow_primePower_canonical
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3) :=
  restrictionH3_injective_of_isUnit_index_canonical A
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Canonical Sylow restriction detects zero degree-three classes. -/
theorem restrictionH3_sylow_eq_zero_iff_primePower_canonical
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x : H3 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restrictionH3_injective_sylow_primePower_canonical A P hd
    simpa using hx
  · rintro rfl
    exact map_zero _

/-- Canonical Sylow restriction detects equality of degree-three classes. -/
theorem restrictionH3_sylow_eq_iff_primePower_canonical
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H3 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 y ↔
      x = y :=
  (restrictionH3_injective_sylow_primePower_canonical A P hd).eq_iff

end Sylow

end groupCohomology
