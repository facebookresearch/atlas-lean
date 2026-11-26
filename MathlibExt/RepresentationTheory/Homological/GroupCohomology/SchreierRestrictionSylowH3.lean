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

Let `G : Type` be a finite group, `p` a prime, `d : ℕ` positive, and `P` a Sylow `p`-subgroup.
For any `ZMod (p^d)`-representation `A`, restriction is injective on `H³(G,A)` and detects
both zero classes and equality. The restriction–corestriction composite multiplies by `[G:P]`,
which is a unit in `ZMod (p^d)`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [Fact p.Prime]

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. Restriction `res_P³ : H³(G,A) → H³(P,Rep.res (Subgroup.subtype P) A)`
along the subgroup inclusion with the identity coefficient morphism is injective. -/
theorem restrictionH3_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3) :=
  restrictionH3_injective_of_isUnit_index A
    (default : (P : Subgroup G).RightTransversal)
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x ∈ H³(G,A)`, `res_P³(x) = 0 ↔ x = 0`, where restriction uses the
subgroup inclusion `P → G` and the identity coefficient map. -/
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

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x,y ∈ H³(G,A)`, `res_P³(x) = res_P³(y) ↔ x = y`, where restriction
is induced by the subgroup inclusion with unchanged coefficients. -/
theorem restrictionH3_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H3 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 y ↔
      x = y :=
  (restrictionH3_injective_sylow_primePower A P hd).eq_iff

end groupCohomology
