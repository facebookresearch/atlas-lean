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
# Degree-three restriction and canonical corestriction

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `A` a representation.
The canonical maps satisfy `cor_H^G ∘ res_H^G = [G:H]` on `H³(G,A)`. If the image of this
index is a unit in `k`, restriction is injective.

For a finite group `G : Type`, a prime `p`, a positive exponent `d`, and
`ZMod(p^d)`-coefficients, a Sylow `p`-subgroup has invertible index. Its degree-three
restriction therefore detects vanishing and equality of classes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `A : Rep k G`. For `x ∈
H³(G,A)`, `corestrictionH3 A (map H.subtype (𝟙 _) 3 x) = (H.index : k) • x`. The map inside
corestriction is restriction to `H` with unchanged coefficients. -/
theorem corestrictionH3_restriction
    (A : Rep k G) [H.FiniteIndex] (x : H3 A) :
    corestrictionH3 A
        (map (Subgroup.subtype H) (𝟙 _) 3 x) =
      (H.index : k) • x := by
  let T : H.RightTransversal := default
  rw [corestrictionH3_eq_of_rightTransversal A T]
  exact corestrictionH3OfRightTransversal_restriction A T x

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `A : Rep k G`. The
linear endomorphism of `H³(G,A)` obtained by restriction followed by canonical corestriction
is `corestrictionH3 A ∘ (map H.subtype (𝟙 _) 3).hom = (H.index : k) • LinearMap.id`. -/
theorem corestrictionH3_comp_restriction
    (A : Rep k G) [H.FiniteIndex] :
    (corestrictionH3 A).comp
        (map (A := A) (B := Rep.res (Subgroup.subtype H) A)
          (Subgroup.subtype H) (𝟙 _) 3).hom =
      (H.index : k) • LinearMap.id := by
  ext x
  exact corestrictionH3_restriction A x

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `A : Rep k G`. If
`IsUnit (H.index : k)`, then `map H.subtype (𝟙 _) 3 : H³(G,A) → H³(H,Rep.res H.subtype A)` is
injective. -/
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

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. Restriction `res_P³ : H³(G,A) → H³(P,Res_P A)` along the subgroup
inclusion with the identity coefficient morphism is injective. -/
theorem restrictionH3_injective_sylow_primePower_canonical
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3) :=
  restrictionH3_injective_of_isUnit_index_canonical A
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x ∈ H³(G,A)`, `res_P³(x) = 0 ↔ x = 0`, where restriction uses the
subgroup inclusion and the identity coefficient map. -/
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

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x,y ∈ H³(G,A)`, `res_P³(x) = res_P³(y) ↔ x = y`, where restriction
is induced by the subgroup inclusion with unchanged coefficients. -/
theorem restrictionH3_sylow_eq_iff_primePower_canonical
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H3 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 3 y ↔
      x = y :=
  (restrictionH3_injective_sylow_primePower_canonical A P hd).eq_iff

end Sylow

end groupCohomology
