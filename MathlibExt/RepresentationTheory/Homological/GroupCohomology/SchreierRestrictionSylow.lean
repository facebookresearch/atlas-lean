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
# Degree-one and degree-two restriction to Sylow subgroups

Let `G : Type` be a finite group, `p` a prime, `d : ℕ` positive, and `P` a Sylow `p`-subgroup.
The index `[G:P]` is a unit in `ZMod (p^d)`. Hence, for any `ZMod (p^d)`-representation `A`,
the restriction maps `H¹(G,A) → H¹(P,Res A)` and `H²(G,A) → H²(P,Res A)` are injective. Each
restriction detects vanishing and equality of classes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [hp : Fact p.Prime]

/-- Let `G : Type` be a finite group, `p : ℕ` prime, `P : Sylow p G`, and `d : ℕ` with `0 < d`.
Then `IsUnit (P.index : ZMod (p ^ d))`; equivalently, the subgroup index `[G:P]` is invertible
modulo `p^d`, since `p` does not divide this index. -/
theorem sylowIndex_isUnit_zmod_primePower
    (P : Sylow p G) (hd : 0 < d) :
    IsUnit (P.index : ZMod (p ^ d)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp.out hd).2 P.not_dvd_index

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. The map `res_P¹ : H¹(G,A) → H¹(P,Rep.res (Subgroup.subtype P) A)`
induced by the subgroup inclusion and the identity coefficient morphism is injective. -/
theorem restrictionH1_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1) :=
  restrictionH1_injective_of_isUnit_index A
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. The map `res_P² : H²(G,A) → H²(P,Rep.res (Subgroup.subtype P) A)`
induced by the subgroup inclusion and the identity coefficient morphism is injective. -/
theorem restrictionH2_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d) :
    Function.Injective
      (map (A := A) (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2) :=
  restrictionH2_injective_of_isUnit_index A
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x ∈ H¹(G,A)`, `res_P¹(x) = 0 ↔ x = 0`, where `res_P¹` is induced
by the subgroup inclusion `P → G` with the identity coefficient map. -/
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

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x,y ∈ H¹(G,A)`, `res_P¹(x) = res_P¹(y) ↔ x = y`, where restriction
is along the subgroup inclusion with the identity coefficient morphism. -/
theorem restrictionH1_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H1 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 1 y ↔
      x = y :=
  (restrictionH1_injective_sylow_primePower A P hd).eq_iff

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x ∈ H²(G,A)`, `res_P²(x) = 0 ↔ x = 0`, where `res_P²` is induced
by the subgroup inclusion `P → G` and the identity coefficient morphism. -/
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

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `x,y ∈ H²(G,A)`, `res_P²(x) = res_P²(y) ↔ x = y`, where restriction
is along the subgroup inclusion with the identity coefficient morphism. -/
theorem restrictionH2_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (x y : H2 A) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2 x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) 2 y ↔
      x = y :=
  (restrictionH2_injective_sylow_primePower A P hd).eq_iff

end groupCohomology
