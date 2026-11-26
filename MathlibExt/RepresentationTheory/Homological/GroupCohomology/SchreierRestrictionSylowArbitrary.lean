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
# Restriction to Sylow subgroups in every degree

Let `G : Type` be a finite group, `p` a prime, `d : ℕ` positive, and `P` a Sylow `p`-subgroup.
For any representation `A` over `ZMod (p^d)` and every `n : ℕ`, restriction along `P → G`
gives an injection `H^n(G,A) → H^n(P,Res A)`. Consequently, vanishing and equality of classes
can be detected after restriction in each degree. The index `[G:P]` is invertible in the
coefficient ring.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] [Finite G]
variable {p d : ℕ} [hp : Fact p.Prime]

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For every `n : ℕ`, `res_P^n : H^n(G,A) → H^n(P,Rep.res
(Subgroup.subtype P) A)` is injective. This is the map induced by the subgroup inclusion with
the identity coefficient morphism. -/
theorem restriction_injective_sylow_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (n : ℕ) :
    Function.Injective
      (map (A := A)
        (B := Rep.res (Subgroup.subtype (P : Subgroup G)) A)
        (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n) := by
  exact restriction_injective_of_isUnit_index (H := (P : Subgroup G)) A n
    (sylowIndex_isUnit_zmod_primePower P hd)

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `n : ℕ` and `x ∈ H^n(G,A)`, `res_P^n(x) = 0 ↔ x = 0`, where
restriction is along `P → G` with unchanged coefficients. -/
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

/-- Let `G : Type` be a finite group, `p` prime, `d : ℕ` with `0 < d`, `P : Sylow p G`, and `A :
Rep (ZMod (p ^ d)) G`. For `n : ℕ` and `x,y ∈ H^n(G,A)`, `res_P^n(x) = res_P^n(y) ↔ x = y`,
where restriction is induced by the subgroup inclusion and the identity coefficient map. -/
theorem restriction_sylow_eq_iff_primePower
    (A : Rep (ZMod (p ^ d)) G) (P : Sylow p G) (hd : 0 < d)
    (n : ℕ) (x y : groupCohomology A n) :
    map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n x =
        map (Subgroup.subtype (P : Subgroup G)) (𝟙 _) n y ↔
      x = y :=
  (restriction_injective_sylow_primePower A P hd n).eq_iff

end groupCohomology
