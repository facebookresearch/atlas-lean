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
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThreeNaturality

/-!
# Coefficient naturality of degree-three corestriction

Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `φ : A → B` a
morphism of representations. The canonical transfer satisfies `φ_* ∘ cor_A³ = cor_B³ ∘ (Res
φ)_*` as maps `H³(H,Res A) → H³(G,B)`. The identity is given both on individual classes and as
an equality of linear maps.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `φ : A → B` a
morphism of `G`-representations. For `x ∈ H³(H,Res A)`, `map (id G) φ 3 (corestrictionH3 A x)
= corestrictionH3 B (map (id H) (Res φ) 3 x)`, where `Res φ = (Rep.resFunctor
(Subgroup.subtype H)).map φ`. -/
theorem corestrictionH3_naturality_apply
    {A B : Rep k G} (φ : A ⟶ B) [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype H) A)) :
    map (MonoidHom.id G) φ 3 (corestrictionH3 A x) =
      corestrictionH3 B
        (map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 3 x) := by
  unfold corestrictionH3
  exact corestrictionH3OfRightTransversal_naturality_apply
    φ (default : H.RightTransversal) x

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `φ : A → B` a
morphism of representations. The linear maps from `H³(H,Res A)` to `H³(G,B)` satisfy `(map (id
G) φ 3).hom ∘ corestrictionH3 A = corestrictionH3 B ∘ (map (id H) (Res φ) 3).hom`, with `Res
φ` induced by restriction to `H`. -/
theorem corestrictionH3_naturality
    {A B : Rep k G} (φ : A ⟶ B) [H.FiniteIndex] :
    (map (MonoidHom.id G) φ 3).hom.comp (corestrictionH3 A) =
      (corestrictionH3 B).comp
        (map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 3).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH3_naturality_apply φ x

end groupCohomology
