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
# Coefficient naturality of canonical degree-three corestriction

For a morphism of `G`-representations, mapping coefficients commutes with
canonical finite-index corestriction in degree three.  The proof specializes
the chosen-transversal naturality square to the default transversal used by
the canonical wrapper.

No field-theoretic, Kummer, norm-residue, or Bloch--Kato claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Elementwise coefficient naturality of canonical degree-three
corestriction. -/
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

/-- Bundled linear-map square for coefficient naturality of canonical
degree-three corestriction. -/
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
