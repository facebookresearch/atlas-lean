/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionUniversal
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanRetracts

/-!
# Actual strict scalar-groupoid comparison for the original completion

The SAME completed canonical scalar categories are genuine groupoids.
If the original canonical scalar categories already are groupoids, the
actual native full unit has a genuine entire enriched inverse; both
whole original triangle equations are proved by native universality.
Its original DK weakness follows from that actual Iso. This preserves
the genuine strict-groupoid hypotheses and does not infer the separate
cofibrant homotopy-groupoid completion weak theorem used in Lemma 2.4.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

/-- Every SAME completed canonical scalar category is genuinely a groupoid through its full original inverse maps. -/
instance completedScalar_isGroupoid (C : Carrier.{u}) (q : SimplexCategoryᵒᵖ) :
    IsGroupoid (SSet.ScalarObject (object C) q) where
  all_isIso {x y} a := by
    refine ⟨⟨(inverseMap C x.obj y.obj).app q a, ?_, ?_⟩⟩
    · exact comp_inverse C q x.obj y.obj a
    · exact inverse_comp C q x.obj y.obj a

variable (C : Carrier.{u}) [∀ q, IsGroupoid (SSet.ScalarObject C q)]

/-- The actual original strict-groupoid unit has the SAME native lift of the whole enriched identity as its inverse. -/
def inverse : object C ⟶ C := lift (𝟙 C)

/-- The SAME original unit followed by its actual full native inverse is the whole original identity. -/
theorem unit_inverse : unit C ≫ inverse C = 𝟙 C := unit_lift (𝟙 C)

/-- The actual full native inverse followed by the SAME original unit is the entire original completed identity. -/
theorem inverse_unit : inverse C ≫ unit C = 𝟙 (object C) := by
  apply unit_restriction_injective
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ unit C) (unit_inverse C)).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- The SAME full original unit and genuine native inverse give an actual enriched carrier isomorphism. -/
def unitIso : C ≅ object C where
  hom := unit C
  inv := inverse C
  hom_inv_id := unit_inverse C
  inv_hom_id := inverse_unit C

/-- The genuine Iso reads back to the SAME actual original completion unit exactly. -/
theorem unitIso_hom : (unitIso C).hom = unit C := rfl

/-- The SAME genuine Iso reads back to the whole native original inverse exactly. -/
theorem unitIso_inv : (unitIso C).inv = inverse C := rfl

/-- Actual strict scalar-groupoid hypotheses imply original DK weakness of the SAME full completion unit. -/
theorem unit_weak_of_scalarGroupoids : EnrichedDwyerKan.weakEquivalences (unit C) := by
  have : IsIso (unit C) := by change IsIso (unitIso C).hom; infer_instance
  exact EnrichedDwyerKan.weakEquivalences.of_isIso (unit C)

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
