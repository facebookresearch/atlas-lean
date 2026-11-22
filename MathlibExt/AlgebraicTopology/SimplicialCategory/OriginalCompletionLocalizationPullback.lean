/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelRightProper
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCofibrantCompletionWeak

/-!
# The actual localization pullback of an original cofibrant homotopy groupoid

The same original completion unit is genuinely weak. Factor an actual
map into that completion by the original full horn factorization, keeping
its middle object and both maps explicit. The literal original pullback
of the right C factor along the same completion unit has a genuinely weak
projection, with all original Hom maps and the full unit square retained.

This is the localization-existence input in Bergner's Section 4. It does
not supply the separate countable A2 interval extraction.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalCompletionLocalizationPullback
open ScalarGroupoidCompletion
variable {O : Type u} (C : FixedObjects O)
attribute [local instance] FixedObjectModel.modelCategory

variable {K : FixedObjects O} (f : K ⟶ fixedObject C)

/-- The actual original full horn factorization of the supplied map to the native completion. -/
abbrev factorization (f : K ⟶ fixedObject C) := FreeFactorization.horn f

/-- The actual middle replacement object is retained, as opposed to identifying it with its source. -/
abbrev middle : FixedObjects O := (factorization C f).Z

/-- The SAME original left replacement map. -/
abbrev left : K ⟶ middle C f := (factorization C f).i

/-- The SAME original right replacement map to the full native completion. -/
abbrev right : middle C f ⟶ fixedObject C := (factorization C f).p

/-- Both original replacement factors compose to the actual supplied full map. -/
theorem factors : left C f ≫ right C f = f := FreeFactorization.horn_fac f

/-- The literal original fixed-label pullback, retaining the full completion unit and right C factor. -/
abbrev object : FixedObjects O := pullback (fixedUnit C) (right C f)

/-- The actual full original projection into the unchanged original source. -/
abbrev toSource : object C f ⟶ C := pullback.fst _ _

/-- The actual full original projection into the retained replacement object. -/
abbrev toMiddle : object C f ⟶ middle C f := pullback.snd _ _

/-- The entire SAME original completion-unit pullback square. -/
theorem unit_square : toSource C f ≫ fixedUnit C = toMiddle C f ≫ right C f :=
  pullback.condition

/-- The actual right C factor is a genuine full Hom fibration in the original fixed-object model. -/
theorem right_fibration : FixedObjectModel.fibrations O (right C f) := (factorization C f).hp

/-- The SAME actual left replacement map is genuinely weak on every original full Hom. -/
theorem left_weak : FixedObjectModel.weakEquivalences O (left C f) :=
  FixedObjectModel.trivialCofibrations_le_weakEquivalences _ (factorization C f).hi

/-- The SAME actual original pullback projection is weak under genuine original source cofibrancy and groupoid
components. -/
theorem toMiddle_weak [IsCofibrant C] [IsGroupoid (ComponentCategory.objects.{u} C.val)] :
    FixedObjectModel.weakEquivalences O (toMiddle C f) :=
  FixedObjectModel.weak_of_isPullback (IsPullback.of_hasPullback (fixedUnit C) (right C f))
    (right_fibration C f) (FreeFactorization.cofibrantUnit_fixedWeak C)

/-- Every SAME complete original Hom projection to the replacement is genuinely realization weak. -/
theorem toMiddle_hom_weak [IsCofibrant C] [IsGroupoid (ComponentCategory.objects.{u} C.val)]
    (x y : (object C f).val) : SSet.realizationWeakEquivalences ((toMiddle C f).val.map x y) :=
  (FixedObjectModel.weakEquivalences_original_iff _).mp (toMiddle_weak C f) x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalCompletionLocalizationPullback
