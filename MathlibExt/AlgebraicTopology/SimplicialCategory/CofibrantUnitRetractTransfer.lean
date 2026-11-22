/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryCofibrantRetract
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionFixedFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarBaseFunctor

/-!
# The original completion unit retains genuine original cofibrant retracts

The existing native natural-transformation retract theorem is applied to
the SAME original fixed completion unit and the genuine original boundary
section/projection. Every actual whole unit map and all original Hom maps
are retained. Weakness is transferred only from that actual source unit.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
open ScalarGroupoidCompletion
attribute [local instance] FixedObjectModel.modelCategory
variable {O : Type u} (C : FixedObjects O)

/-- The SAME original unit arrow is a retract of the SAME original boundary-source unit arrow. -/
def completionUnitRetract [IsCofibrant C] :
    RetractArrow (fixedUnit C) (fixedUnit (cofibrantSource C)) :=
  fixedNaturalUnit.retractArrowApp (cofibrantRetract C)

/-- Genuine weakness of the SAME source unit transfers to the SAME original cofibrant input unit. -/
theorem completionUnit_weak_of_source [IsCofibrant C]
    (h : FixedObjectModel.weakEquivalences O (fixedUnit (cofibrantSource C))) :
    FixedObjectModel.weakEquivalences O (fixedUnit C) :=
  MorphismProperty.of_retract (completionUnitRetract C) h

/-- The SAME original full labelled base unit arrow retains the genuine original retract. -/
def completionUnitBaseRetract [IsCofibrant C] :
    RetractArrow (scalarLabelBaseMap (fixedUnit C))
      (scalarLabelBaseMap (fixedUnit (cofibrantSource C))) :=
  (completionUnitRetract C).map scalarLabelBaseFunctor

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
