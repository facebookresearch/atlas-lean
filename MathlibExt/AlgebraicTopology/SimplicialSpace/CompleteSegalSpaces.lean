/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyModel
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps

/-!
# Complete Segal spaces through inner locality

Following Rezk, §4 and Proposition 6.4(3), a complete Segal space is Reedy-fibrant
and local for every Segal spine inclusion in dimension at least two and the map
from the zero representable to the full walking-isomorphism nerve. Restrictions
are evaluated in the actual pointwise inner enriched end.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory HomotopicalAlgebra Opposite
open scoped SimplicialSpace.Inner

namespace SimplicialSpace

/-- Reedy-fibrant objects local for the full original Segal/E family. -/
def completeSegalSpaces : ObjectProperty SimplicialSpace.{u} := by
  letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact fun W => IsFibrant W ∧
    ∀ a : SSet.Rezk.LocalizingIndex,
      SSet.realizationWeakEquivalences
        ((innerHomFunctor.map
          (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} a).hom).op).app W)

end SimplicialSpace
