/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalUnitIntrinsicHo
import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKComposition

/-!
# Intrinsic Dwyer–Kan equivalence of the completion unit

The designated completion unit of a Segal space is an intrinsic Dwyer–Kan equivalence. Its
mapping-fibre weak equivalences and homotopy-category equivalence establish the criterion using
the constructed Segal structure on the target.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SimplicialSpace.RezkCompletionData

/-- The literal original completion unit is intrinsically DK, from the
constructed mapping-fibre and intrinsic homotopy-category comparisons. -/
theorem unit_intrinsicDK (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IntrinsicDK.isEquivalence (unit.app W) hW
      (RezkCompletionAllVertex.sameCompletion_segal W hW) :=
  (IntrinsicDK.iff_mappingWeak_and_HoIsEquivalence _ _ _).mpr
    (unit_full_mapping_fibres_and_intrinsicHo W hW)

end SimplicialSpace.RezkCompletionData
