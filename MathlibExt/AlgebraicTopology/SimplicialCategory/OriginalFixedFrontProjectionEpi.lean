/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCollapse

/-!
# The entire original fixed-front projection is epi

Every original quotient simplex has an actual original successor
representative. The original full projection is therefore epi in every
scalar degree and as a whole simplicial-set map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The SAME complete original fixed-front projection is epi in every original dimension. -/
theorem projection_epi (n : ℕ) : Epi (FixedFrontCollapse.projection.{u} n) := by
  let _ : ∀ q, Epi ((FixedFrontCollapse.projection.{u} n).app q) := fun q =>
    (CategoryTheory.epi_iff_surjective _).mpr (fun p => _root_.Quotient.exists_rep p)
  exact NatTrans.epi_of_epi_app _

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
