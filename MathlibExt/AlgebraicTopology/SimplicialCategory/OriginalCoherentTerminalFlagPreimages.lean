/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagSupport

/-!
# Native ordered preimages of original coefficient support

The native finite order isomorphism gives the actual selected index of
each original supported vertex, with both exact inverse equations.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag

variable {n : ℕ} {q : SimplexCategoryᵒᵖ}

/-- The native selected index of the same original supported vertex. -/
def preimage (p : (coefficientObject.{u} n).obj q) (j : Fin (n + 1))
    (hj : j ∈ support p) : Fin (dimension p + 1) :=
  ((support p).orderIsoOfFin (card_support p)).symm ⟨j, hj⟩

/-- The actual selected index maps back to the same original vertex. -/
theorem embedding_preimage (p : (coefficientObject.{u} n).obj q) (j : Fin (n + 1))
    (hj : j ∈ support p) :
    embedding p (preimage p j hj) = j :=
  congrArg Subtype.val (((support p).orderIsoOfFin (card_support p)).apply_symm_apply ⟨j, hj⟩)

/-- The actual supported vertex has precisely its original selected index. -/
theorem preimage_embedding (p : (coefficientObject.{u} n).obj q)
    (i : Fin (dimension p + 1)) :
    preimage p (embedding p i)
      (Finset.orderEmbOfFin_mem (support p) (card_support p) i) = i :=
  (embedding p).injective (embedding_preimage p (embedding p i) _)

end CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag
