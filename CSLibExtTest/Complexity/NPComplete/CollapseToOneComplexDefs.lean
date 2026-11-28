/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CollapseToOneComplexDefs

namespace MetaMathlibExt.Complexity.NPComplete.CollapseToOneComplex

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CollapseToOneComplexInstance) :
    collapseToOneComplexDec (bitEncode i) = true ↔
      WellFormed i ∧ CollapseToOneComplexFeasible i := by
  simp [collapseToOneComplexDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : collapseToOneComplexDec [true] = false := by
  have h : bitDecode (α := CollapseToOneComplexInstance) [true] = none := rfl
  simp [collapseToOneComplexDec, h]

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsFacet topCard)

/-- The solid tetrahedron `{0, 1, 2, 3}` collapses to the three edges at vertex `3`: remove the
free triangle `{0, 1, 2}` with the tetrahedron, then the free edges `{0, 1}`, `{0, 2}` and
`{1, 2}` with the remaining triangles containing them. -/
example : collapseToOneComplexDec (bitEncode ([[0, 1, 2, 3]] : CollapseToOneComplexInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, _, ?_, (by decide :
    topCard ((((complex [[0, 1, 2, 3]]).filter fun ϑ => ¬ {0, 1, 2} ⊆ ϑ).filter fun ϑ =>
      ¬ {0, 1} ⊆ ϑ).filter (fun ϑ => ¬ {0, 2} ⊆ ϑ) |>.filter fun ϑ => ¬ {1, 2} ⊆ ϑ) ≤ 2)⟩
  refine .head ⟨{0, 1, 2}, by unfold IsFreeFace IsFacet; decide, rfl⟩ ?_
  refine .head ⟨{0, 1}, by unfold IsFreeFace IsFacet; decide, rfl⟩ ?_
  refine .head ⟨{0, 2}, by unfold IsFreeFace IsFacet; decide, rfl⟩ ?_
  exact .single ⟨{1, 2}, by unfold IsFreeFace IsFacet; decide, rfl⟩

/-- The boundary of the 4-simplex on `0, …, 4`: five tetrahedra forming a 3-sphere. -/
private abbrev sphere : CollapseToOneComplexInstance :=
  [[1, 2, 3, 4], [0, 2, 3, 4], [0, 1, 3, 4], [0, 1, 2, 4], [0, 1, 2, 3]]

/-- In the boundary of the 4-simplex every triangle lies in exactly two tetrahedra, so no face is
free, no elementary collapse applies, and the complex keeps dimension `3`. -/
example : collapseToOneComplexDec (bitEncode sphere) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, L, hL, htop⟩
  have nofree : ∀ σ ∈ complex sphere, ¬ IsFreeFace (complex sphere) σ := by
    unfold IsFreeFace IsFacet
    decide +kernel
  rcases hL.cases_head with rfl | ⟨c, ⟨σ, hσ, -⟩, -⟩
  · exact absurd htop (by decide +kernel)
  · exact nofree σ hσ.2.1 hσ

end MetaMathlibExt.Complexity.NPComplete.CollapseToOneComplex
