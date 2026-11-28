/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DCollapsibilityDefs

namespace MetaMathlibExt.Complexity.NPComplete.DCollapsibility

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsSimplicialComplex IsFacet)

private theorem accepts_encoding (d : ℕ) (i : DCollapsibilityInstance) :
    dCollapsibilityDec d (bitEncode i) = true ↔ WellFormed i ∧ DCollapsibilityFeasible d i := by
  simp [dCollapsibilityDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every `d`. -/
example (d : ℕ) : dCollapsibilityDec d [true] = false := by
  have h : bitDecode (α := DCollapsibilityInstance) [true] = none := rfl
  simp [dCollapsibilityDec, h]

/-- The path `0 - 1 - 2`: two edges sharing the vertex `1`, with all their faces. -/
private abbrev path : DCollapsibilityInstance := [[], [0], [1], [2], [0, 1], [1, 2]]

/-- The boundary of the triangle `012`: three edges, three vertices and the empty face. -/
private abbrev hollowTriangle : DCollapsibilityInstance :=
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2]]

private theorem wellFormed_path : WellFormed path := by
  unfold WellFormed IsSimplicialComplex
  decide

private theorem wellFormed_hollowTriangle : WellFormed hollowTriangle := by
  unfold WellFormed IsSimplicialComplex
  decide

/-- A complex with no elementary `d`-collapse that is not already empty is not
`d`-collapsible. -/
private theorem not_feasible_of_stuck {d : ℕ} {i : DCollapsibilityInstance}
    (hne : complex i ≠ ∅) (hstuck : ∀ K', ¬ ElementaryCollapse d (complex i) K') :
    ¬ DCollapsibilityFeasible d i := fun h =>
  match Relation.ReflTransGen.cases_head h with
  | .inl e => hne e
  | .inr ⟨K', hK', _⟩ => hstuck K' hK'

/-- `d = 1`: the vertex `0` lies only in the edge `01`, so it collapses away with that edge,
leaving the edge `12`, whose empty face then lies in a unique facet. -/
example : dCollapsibilityDec 1 (bitEncode path) = true := by
  refine (accepts_encoding _ _).2 ⟨wellFormed_path, ?_⟩
  refine .head (b := (complex path).filter fun η => ¬ ({0} ⊆ η ∧ η ⊆ {0, 1}))
    ⟨{0}, by decide, by decide, {0, 1}, by decide, by unfold IsFacet; decide, by decide,
      by unfold IsFacet; decide, rfl⟩ (.single ?_)
  exact ⟨∅, by decide, by decide, {1, 2}, by decide, by unfold IsFacet; decide, by decide,
    by unfold IsFacet; decide, by decide⟩

/-- `d = 0`: only the empty face may be collapsed, and it lies in the two facets `01` and
`12`, so the path is stuck although its `1`-collapse exists. -/
example : dCollapsibilityDec 0 (bitEncode path) = false := by
  have h : ¬ DCollapsibilityFeasible 0 path := by
    refine not_feasible_of_stuck (by decide) fun K' ⟨σ, hσ, hc, τ, hτ, hf, hs, hu, _⟩ => ?_
    obtain rfl : σ = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hc)
    have h₁ := hu {0, 1} (by decide) (by unfold IsFacet; decide) (Finset.empty_subset _)
    have h₂ := hu {1, 2} (by decide) (by unfold IsFacet; decide) (Finset.empty_subset _)
    exact absurd (h₁.trans h₂.symm) (by decide)
  simp [dCollapsibilityDec, bitDecode_bitEncode, h]

/-- `d = 1`: every vertex of the hollow triangle lies in two edges and the empty face in three,
so no elementary `1`-collapse applies. -/
example : dCollapsibilityDec 1 (bitEncode hollowTriangle) = false := by
  have h : ¬ DCollapsibilityFeasible 1 hollowTriangle := by
    refine not_feasible_of_stuck (by decide) fun K' hK' => ?_
    obtain ⟨σ, hσ, hc, τ, hτ, hf, hs, hu, -⟩ := hK'
    revert σ τ
    unfold IsFacet
    decide
  simp [dCollapsibilityDec, bitDecode_bitEncode, h]

/-- `d = 2`: an edge may be collapsed as its own unique facet, after which the remaining path
collapses as before. -/
example : dCollapsibilityDec 2 (bitEncode hollowTriangle) = true := by
  refine (accepts_encoding _ _).2 ⟨wellFormed_hollowTriangle, ?_⟩
  refine .head (b := (complex hollowTriangle).filter fun η => ¬ ({0, 1} ⊆ η ∧ η ⊆ {0, 1}))
    ⟨{0, 1}, by decide, by decide, {0, 1}, by decide, by unfold IsFacet; decide, by decide,
      by unfold IsFacet; decide, rfl⟩ (.head ⟨{0}, by decide, by decide, {0, 2}, by decide,
        by unfold IsFacet; decide, by decide, by unfold IsFacet; decide, rfl⟩ (.single ?_))
  exact ⟨∅, by decide, by decide, {1, 2}, by decide, by unfold IsFacet; decide, by decide,
    by unfold IsFacet; decide, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.DCollapsibility
