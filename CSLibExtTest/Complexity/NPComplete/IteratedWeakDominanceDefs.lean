/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.IteratedWeakDominanceDefs

namespace MetaMathlibExt.Complexity.NPComplete.IteratedWeakDominance

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : IteratedWeakDominanceInstance) :
    iteratedWeakDominanceDec (bitEncode i) = true ↔
      WellFormed i ∧ IteratedWeakDominanceFeasible i := by
  simp [iteratedWeakDominanceDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := IteratedWeakDominanceInstance) bits = none) :
    iteratedWeakDominanceDec bits = false := by
  simp [iteratedWeakDominanceDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : iteratedWeakDominanceDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Two row strategies against one column strategy: row `0` pays the row player `1` and row `1`
pays `0`; the distinguished strategy is row `1`. -/
private abbrev dominatedInst : IteratedWeakDominanceInstance :=
  (2, 1, [[((1, 0), (0, 0))], [((0, 0), (0, 0))]], false, 1)

/-- The same game with all payoffs `0`. -/
private abbrev tiedInst : IteratedWeakDominanceInstance :=
  (2, 1, [[((0, 0), (0, 0))], [((0, 0), (0, 0))]], false, 1)

/-- Row `1` is strictly worse than row `0` against the only column, so one elimination step
removes it. -/
example : iteratedWeakDominanceDec (bitEncode dominatedInst) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, (Finset.univ.erase 1, Finset.univ), ?_, ?_⟩
  · refine Relation.ReflTransGen.single (Or.inl ⟨1, Finset.mem_univ _, ?_, rfl⟩)
    refine ⟨0, Finset.mem_univ _, ?_, ?_⟩
    · unfold rowUtility entry; decide
    · unfold rowUtility entry; decide
  · show ∀ r ∈ (Finset.univ.erase 1 : Finset (Fin 2)), (r : ℕ) ≠ 1
    decide

/-- With all payoffs equal no strategy is weakly dominated, so nothing is ever eliminated. -/
example : iteratedWeakDominanceDec (bitEncode tiedInst) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, S, hreach, hgone⟩
  have hstuck : ∀ T, ¬ EliminationStep tiedInst (Finset.univ, Finset.univ) T := by
    rintro T (⟨r, -, ⟨r', -, -, c, -, hlt⟩, -⟩ | ⟨c, -, ⟨c', -, -, r, -, hlt⟩, -⟩)
    · revert hlt; unfold rowUtility entry; revert r r' c; decide
    · revert hlt; unfold colUtility entry; revert c c' r; decide
  have hS : S = (Finset.univ, Finset.univ) := by
    rcases hreach.cases_head with h | ⟨T, hT, -⟩
    · exact h.symm
    · exact absurd hT (hstuck T)
  subst hS
  exact hgone 1 (Finset.mem_univ _) rfl

/-- A distinguished row index past the last row is malformed. -/
example :
    iteratedWeakDominanceDec (bitEncode
      ((2, 1, [[((1, 0), (0, 0))], [((0, 0), (0, 0))]], false, 2) :
        IteratedWeakDominanceInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, -, -, h⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.IteratedWeakDominance
