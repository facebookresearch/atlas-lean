/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.EvenNoncrossingDyckDescents

open MetaMathlibExt DyckStep

-- The empty partition and path are included in the statement.
example : Nonempty
    ({P : NoncrossingPartition 0 // ∀ B ∈ P.val.parts, Even B.card} ≃
      {p : DyckWord // p.semilength = 0 ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j}) := by
  simpa using nonempty_equiv_evenNoncrossing_evenDescentDyck 0

-- A path with two even descents can be recovered from a partition, not just
-- from a single block of size four.
example : ∃ (e : {P : NoncrossingPartition 4 // ∀ B ∈ P.val.parts, Even B.card} ≃
    {p : DyckWord // p.semilength = 4 ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j}),
    ∃ P, (e P).val.toList = [U, U, U, D, D, U, D, D] := by
  obtain ⟨e⟩ := nonempty_equiv_evenNoncrossing_evenDescentDyck 2
  let p : DyckWord := ((0 : DyckWord).nest.nest + (0 : DyckWord).nest).nest
  have hp : p.semilength = 4 ∧ ∀ j ∈ dyckPeakDescents p.toList, Even j := by
    change 4 = 4 ∧ ∀ j ∈ ([2, 2] : List ℕ), Even j
    simp
  refine ⟨e, e.symm ⟨p, hp⟩, ?_⟩
  rw [e.apply_symm_apply]
  rfl
