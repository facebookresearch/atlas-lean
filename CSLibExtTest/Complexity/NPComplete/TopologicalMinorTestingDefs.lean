/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TopologicalMinorTestingDefs

namespace MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TopologicalMinorTestingInstance) :
    topologicalMinorTestingDec (bitEncode i) = true ↔
      WellFormed i ∧ TopologicalMinorTestingFeasible i := by
  simp [topologicalMinorTestingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : topologicalMinorTestingDec [true] = false := by
  have h : bitDecode (α := TopologicalMinorTestingInstance) [true] = none := rfl
  simp [topologicalMinorTestingDec, h]

/-- The path `0 - 1 - 2` as a host graph. -/
private abbrev path3 : TopologicalMinorTestingInstance := (3, [(0, 1), (1, 2)], 2, [(0, 1)])

private theorem adj01 : (Graph path3).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem adj12 : (Graph path3).Adj 1 2 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The path `0 - 1 - 2` contains a subdivision of a single edge: map its ends to `0` and
`2` and route the edge through `1`. -/
example : topologicalMinorTestingDec (bitEncode path3) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun c => if (c : ℕ) = 0 then 0 else 2,
    fun _ => ⟨0, 2, .cons adj01 (.cons adj12 .nil)⟩, ?_, ?_, ?_, ?_⟩
  · intro a b h
    revert a b
    decide
  · intro j
    obtain rfl : j = ⟨0, by decide⟩ := Fin.ext (by have := j.isLt; simp [path3] at this ⊢)
    refine ⟨0, 1, rfl, rfl, rfl, rfl, ?_⟩
    rw [SimpleGraph.Walk.isPath_def]
    decide
  · intro j w hw c hc
    revert w
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    revert c
    decide
  · intro j l hjl
    exact absurd (Fin.ext (by have := j.isLt; have := l.isLt; simp at *)) hjl

/-- The two-vertex graph with no edges does not contain a subdivision of an edge: its two
branch vertices are distinct and no walk joins distinct vertices. -/
example :
    topologicalMinorTestingDec
      (bitEncode ((2, [], 2, [(0, 1)]) : TopologicalMinorTestingInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, φ, paths, hinj, hends, -, -⟩
  obtain ⟨a, b, ha, hb, hu, hv, -⟩ := hends ⟨0, by simp⟩
  have hab : a ≠ b := fun h => by simp [h] at ha hb; omega
  have hconst : ∀ u v, (Graph ((2, [], 2, [(0, 1)]) : TopologicalMinorTestingInstance)).Walk u v →
      u = v := by
    intro u v p
    cases p with
    | nil => rfl
    | cons h _ => simp [Graph, Cslib.Complexity.Karp.edgeGraph] at h
  exact hab (hinj (hu.symm.trans ((hconst _ _ (paths ⟨0, by simp⟩).2.2).trans hv)))

/-- The rejected instance is well formed, so the rejection comes from the missing edge. -/
example : WellFormed ((2, [], 2, [(0, 1)]) : TopologicalMinorTestingInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting
