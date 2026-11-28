/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaximumCoverageLocationDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MaximumCoverageLocationInstance) :
    maximumCoverageLocationDec (bitEncode i) = true ↔
      WellFormed i ∧ MaximumCoverageLocationFeasible i := by
  simp [maximumCoverageLocationDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MaximumCoverageLocationInstance) bits = none) :
    maximumCoverageLocationDec bits = false := by
  simp [maximumCoverageLocationDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : maximumCoverageLocationDec [true] = false :=
  rejects_undecodable [true] rfl

/-- One edge `{0, 1}` of length `2`; each vertex has a customer of gain `1` and radius `2 / 1`;
one point; target `2`. -/
private abbrev edgeInst : MaximumCoverageLocationInstance :=
  (2, [(0, 1, 2)], [(1, 2, 1), (1, 2, 1)], 1, 2)

/-- Two isolated vertices, each with a customer of gain `1` and radius `1 / 1`; one point;
target `2`. -/
private abbrev isolatedInst : MaximumCoverageLocationInstance :=
  (2, [], [(1, 1, 1), (1, 1, 1)], 1, 2)

private theorem univ_fin_two : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide

/-- The midpoint of the edge is at distance `1 < 2` from both customers, gaining `1 + 1 = 2`. -/
example : maximumCoverageLocationDec (bitEncode edgeInst) = true := by
  apply (accepts_encoding _).2
  have hlen : edgeLength edgeInst s(0, 1) = 2 := by decide
  have hadj : (Graph edgeInst).Adj 0 1 := by
    simp [Graph, Cslib.Complexity.Karp.edgeGraph]
  have hrad : ∀ v, radius edgeInst v = 2 := by
    intro v
    rcases v with ⟨_ | _ | n, hn⟩
    · simp [radius]
    · simp [radius]
    · exact absurd hn (by simp)
  have hcov : ∀ v, ∃ x ∈ ({(0, 1, 1)} : Finset (Fin edgeInst.1 × Fin edgeInst.1 × ℝ)),
      DistLT edgeInst v x (radius edgeInst v) := by
    intro v
    refine ⟨(0, 1, 1), Finset.mem_singleton_self _, ?_⟩
    rw [hrad]
    rcases v with ⟨_ | _ | n, hn⟩
    · refine Or.inl ⟨SimpleGraph.Walk.nil, ?_⟩
      simp only [walkLength, SimpleGraph.Walk.edges_nil, List.map_nil, List.sum_nil,
        Nat.cast_zero, zero_add]
      exact one_lt_two
    · refine Or.inr ⟨SimpleGraph.Walk.nil, ?_⟩
      simp only [walkLength, SimpleGraph.Walk.edges_nil, List.map_nil, List.sum_nil,
        Nat.cast_zero, zero_add, hlen, Nat.cast_ofNat]
      rw [sub_eq_iff_eq_add.2 one_add_one_eq_two.symm]
      exact one_lt_two
    · exact absurd hn (by simp)
  refine ⟨by unfold WellFormed; decide, {(0, 1, 1)}, by simp, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    refine Or.inr ⟨hadj, by norm_num, ?_⟩
    rw [hlen]
    norm_num
  · rw [Finset.sum_filter, univ_fin_two, Finset.sum_pair (by decide),
      ite_eq_left (hcov 0), ite_eq_left (hcov 1)]
    simp [gain]

/-- Without edges a point reaches only its own vertex, so it gains at most `1 < 2`. -/
example : maximumCoverageLocationDec (bitEncode isolatedInst) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, P, hcard, hon, hW⟩
  have hwalk : ∀ {u v : Fin 2}, (Graph isolatedInst).Walk u v → u = v := by
    intro u v W
    cases W with
    | nil => rfl
    | cons h _ => simp [Graph, Cslib.Complexity.Karp.edgeGraph] at h
  have hreach : ∀ v : Fin 2, ∀ x ∈ P, ∀ t, DistLT isolatedInst v x t → v = x.1 := by
    intro v x hx t hd
    have hx1 : x.1 = x.2.1 := by
      rcases hon x hx with h | ⟨h, -⟩
      · exact h.1
      · simp [Graph, Cslib.Complexity.Karp.edgeGraph] at h
    rcases hd with ⟨W, -⟩ | ⟨W, -⟩
    · exact hwalk W
    · rw [hx1]; exact hwalk W
  have hnot : ¬ ((∃ x ∈ P, DistLT isolatedInst 0 x (radius isolatedInst 0)) ∧
      ∃ x ∈ P, DistLT isolatedInst 1 x (radius isolatedInst 1)) := by
    rintro ⟨⟨x, hx, h0⟩, ⟨y, hy, h1⟩⟩
    have hxy : y = x := Finset.card_le_one.1 hcard y hy x hx
    subst hxy
    exact absurd ((hreach 0 y hx _ h0).trans (hreach 1 y hy _ h1).symm) (by decide)
  rw [Finset.sum_filter, univ_fin_two, Finset.sum_pair (by decide)] at hW
  have hg : ∀ v, gain isolatedInst v = 1 := by
    intro v
    rcases v with ⟨_ | _ | n, hn⟩
    · rfl
    · rfl
    · exact absurd hn (by simp)
  simp only [hg] at hW
  by_cases h0 : ∃ x ∈ P, DistLT isolatedInst 0 x (radius isolatedInst 0)
  · have h1 : ¬ ∃ x ∈ P, DistLT isolatedInst 1 x (radius isolatedInst 1) :=
      fun h1 => hnot ⟨h0, h1⟩
    rw [ite_eq_left h0, ite_eq_right h1] at hW
    exact absurd hW (by decide)
  · rw [ite_eq_right h0] at hW
    split at hW <;> exact absurd hW (by decide)

/-- A customer with radius numerator `0` is malformed. -/
example :
    maximumCoverageLocationDec (bitEncode
      ((2, [(0, 1, 2)], [(1, 0, 1), (1, 2, 1)], 1, 1) : MaximumCoverageLocationInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, h⟩, -⟩
  exact absurd (h (1, 0, 1) (by simp)).1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation
