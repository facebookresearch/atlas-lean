/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SyntenicDistanceDefs

namespace MetaMathlibExt.Complexity.NPComplete.SyntenicDistance

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SyntenicDistanceInstance) :
    syntenicDistanceDec (bitEncode i) = true ↔ WellFormed i ∧ SyntenicDistanceFeasible i := by
  simp [syntenicDistanceDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : syntenicDistanceDec [true] = false := by
  have h : bitDecode (α := SyntenicDistanceInstance) [true] = none := rfl
  simp [syntenicDistanceDec, h]

private theorem genome_split : genome [[1], [2]] = {1} ::ₘ {2} ::ₘ 0 := by decide

private theorem genome_fused : genome [[1, 2]] = ({1} ∪ {2}) ::ₘ 0 := by decide

/-- One fusion joins the two one-gene chromosomes, so the distance is at most one. -/
example :
    syntenicDistanceDec
      (bitEncode (([[1], [2]], [[1, 2]], 1) : SyntenicDistanceInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, 1, le_rfl,
    fun j => if j = 0 then genome [[1], [2]] else genome [[1, 2]], rfl, rfl, ?_⟩
  intro j hj
  obtain rfl : j = 0 := by omega
  show Move (genome [[1], [2]]) (genome [[1, 2]])
  rw [genome_split, genome_fused]
  exact Move.fusion 0 {1} {2} _ (by simp) (by simp) rfl

/-- The same genomes are rejected with bound zero: the genomes differ, so some move is needed. -/
example :
    syntenicDistanceDec
      (bitEncode (([[1], [2]], [[1, 2]], 0) : SyntenicDistanceInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, m, hm, g, h0, hm', -⟩
  obtain rfl : m = 0 := Nat.le_zero.1 hm
  rw [h0] at hm'
  revert hm'
  decide

/-- The rejected instance is well formed, so the rejection comes from the distance bound. -/
example : WellFormed (([[1], [2]], [[1, 2]], 0) : SyntenicDistanceInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.SyntenicDistance
