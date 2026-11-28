/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (d : ℕ) (i : CocomparabilityIntervalDimensionRecognitionInstance) :
    cocomparabilityIntervalDimensionRecognitionDec d (bitEncode i) = true ↔
      WellFormed i ∧ CocomparabilityIntervalDimensionRecognitionFeasible d i := by
  simp [cocomparabilityIntervalDimensionRecognitionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every `d`. -/
example (d : ℕ) : cocomparabilityIntervalDimensionRecognitionDec d [true] = false := by
  have h : bitDecode (α := CocomparabilityIntervalDimensionRecognitionInstance) [true] = none :=
    rfl
  simp [cocomparabilityIntervalDimensionRecognitionDec, h]

/-- Three vertices with the single edge `{0, 1}`. -/
private abbrev inst : CocomparabilityIntervalDimensionRecognitionInstance := (3, [(0, 1)])

/-- Left endpoints of the intervals `[0, 1]`, `[0, 1]`, `[2, 2]`. -/
private def lo (v : Fin 3) : ℕ := [0, 0, 2].getD v.val 0

/-- Right endpoints of the intervals `[0, 1]`, `[0, 1]`, `[2, 2]`. -/
private def hi (v : Fin 3) : ℕ := [1, 1, 2].getD v.val 0

set_option synthInstance.maxSize 1024 in
private theorem inst_compl : ∀ u v : Fin 3,
    (u ≠ v ∧ ¬ (u ≠ v ∧ ((u.val, v.val) ∈ inst.2 ∨ (v.val, u.val) ∈ inst.2))) ↔
      (hi u < lo v ∨ hi v < lo u) := by
  decide

/-- The interval order of `[0, 1]`, `[0, 1]`, `[2, 2]` (vertices `0` and `1` incomparable, both
below `2`) has interval dimension `1`, so for every `d ≥ 1` its co-comparability graph, the
single edge `{0, 1}` plus the isolated vertex `2`, is accepted. -/
private theorem inst_feasible (d : ℕ) (hd : 1 ≤ d) :
    CocomparabilityIntervalDimensionRecognitionFeasible d inst := by
  have hle : ∀ v, lo v ≤ hi v := by decide
  refine ⟨fun u v => hi u < lo v,
    { irrefl := fun v h => absurd (hle v) (Nat.not_le.2 h)
      trans := fun u v w h₁ h₂ => Nat.lt_of_lt_of_le h₁ (Nat.le_trans (hle v) (Nat.le_of_lt h₂)) },
    fun u v => ?_, 1, hd, fun _ v => (lo v : ℝ), fun _ v => (hi v : ℝ),
    fun _ v => Nat.cast_le.2 (hle v), fun u v => by simp⟩
  rw [SimpleGraph.compl_adj, ← inst_compl]
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

example : cocomparabilityIntervalDimensionRecognitionDec 1 (bitEncode inst) = true :=
  (accepts_encoding 1 _).2 ⟨by unfold WellFormed; decide, inst_feasible 1 le_rfl⟩

example : cocomparabilityIntervalDimensionRecognitionDec 2 (bitEncode inst) = true :=
  (accepts_encoding 2 _).2 ⟨by unfold WellFormed; decide, inst_feasible 2 (by decide)⟩

/-- With `d = 0` the empty family of interval orders makes `r u v` hold for all `u` and `v`,
contradicting irreflexivity, so the same well-formed graph is rejected. -/
example : cocomparabilityIntervalDimensionRecognitionDec 0 (bitEncode inst) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, r, hr, -, k, hk, l, h, -, hiff⟩
  obtain rfl : k = 0 := Nat.le_zero.1 hk
  exact hr.irrefl 0 ((hiff 0 0).2 fun j => j.elim0)

end MetaMathlibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognition
