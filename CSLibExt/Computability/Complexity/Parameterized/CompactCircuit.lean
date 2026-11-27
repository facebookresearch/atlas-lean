/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Support
public import CSLibExt.Computability.Complexity.Parameterized.Weft

/-!
# Compressing the variables of a serialized circuit

The variable count is binary, so even a single gate can belong to a circuit
declaring exponentially many variables. Compress the variable domain before
enumerating assignments to the slots of the consistency graph.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support

open MetaMathlibExt.BitstringEncoding

/-- Preprocess a serialized instance. An excessive weight or a malformed
encoding maps to the empty string, which the circuit decoder rejects. -/
def compact (p : List Bool × ℕ) : List Bool × ℕ :=
  match bitDecode (α := ℕ × List WCGate) p.1 with
  | none => ([], 0)
  | some (n, C) =>
    if p.2 ≤ n then
      let L := labels n p.2 C
      (bitEncode (L.length, C.map (reindexGate n L)), min p.2 (active n C).card)
    else ([], 0)

/-- Preprocessing never increases the parameter. -/
theorem compact_weight_le (p : List Bool × ℕ) : (compact p).2 ≤ p.2 := by
  unfold compact
  split
  · exact Nat.zero_le _
  · split
    · exact min_le_left ..
    · exact Nat.zero_le _

/-- Every input, including an excessive weight or an undecodable circuit,
has the same answer after preprocessing. -/
theorem compact_correct (t d : ℕ) (x : List Bool) (k : ℕ) :
    WeightedCircuitSat t d x k ↔
      WeightedCircuitSat t d (compact (x, k)).1 (compact (x, k)).2 := by
  have hnil : bitDecode (α := ℕ × List WCGate) [] = none := rfl
  cases h : bitDecode (α := ℕ × List WCGate) x with
  | none => simp [compact, WeightedCircuitSat, h, hnil]
  | some p =>
    obtain ⟨n, C⟩ := p
    by_cases hk : k ≤ n
    · have he : bitDecode (α := ℕ × List WCGate) x = bitDecode (bitEncode (n, C)) := by
        simpa only [bitDecode_bitEncode] using h
      rw [weightedCircuitSat_congr_decode he t d k]
      simpa only [compact, h, hk, ↓reduceIte] using reindex_correct n k hk C t d
    · have impossible : ¬ ∃ a : List Bool, a.length = n ∧ (a.filter id).length = k ∧
            (wcCircuitEval C a).getLast? = some true := by
        rintro ⟨a, ha, hw, _⟩
        exact hk (hw ▸ ha ▸ List.length_filter_le id a)
      simp [compact, WeightedCircuitSat, h, hk, impossible, hnil]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support
