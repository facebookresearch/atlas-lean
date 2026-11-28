/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BROADCAST TIME for fixed K ≥ 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME,
p. 219 (comment: "Remains NP-complete for any fixed `K ≥ 4`"; the entry's reference is
[Garey and Johnson, unpublished], "Transformation from 3DM").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumBroadcastTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeFixedK

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, and the base set `V₀` as a
list of vertices; the time bound `K` is fixed. -/
abbrev MinimumBroadcastTimeFixedKInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- The [ND49] instance `(n, E, V₀, K)` of a graph with base set `(n, E, V₀)` and the fixed
bound `K`. -/
def withBound (K : ℕ) (i : MinimumBroadcastTimeFixedKInstance) :
    MinimumBroadcastTime.MinimumBroadcastTimeInstance :=
  (i.1, i.2.1, i.2.2, K)

open Classical in
/-- MINIMUM BROADCAST TIME for a fixed bound `K` as a decision problem over bitstrings. -/
noncomputable def minimumBroadcastTimeFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumBroadcastTimeFixedKInstance) x with
  | some i => decide (MinimumBroadcastTime.WellFormed (withBound K i) ∧
      MinimumBroadcastTime.MinimumBroadcastTimeFeasible (withBound K i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeFixedK
