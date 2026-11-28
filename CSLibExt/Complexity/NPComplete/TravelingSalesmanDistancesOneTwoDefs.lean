/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TspDefs

/-!
# TRAVELING SALESMAN with distances 1 and 2: definitions

INSTANCE: a set `C` of `m` cities, a distance `d(cᵢ, cⱼ) ∈ {1, 2}` for each pair of distinct
cities, and a positive integer `B`. QUESTION: is there a tour of `C` having length `B` or less,
i.e., a permutation `⟨c_π(1), ..., c_π(m)⟩` of `C` with
`∑_{i < m} d(c_π(i), c_π(i+1)) + d(c_π(m), c_π(1)) ≤ B`?

This is TRAVELING SALESMAN (`WantedExt.Complexity.NPComplete.TspWanted`, Garey and Johnson
[ND22]) restricted as in the [ND22] comment: "Remains NP-complete even if `d(cᵢ, cⱼ) ∈ {1,2}`
for all `cᵢ, cⱼ ∈ C`." Garey and Johnson give no separate reference: the entry's
transformation from HAMILTONIAN CIRCUIT (NP-complete by Karp (1972)) already yields such
instances, with distance `1` between adjacent and `2` between non-adjacent vertices and
`B = m`, so that a tour of length `m` uses only edges of the graph. Papadimitriou and
Yannakakis (1993) study this special case as TSP(1,2).

The instance (city count `m`, distance matrix, bound), `Tsp.WellFormed` (`0 < m`, a symmetric
`m × m` matrix with zero diagonal) and `Tsp.TspFeasible` are reused unchanged; the restriction
adds to well-formedness that the distance between distinct cities is `1` or `2`, and Garey and
Johnson's positive bound `B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND22] TRAVELING SALESMAN, comment;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT);
C. H. Papadimitriou and M. Yannakakis, "The traveling salesman problem with distances one and
two", Mathematics of Operations Research 18 (1993), 1-11, doi:10.1287/moor.18.1.1.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TravelingSalesmanDistancesOneTwo

/-- Well-formedness of an instance: a well-formed TRAVELING SALESMAN instance (`0 < m`, a
symmetric `m × m` distance matrix with zero diagonal) in which the distance between any two
distinct cities is `1` or `2`, and `0 < B`. -/
def WellFormed (i : Tsp.TspInstance) : Prop :=
  Tsp.WellFormed i ∧
    (∀ a < i.1, ∀ b < i.1, a ≠ b →
      (i.2.1.getD a []).getD b 0 = 1 ∨ (i.2.1.getD a []).getD b 0 = 2) ∧
    0 < i.2.2

open Classical in
/-- TRAVELING SALESMAN with distances 1 and 2 as a decision problem over bitstrings. -/
noncomputable def travelingSalesmanDistancesOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Tsp.TspInstance) x with
  | some i => decide (WellFormed i ∧ Tsp.TspFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TravelingSalesmanDistancesOneTwo
