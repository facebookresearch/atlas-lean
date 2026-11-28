/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED COMPONENT SPANNING FOREST with unit weights and fixed `B ≥ 3`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND10] BOUNDED COMPONENT SPANNING FOREST,
p. 208, comment: "Remains NP-complete even if all weights equal 1 and B is any fixed integer
larger than 2 [Garey and Johnson, ——]" (unpublished);
M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected
subgraphs", Discrete Applied Mathematics 10 (1985), 139-153, doi:10.1016/0166-218X(85)90008-3,
Theorem 2.1(a).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedComponentSpanningForestDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedB

open MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest
  (BoundedComponentSpanningForestInstance BoundedComponentSpanningForestFeasible)

/-- An instance for a fixed bound `B`: vertex count `n` (vertices `Fin n`), edge list, vertex
weights `[w 0, …, w (n - 1)]`, and the bound `K` on the number of parts. -/
abbrev FixedBoundInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The BOUNDED COMPONENT SPANNING FOREST instance given by `i` and the weight bound `B`. -/
abbrev withBound (i : FixedBoundInstance) (B : ℕ) : BoundedComponentSpanningForestInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2, B)

/-- Well-formedness of an instance for the bound `B`: the BOUNDED COMPONENT SPANNING FOREST
instance `withBound i B` is well-formed, and every vertex weight is `1`. -/
def WellFormed (B : ℕ) (i : FixedBoundInstance) : Prop :=
  BoundedComponentSpanningForest.WellFormed (withBound i B) ∧ ∀ x ∈ i.2.2.1, x = 1

open Classical in
/-- BOUNDED COMPONENT SPANNING FOREST with unit weights and the weight bound fixed to `B`, as a
decision problem over bitstrings. -/
noncomputable def boundedComponentSpanningForestUnitWeightsDec (B : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed B i ∧ BoundedComponentSpanningForestFeasible (withBound i B))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedB
