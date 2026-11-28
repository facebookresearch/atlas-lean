/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC FACILITY LOCATION: definitions

Source:
S. Guha and S. Khuller, "Greedy strikes back: improved facility location algorithms",
J. Algorithms 31 (1999), 228-248, doi:10.1006/jagm.1998.0993 (the metric uncapacitated facility
location problem, proved max SNP-hard);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM FACILITY LOCATION (the same instance; its printed objective differs, see
below).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricFacilityLocation

/-- An instance: location count `n`, cost matrix `c`, candidate locations with building costs
`(v, f(v))`, demands `d` and bound `K`. -/
abbrev MetricFacilityLocationInstance :=
  ℕ × List (List ℕ) × List (ℕ × ℕ) × List ℕ × ℕ

/-- The cost `c(u, v)`. -/
def cost (i : MetricFacilityLocationInstance) (u v : ℕ) : ℕ := (i.2.1.getD u []).getD v 0

/-- Well-formedness of an instance: the cost matrix is `n × n`, zero exactly on the diagonal,
symmetric and satisfies the triangle inequality; the candidate locations are distinct locations;
there is one demand per location; and `0 < K`. -/
def WellFormed (i : MetricFacilityLocationInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ u < i.1, ∀ v < i.1, cost i u v = 0 ↔ u = v) ∧
    (∀ u < i.1, ∀ v < i.1, cost i u v = cost i v u) ∧
    (∀ u < i.1, ∀ v < i.1, ∀ w < i.1, cost i u w ≤ cost i u v + cost i v w) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧ (∀ p ∈ i.2.2.1, p.1 < i.1) ∧ i.2.2.2.1.length = i.1 ∧
    0 < i.2.2.2.2

/-- Facilities built at the locations of a sublist `F'` of the candidates, with location `v`
served by the facility at `a(v)`, cost at most `K` in total. -/
def MetricFacilityLocationFeasible (i : MetricFacilityLocationInstance) : Prop :=
  ∃ F' : List (ℕ × ℕ), F'.Sublist i.2.2.1 ∧
    ∃ a : List ℕ, a.length = i.1 ∧ (∀ v < i.1, a.getD v 0 ∈ F'.map Prod.fst) ∧
      (F'.map Prod.snd).sum +
          ((List.range i.1).map fun v => i.2.2.2.1.getD v 0 * cost i (a.getD v 0) v).sum ≤
        i.2.2.2.2

open Classical in
/-- METRIC FACILITY LOCATION as a decision problem over bitstrings. -/
noncomputable def metricFacilityLocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricFacilityLocationInstance) x with
  | some i => decide (WellFormed i ∧ MetricFacilityLocationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricFacilityLocation
