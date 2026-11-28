/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CATERPILLAR ARBORICITY AT MOST 2: definitions

Source:
T. C. Shermer, "On rectangle visibility graphs III. External visibility and complexity",
Proceedings of the 8th Canadian Conference on Computational Geometry (CCCG '96), Ottawa (1996),
234-239 (Section 1: definitions of caterpillars, caterpillar forests and caterpillar arboricity;
Theorem 3.2: "Caterpillar Arboricity 2 is NP-complete");
ISGCI (Information System on Graph Classes and their Inclusions), class "caterpillar
arboricity <= 2" (gc_732), problem Recognition, NP-complete, citing Shermer.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CaterpillarArboricityTwo

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev CaterpillarArboricityTwoInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CaterpillarArboricityTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CaterpillarArboricityTwoInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a caterpillar forest: a forest in which every connected component has a path such
that every vertex of the component is on the path or adjacent to a vertex of the path. -/
def IsCaterpillarForest {V : Type*} (H : SimpleGraph V) : Prop :=
  H.IsAcyclic ∧ ∀ c : H.ConnectedComponent, ∃ (a b : V) (p : H.Walk a b), p.IsPath ∧
    ∀ v ∈ c.supp, v ∈ p.support ∨ ∃ w ∈ p.support, H.Adj v w

/-- The graph decomposes into two edge-disjoint caterpillar forests. -/
def CaterpillarArboricityTwoFeasible (i : CaterpillarArboricityTwoInstance) : Prop :=
  ∃ H₁ H₂ : SimpleGraph (Fin i.1), H₁ ⊔ H₂ = Graph i ∧ Disjoint H₁ H₂ ∧
    IsCaterpillarForest H₁ ∧ IsCaterpillarForest H₂

open Classical in
/-- CATERPILLAR ARBORICITY AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def caterpillarArboricityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CaterpillarArboricityTwoInstance) x with
  | some i => decide (WellFormed i ∧ CaterpillarArboricityTwoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CaterpillarArboricityTwo
