/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BANDWIDTH for caterpillars with hairs of length at most 3: definitions

Source:
B. Monien, "The bandwidth minimization problem for caterpillars with hair length 3 is
NP-complete", SIAM Journal on Algebraic and Discrete Methods 7 (1986), 505-512,
doi:10.1137/0607057;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the parent
problem).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.BandwidthDefs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BandwidthCaterpillarsHairLengthThree

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : Bandwidth.BandwidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- `G` is a caterpillar with hairs of length at most `h`: a tree with a path `body` (a list of
distinct vertices, consecutive ones adjacent) such that every vertex off the body has degree at
most `2` and is within distance `h` of some body vertex. -/
def IsCaterpillarWithHairLength (h : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.IsTree ∧ ∃ body : List (Fin n), body.Nodup ∧ body.IsChain G.Adj ∧
    ∀ v, v ∉ body → G.degree v ≤ 2 ∧ ∃ b ∈ body, G.dist v b ≤ h

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is a
caterpillar with hairs of length at most `3`, and `0 < K ≤ n`. -/
def WellFormed (i : Bandwidth.BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ IsCaterpillarWithHairLength 3 (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- BANDWIDTH for caterpillars with hairs of length at most 3 as a decision problem over
bitstrings. -/
noncomputable def bandwidthCaterpillarsHairLengthThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Bandwidth.BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ Bandwidth.BandwidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BandwidthCaterpillarsHairLengthThree
