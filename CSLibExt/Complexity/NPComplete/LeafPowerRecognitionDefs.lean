/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LEAF POWER RECOGNITION: definitions

Source:
M. Dupré la Tour, M. Lafond and N. Ndiaye, "Recognizing leaf powers and pairwise compatibility
graphs is NP-complete", Proceedings of the 2026 Annual ACM-SIAM Symposium on Discrete
Algorithms (SODA 2026), 6166-6183, doi:10.1137/1.9781611978971.219 (arXiv:2510.19763;
Section 2: the definition of leaf powers used below; Corollary 1.2: "Recognition of leaf powers"
is NP-complete);
ISGCI (https://www.graphclasses.org/classes/gc_649.html), class leaf power, problem
"Recognition": NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LeafPowerRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev LeafPowerRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LeafPowerRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : LeafPowerRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `T` is a leaf root of `G` with threshold `θ`, the vertices of `G` being the leaves `f v` of
`T`: `T` is acyclic and preconnected (a tree, or empty), `f` is injective, the leaves of `T` (the
vertices with at most one neighbour) are exactly the values of `f`, and two distinct vertices of
`G` are adjacent exactly when their leaves are at distance at most `θ` in `T`. -/
def IsLeafRoot {n m : ℕ} (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin m))
    (f : Fin n → Fin m) (θ : ℕ) : Prop :=
  T.IsAcyclic ∧ T.Preconnected ∧ Function.Injective f ∧
    (∀ x, (T.neighborSet x).Subsingleton ↔ x ∈ Set.range f) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ T.dist (f u) (f v) ≤ θ)

/-- The graph of the instance is a leaf power: it has a leaf root for some threshold. -/
def LeafPowerRecognitionFeasible (i : LeafPowerRecognitionInstance) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (f : Fin i.1 → Fin m) (θ : ℕ), IsLeafRoot (Graph i) T f θ

open Classical in
/-- LEAF POWER RECOGNITION as a decision problem over bitstrings. -/
noncomputable def leafPowerRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LeafPowerRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ LeafPowerRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LeafPowerRecognition
