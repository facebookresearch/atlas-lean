/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EMBEDDING DIMENSION: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
89-99, doi:10.1016/0196-6774(82)90011-6, problem [4] EMBEDDING DIMENSION (reference: Dewdney;
transformation from VERTEX COVER);
A. K. Dewdney, "The embedding dimension of a graph", Report No. 52, Department of Computer
Science, University of Western Ontario, London, Ontario (1979), as cited by the column
(Dewdney's report was not available; the column records the result and its attribution).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.NesetrilRodlDimensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EmbeddingDimension

open NesetrilRodlDimension (NesetrilRodlDimensionInstance Graph)

/-- Well-formedness of an instance: `n` is written in unary as `[true, ..., true]`, the edge
list describes a simple graph on `0, ..., n - 1`, and `K` is positive. -/
def WellFormed (i : NesetrilRodlDimensionInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The graph on `{0, 1, 2}^K` (functions `Fin K → Fin 3`) joining two distinct tuples whose
components differ by at most `1` everywhere. -/
def Host (K : ℕ) : SimpleGraph (Fin K → Fin 3) :=
  SimpleGraph.fromRel fun f g => ∀ k, (f k : ℕ) ≤ g k + 1 ∧ (g k : ℕ) ≤ f k + 1

/-- `G` embeds into `Host K` as an induced subgraph: some one-to-one `f : V → {0, 1, 2}^K` has
`{u, v} ∈ E` iff `f(u)` and `f(v)` are adjacent in `Host K`. -/
def EmbeddingDimensionFeasible (i : NesetrilRodlDimensionInstance) : Prop :=
  Nonempty (Graph i ↪g Host i.2.2)

open Classical in
/-- EMBEDDING DIMENSION as a decision problem over bitstrings. -/
noncomputable def embeddingDimensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NesetrilRodlDimensionInstance) x with
  | some i => decide (WellFormed i ∧ EmbeddingDimensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EmbeddingDimension
