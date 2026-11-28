/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# L(2,1)-LABELING WITH FIXED SPAN: definitions

Source:
J. Fiala, T. Kloks and J. Kratochvíl, "Fixed-parameter complexity of λ-labelings", Discrete
Applied Mathematics 113 (2001), 59-72, doi:10.1016/S0166-218X(00)00387-5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.L21LabelingFixedSpan

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev L21LabelingFixedSpanInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : L21LabelingFixedSpanInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : L21LabelingFixedSpanInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `f` is an `L(2,1)`-labeling of `G`: labels of adjacent vertices differ by at least two, and
distinct vertices at distance two get different labels. -/
def IsL21Labeling {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin n → Fin m) : Prop :=
  (∀ u v, G.Adj u v → (f u : ℕ) + 2 ≤ f v ∨ (f v : ℕ) + 2 ≤ f u) ∧
    ∀ u v w, u ≠ v → G.Adj u w → G.Adj w v → f u ≠ f v

/-- `G` has an `L(2,1)`-labeling with labels in `{0, …, K}`. -/
def L21LabelingFixedSpanFeasible (K : ℕ) (i : L21LabelingFixedSpanInstance) : Prop :=
  ∃ f : Fin i.1 → Fin (K + 1), IsL21Labeling (Graph i) f

open Classical in
/-- L(2,1)-LABELING WITH SPAN `K` for the fixed `K` as a decision problem over bitstrings. -/
noncomputable def l21LabelingFixedSpanDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := L21LabelingFixedSpanInstance) x with
  | some i => decide (WellFormed i ∧ L21LabelingFixedSpanFeasible K i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.L21LabelingFixedSpan
