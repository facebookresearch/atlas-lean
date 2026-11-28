/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [6] CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE
(reference: A. M. Frieze, "On equitably partitioning a connected graph into connected
subgraphs", technical report; transformation from 3DM);
M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected
subgraphs", Discrete Applied Mathematics 10 (1985), 139-153,
doi:10.1016/0166-218X(85)90008-3, Theorem 2.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CutIntoConnectedComponentsBoundedSize

/-- Well-formedness of an instance `(n, E, K)`: a simple edge list on the vertices
`0, …, n - 1` (`GraphColoring.WellFormed`), and the bound `K ≥ |V| / 2`, that is
`n ≤ 2 K`. -/
def WellFormed (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.1 ≤ 2 * i.2.2

/-- Some set `V₁` with complement `V₂` has `|V₁| ≤ K`, `|V₂| ≤ K`, and both induced subgraphs
connected. -/
def CutIntoConnectedComponentsBoundedSizeFeasible (i : GraphColoring.GraphColoringInstance) :
    Prop :=
  ∃ V₁ : Finset (Fin i.1), V₁.card ≤ i.2.2 ∧ V₁ᶜ.card ≤ i.2.2 ∧
    ((GraphColoring.Graph i).induce (V₁ : Set (Fin i.1))).Connected ∧
    ((GraphColoring.Graph i).induce ((V₁ᶜ : Finset (Fin i.1)) : Set (Fin i.1))).Connected

open Classical in
/-- CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE as a decision problem over bitstrings. -/
noncomputable def cutIntoConnectedComponentsBoundedSizeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ CutIntoConnectedComponentsBoundedSizeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CutIntoConnectedComponentsBoundedSize
