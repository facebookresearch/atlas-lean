/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERFECT PHYLOGENY: definitions

Source:
H. L. Bodlaender, M. R. Fellows, and T. J. Warnow, "Two strikes against perfect phylogeny",
Automata, Languages and Programming (ICALP 1992), Lecture Notes in Computer Science 623, 273-283,
doi:10.1007/3-540-55719-9_80, Section 1 (the problem) and Section 3 (Theorem 1 and its
consequence that Perfect Phylogeny is NP-complete);
M. A. Steel, "The complexity of reconstructing trees from qualitative characters and subtrees",
Journal of Classification 9 (1992), 91-116, doi:10.1007/BF02618470.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PerfectPhylogeny

/-- An instance: the number `m` of characters and, for each species, its list of `m` states. -/
abbrev PerfectPhylogenyInstance := ℕ × List (List ℕ)

/-- Well-formedness: there is at least one species, and every species has a state for each of
the `m` characters. -/
def WellFormed (i : PerfectPhylogenyInstance) : Prop :=
  i.2 ≠ [] ∧ ∀ s ∈ i.2, s.length = i.1

/-- The state of species `s` for character `c`. -/
def state (i : PerfectPhylogenyInstance) (s c : ℕ) : ℕ :=
  (i.2.getD s []).getD c 0

/-- `(T, f, lab)` is a perfect phylogeny for the instance: `T` is a tree, species `s` sits at node
`f s` and keeps its states there, every node carries for each character a state that some species
has, and for each character `c` and state `x` the nodes with state `x` induce a connected
subgraph. -/
def IsPerfectPhylogeny (i : PerfectPhylogenyInstance) {N : ℕ} (T : SimpleGraph (Fin N))
    (f : Fin i.2.length → Fin N) (lab : Fin N → Fin i.1 → ℕ) : Prop :=
  T.IsTree ∧ (∀ s c, lab (f s) c = state i s c) ∧
    (∀ v c, ∃ s : Fin i.2.length, lab v c = state i s c) ∧
    ∀ c x, (T.induce {v | lab v c = x}).Preconnected

/-- A perfect phylogeny exists. -/
def PerfectPhylogenyFeasible (i : PerfectPhylogenyInstance) : Prop :=
  ∃ N, ∃ T : SimpleGraph (Fin N), ∃ f lab, IsPerfectPhylogeny i T f lab

open Classical in
/-- PERFECT PHYLOGENY as a decision problem over bitstrings. -/
noncomputable def perfectPhylogenyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PerfectPhylogenyInstance) x with
  | some i => decide (WellFormed i ∧ PerfectPhylogenyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PerfectPhylogeny
