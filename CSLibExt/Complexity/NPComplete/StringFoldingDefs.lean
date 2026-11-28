/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRING FOLDING: definitions

Source:
M. Paterson and T. Przytycka, "On the complexity of string folding", Discrete Applied
Mathematics 71 (1996), 217-230, doi:10.1016/S0166-218X(96)00065-0;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM STRING FOLDING (decision version).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import CSLibExt.Complexity.NPComplete.HPFoldingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StringFolding

/-- An instance: the string `s` (symbols as natural numbers) and the bound `K`. -/
abbrev StringFoldingInstance := List ℕ × ℕ

/-- Well-formedness of an instance: `0 < K`. -/
def WellFormed (i : StringFoldingInstance) : Prop :=
  0 < i.2

/-- `f` is a folding of `s` in `ℤ^d`: `HPFolding.IsFolding` (one-to-one, consecutive residues at
adjacent sites), which depends only on the length of the string, applied to `f` along the cast
`Fin |s.map (fun _ => true)| → Fin |s|`. -/
def IsFolding (d : ℕ) (s : List ℕ) (f : Fin s.length → StatMech.Lattice.Site d) : Prop :=
  HPFolding.IsFolding d (s.map fun _ => true) (f ∘ Fin.cast (List.length_map _))

open Classical in
/-- The contacts of `f`: the pairs `(a, b)` of residues with `a + 1 < b` (so not adjacent in
`s`) that carry equal symbols and that `f` maps to adjacent lattice sites. -/
noncomputable def contacts (d : ℕ) (s : List ℕ) (f : Fin s.length → StatMech.Lattice.Site d) :
    Finset (Fin s.length × Fin s.length) :=
  Finset.univ.filter fun ab => ab.1.1 + 1 < ab.2.1 ∧ s.get ab.1 = s.get ab.2 ∧
    (StatMech.Lattice.hypercubicLattice d).Adj (f ab.1) (f ab.2)

/-- Some folding of the string in `ℤ^d` has at least `K` contacts. -/
def StringFoldingFeasible (d : ℕ) (i : StringFoldingInstance) : Prop :=
  ∃ f : Fin i.1.length → StatMech.Lattice.Site d,
    IsFolding d i.1 f ∧ i.2 ≤ (contacts d i.1 f).card

open Classical in
/-- STRING FOLDING on the lattice `ℤ^d`, as a decision problem over bitstrings. -/
noncomputable def stringFoldingDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := StringFoldingInstance) x with
  | some i => decide (WellFormed i ∧ StringFoldingFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StringFolding
