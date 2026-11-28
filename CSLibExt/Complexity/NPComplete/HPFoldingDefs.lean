/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROTEIN FOLDING IN THE 2D HP MODEL: definitions

Source:
P. Crescenzi, D. Goldman, C. Papadimitriou, A. Piccolboni, and M. Yannakakis, "On the
complexity of protein folding", Journal of Computational Biology 5 (1998), 423-465,
doi:10.1089/cmb.1998.5.423.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HPFolding

/-- An instance: the residue string `s` (`true` for `H`, `false` for `P`) and the bound `K`. -/
abbrev HPFoldingInstance := List Bool × ℕ

/-- `f` is a folding of `s` in `ℤ^d`: a self-avoiding walk, i.e., `f` is one-to-one and maps
consecutive residues to adjacent lattice sites. -/
def IsFolding (d : ℕ) (s : List Bool) (f : Fin s.length → StatMech.Lattice.Site d) : Prop :=
  Function.Injective f ∧
    ∀ a b : Fin s.length, b.1 = a.1 + 1 → (StatMech.Lattice.hypercubicLattice d).Adj (f a) (f b)

open Classical in
/-- The H-H contacts of `f`: the pairs `(a, b)` of `H` residues with `a + 1 < b` (so not
consecutive in `s`) that `f` maps to adjacent lattice sites. -/
noncomputable def contacts (d : ℕ) (s : List Bool) (f : Fin s.length → StatMech.Lattice.Site d) :
    Finset (Fin s.length × Fin s.length) :=
  Finset.univ.filter fun ab => ab.1.1 + 1 < ab.2.1 ∧ s.get ab.1 = true ∧ s.get ab.2 = true ∧
    (StatMech.Lattice.hypercubicLattice d).Adj (f ab.1) (f ab.2)

/-- Some folding of the string in `ℤ^d` has at least `K` H-H contacts. -/
def HPFoldingFeasible (d : ℕ) (i : HPFoldingInstance) : Prop :=
  ∃ f : Fin i.1.length → StatMech.Lattice.Site d, IsFolding d i.1 f ∧ i.2 ≤ (contacts d i.1 f).card

open Classical in
/-- PROTEIN FOLDING IN THE HP MODEL on the lattice `ℤ^d`, as a decision problem over
bitstrings. -/
noncomputable def hpFoldingDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HPFoldingInstance) x with
  | some i => decide (HPFoldingFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HPFolding
