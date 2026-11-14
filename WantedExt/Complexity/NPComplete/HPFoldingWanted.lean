/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROTEIN FOLDING IN THE 2D HP MODEL is NP-complete

Source:
P. Crescenzi, D. Goldman, C. Papadimitriou, A. Piccolboni, and M. Yannakakis, "On the
complexity of protein folding", Journal of Computational Biology 5 (1998), 423-465,
doi:10.1089/cmb.1998.5.423.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HPFolding

/-!
# PROTEIN FOLDING IN THE 2D HP MODEL is NP-complete

INSTANCE: a string `s` over `{H, P}` (hydrophobic and polar residues) and an integer `K`.
QUESTION: is there a folding of `s` in the square lattice `ℤ²`, i.e., a self-avoiding walk: a
one-to-one map of the residues to lattice points sending consecutive residues to adjacent
points, with at least `K` H-H contacts, i.e., pairs of `H` residues that are not consecutive in
`s` and are mapped to adjacent lattice points? (The energy of a folding is minus its number of
contacts; the question asks for a folding of energy at most `-K`.)

The lattice is MathlibExt's `StatMech.Lattice.hypercubicLattice d` on `ℤ^d` (sites
`Fin d → ℤ`, adjacent at `ℓ¹` distance one); the square lattice is `d = 2`. Foldings and
contacts are defined for every `d`, so that the cubic-lattice version (`d = 3`) can reuse
them. The string is a `List Bool` with `true` for `H`, residues are `Fin |s|`, and a contact
is a pair `(a, b)` of residues with `a + 1 < b`. Every decoded instance is well formed (`K` is
any natural number; `K = 0` is trivially a yes-instance).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PROTEIN FOLDING IN THE 2D HP MODEL is NP-complete.** Source: Crescenzi, Goldman,
Papadimitriou, Piccolboni, and Yannakakis (1998). -/
public theorem_wanted hpFolding2D_npComplete :
    hpFoldingDec 2 ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hpFoldingDec 2)

end MetaMathlibExt.Complexity.NPComplete.HPFolding
