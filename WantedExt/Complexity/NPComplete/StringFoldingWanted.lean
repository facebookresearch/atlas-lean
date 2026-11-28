/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRING FOLDING is NP-complete

Source:
M. Paterson and T. Przytycka, "On the complexity of string folding", Discrete Applied
Mathematics 71 (1996), 217-230, doi:10.1016/S0166-218X(96)00065-0;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM STRING FOLDING (decision version).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StringFoldingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StringFolding

/-!
# STRING FOLDING is NP-complete

INSTANCE: a finite alphabet `Σ`, a finite string `s` over `Σ`, and a positive integer `K`.
QUESTION: is there a folding of `s` in the cubic lattice `ℤ³`, i.e., a mapping of the symbols of
`s` into `ℤ³` such that adjacent symbols of `s` are adjacent in the lattice and no site is
occupied by more than one symbol, with at least `K` pairs of equal symbols that lie at adjacent
lattice sites, excluding pairs that are adjacent in `s`?

This is the decision version of the compendium's MAXIMUM STRING FOLDING. Paterson and Przytycka
(1996) define the recognition problem STRING-FOLD (a string `S`, an integer `k` and a grid; is
there a fold of `S` with score at least `k`?), where the score counts the pairs of identical
symbols mapped to adjacent grid nodes, not counting successive identical symbols of `S`, and
prove it NP-complete for the square grid `ℤ²` and the cubic grid `ℤ³`; their alphabet is not
fixed but implicitly part of the instance. This module states the cubic case. It generalizes
PROTEIN FOLDING IN THE 3D HP MODEL (`HPFolding3DWanted`), where only `H`-`H` pairs count.

The string is a `List ℕ` (symbols are natural numbers; the alphabet is the finite set of symbols
occurring in `s`), residues are `Fin |s|`, and the lattice is MathlibExt's
`StatMech.Lattice.hypercubicLattice d` on `ℤ^d` (sites `Fin d → ℤ`, adjacent at `ℓ¹` distance
one), with `d = 3` in the theorem. A folding is `HPFolding.IsFolding` (one-to-one, consecutive
residues at adjacent sites), which is stated for strings typed `List Bool` and depends only on
the length; it is applied to `s.map (fun _ => true)` along the cast of `Fin |s|`. A contact is a
pair `(a, b)` of residues with `a + 1 < b` (so not adjacent in `s`), equal symbols, and adjacent
sites. `WellFormed` requires `0 < K` (the compendium's decision versions take a positive
integer `K`; for `K = 0` the question is trivially yes).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRING FOLDING (cubic lattice) is NP-complete.** Source: Paterson and Przytycka (1996);
Crescenzi and Kann, MAXIMUM STRING FOLDING. -/
public theorem_wanted stringFolding_npComplete :
    stringFoldingDec 3 ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (stringFoldingDec 3)

end MetaMathlibExt.Complexity.NPComplete.StringFolding
