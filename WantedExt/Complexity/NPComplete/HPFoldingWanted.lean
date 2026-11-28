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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HPFoldingDefs

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

/-- **PROTEIN FOLDING IN THE 2D HP MODEL is NP-complete.** Source: Crescenzi, Goldman,
Papadimitriou, Piccolboni, and Yannakakis (1998). -/
public theorem_wanted hpFolding2D_npComplete :
    hpFoldingDec 2 ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hpFoldingDec 2)

end MetaMathlibExt.Complexity.NPComplete.HPFolding
