/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROTEIN FOLDING IN THE 3D HP MODEL is NP-complete

Source:
B. Berger and T. Leighton, "Protein folding in the hydrophobic-hydrophilic (HP) model is
NP-complete", Journal of Computational Biology 5 (1998), 27-40, doi:10.1089/cmb.1998.5.27.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HPFoldingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HPFolding3D

/-!
# PROTEIN FOLDING IN THE 3D HP MODEL is NP-complete

INSTANCE: a string `s` over `{H, P}` and an integer `K`. QUESTION: is there a folding of `s` in
the cubic lattice `ℤ³` (a self-avoiding walk: a one-to-one map of the residues to lattice points
sending consecutive residues to adjacent points) with at least `K` H-H contacts (pairs of `H`
residues not consecutive in `s` that are mapped to adjacent lattice points)?

This is PROTEIN FOLDING IN THE HP MODEL (`HPFoldingWanted`, which states the square-lattice
case) on the cubic lattice: the instance type `HPFolding.HPFoldingInstance`, the foldings
`HPFolding.IsFolding`, the contacts `HPFolding.contacts` and the decision problem
`HPFolding.hpFoldingDec` are reused with dimension `3`, i.e., on MathlibExt's
`StatMech.Lattice.hypercubicLattice 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PROTEIN FOLDING IN THE 3D HP MODEL is NP-complete.** Source: Berger and Leighton
(1998). -/
public theorem_wanted hpFolding3D_npComplete :
    HPFolding.hpFoldingDec 3 ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (HPFolding.hpFoldingDec 3)

end MetaMathlibExt.Complexity.NPComplete.HPFolding3D
