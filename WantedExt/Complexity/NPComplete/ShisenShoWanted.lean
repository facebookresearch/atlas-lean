/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SHISEN-SHO is NP-complete

Source:
C. Iwamoto, Y. Wada and K. Morita, "Generalized Shisen-Sho is NP-Complete", IEICE Transactions
on Information and Systems E95-D(11) (2012), 2712-2715, doi:10.1587/transinf.E95.D.2712.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShisenShoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShisenSho

/-!
# GENERALIZED SHISEN-SHO is NP-complete

Generalized Shisen-Sho (Iwamoto, Wada and Morita) is played with `4p` tiles that fill a
rectangular grid; for each label there are exactly four tiles carrying it. Two tiles can be
removed if they are labeled by the same number and if they are adjacent or can be connected
with at most three orthogonal line segments, which must not cross tiles. The question is whether
the player can remove all of the tiles.

The line segments run along rows and columns of cell centres and may leave the board, as in
the paper's Fig. 1, where two tiles of a completely filled board are connected by three
segments. Positions are integer points `(row, column)`; the board occupies rows `0, …, R - 1` and
columns `0, …, C - 1`, and every point outside it is free.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED SHISEN-SHO is NP-complete.** Source: Iwamoto, Wada and Morita (2012). -/
public theorem_wanted shisenSho_npComplete :
    shisenShoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shisenShoDec

end MetaMathlibExt.Complexity.NPComplete.ShisenSho
