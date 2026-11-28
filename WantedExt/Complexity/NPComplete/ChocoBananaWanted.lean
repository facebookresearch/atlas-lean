/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHOCO BANANA is NP-complete

Source:
C. Iwamoto and T. Tokunaga, "Choco Banana is NP-complete", IEICE Transactions on Fundamentals
of Electronics, Communications and Computer Sciences E107-A(9) (2024), 1488-1491,
doi:10.1587/transfun.2023DML0001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChocoBananaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChocoBanana

/-!
# CHOCO BANANA is NP-complete

INSTANCE: a rectangular grid of cells, where some of the cells contain a positive number.
QUESTION: can some of the cells be painted black, the others white, so that
(1) each set of connected black cells forms a rectangle area,
(2) each set of connected white cells does not form a rectangle area (squares included), and
(3) each number equals the number of cells of the connected area containing it?

A connected area is a maximal set of same-colored cells connected through orthogonally
adjacent same-colored cells. The grid with `h` rows and `w` columns is Mathlib's grid graph
`pathGraph h □ pathGraph w` on `Fin h × Fin w`; keeping only its edges between cells of the same
color gives `areaGraph`, whose connected components are the connected areas.

The instance lists the rows of the grid, top to bottom; entry `0` is a cell without a number
and an entry `n ≥ 1` is a cell containing the number `n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHOCO BANANA is NP-complete.** Source: Iwamoto and Tokunaga (2024), Theorem 1. -/
public theorem_wanted chocoBanana_npComplete :
    chocoBananaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chocoBananaDec

end MetaMathlibExt.Complexity.NPComplete.ChocoBanana
