/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3D ISING SPIN GLASS GROUND STATE is NP-complete

Source:
F. Barahona, "On the computational complexity of Ising spin glass models", Journal of
Physics A: Mathematical and General 15 (1982), 3241-3253,
doi:10.1088/0305-4470/15/10/028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlassDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass

/-!
# 3D ISING SPIN GLASS GROUND STATE is NP-complete

INSTANCE: a finite three-dimensional grid graph `G = (V, E)`, couplings `J_{ij} ∈ {-1, 0, 1}`
on its edges, and an integer `E₀`.
QUESTION: is there a spin assignment `s ∈ {-1, +1}^V` whose energy `-∑_{(ij) ∈ E} J_{ij} sᵢ sⱼ`
is at most `E₀`?

Barahona proves that finding a ground state of this model is NP-hard, "even in a two-level grid
and with interactions restricted to be {-1, 0, 1}" (problem P3, the two-level spin glass); the
energy of a given assignment is computable in polynomial time.

The grid is the box `{0, …, a - 1} × {0, …, b - 1} × {0, …, c - 1}` of the cubic lattice,
whose sites `((x, y), z)` are adjacent when they differ by one in exactly one coordinate:
the Mathlib graph `SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ`. The
couplings are a list of entries `(u, v, J)` on distinct lattice edges of the box; an edge that
is not listed has coupling `0`, which contributes nothing to the energy. Integers are encoded
as pairs of naturals `(positive part, negative part)` (`intOf`), as in
`WantedExt.Complexity.NPComplete.ZeroOneILPWanted`. A spin assignment is a map from sites to
`Bool` (`true` is `+1`, `false` is `-1`); only its values on the box enter the energy.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3D ISING SPIN GLASS GROUND STATE is NP-complete.** Source: Barahona (1982). -/
public theorem_wanted threeDimensionalIsingSpinGlass_npComplete :
    threeDimensionalIsingSpinGlassDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalIsingSpinGlassDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass
