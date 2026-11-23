/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOCHROMATIC K_k is NP-complete for every fixed k ≥ 4

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT6] MONOCHROMATIC
TRIANGLE (p. 191), comment "Variants in which 'triangle' is replaced by any larger fixed complete
graph are also NP-complete [Burr, 1976]";
S. A. Burr, "On the computational complexity of Ramsey-type problems", in *Mathematics of Ramsey
Theory* (J. Nešetřil and V. Rödl, eds.), Algorithms and Combinatorics 5, Springer (1990), 46-52,
doi:10.1007/978-3-642-72905-8_5 (as recorded by M. Schaefer, "Graph Ramsey theory and the
polynomial hierarchy", Journal of Computer and System Sciences 62 (2001), 290-322,
doi:10.1006/jcss.2000.1729, p. 292: deciding `F → (G, H)` is coNP-complete for any fixed
3-connected graphs `G` and `H`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MonochromaticTriangleWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonochromaticCliqueFixedK

open MetaMathlibExt.Complexity.NPComplete.MonochromaticTriangle
  (MonochromaticTriangleInstance Graph)

/-!
# MONOCHROMATIC K_k is NP-complete for every fixed k ≥ 4

Fix an integer `k ≥ 4`.
INSTANCE: a graph `G = (V, E)`.
QUESTION: is there a partition of `E` into two disjoint sets `E₁, E₂` such that neither
`G₁ = (V, E₁)` nor `G₂ = (V, E₂)` contains a complete graph `K_k`?

This is MONOCHROMATIC TRIANGLE ([GT6], `MonochromaticTriangleWanted`) with "triangle" replaced
by the fixed complete graph `K_k`. The instance type, `MonochromaticTriangle.Graph` and
`MonochromaticTriangle.WellFormed` (a simple edge list on `Fin n`) are reused unchanged. As
there, the partition is given by the subgraph `G₁ ≤ G` with edge set `E₁`, so that `G \ G₁` has
edge set `E₂ = E \ E₁`; "contains no `K_k`" is Mathlib's `CliqueFree k`.

`k` is fixed, not part of the input: the decision problem is `monochromaticCliqueFixedKDec k`, and
the theorem holds for every `k ≥ 4` (the case `k = 3` is [GT6] itself). For fixed `k`, checking
that a 2-coloring of the edges has no monochromatic `K_k` takes polynomial time, so the problem
is in NP. Hardness is Burr's: deciding `F → (G, H)` (every red-blue coloring of the edges of `F`
has a red `G` or a blue `H`) is coNP-complete for fixed 3-connected `G` and `H`, and `K_k` is
3-connected for `k ≥ 4`; this problem is the complement of `F → (K_k, K_k)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The edges split into two parts neither of which contains `K_k`: a subgraph `G₁ ≤ G` such that
neither `G₁` nor its complement `G \ G₁` in `G` contains a `k`-clique. -/
def MonochromaticCliqueFeasible (k : ℕ) (i : MonochromaticTriangleInstance) : Prop :=
  ∃ G₁ : SimpleGraph (Fin i.1), G₁ ≤ Graph i ∧ G₁.CliqueFree k ∧ (Graph i \ G₁).CliqueFree k

open Classical in
/-- MONOCHROMATIC K_k, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def monochromaticCliqueFixedKDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonochromaticTriangleInstance) x with
  | some i => decide (MonochromaticTriangle.WellFormed i ∧ MonochromaticCliqueFeasible k i)
  | none => false

/-- **MONOCHROMATIC K_k is NP-complete for every fixed `k ≥ 4`.** Source: Garey and Johnson
(1979), [GT6], comment (Burr, 1976); Burr (1990). -/
public theorem_wanted monochromaticCliqueFixedK_npComplete (k : ℕ) (_hk : 4 ≤ k) :
    monochromaticCliqueFixedKDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (monochromaticCliqueFixedKDec k)

end MetaMathlibExt.Complexity.NPComplete.MonochromaticCliqueFixedK
