/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-DIMENSIONAL BANDWIDTH is NP-complete

Source:
Z. Miller and J. B. Orlin, "NP-completeness for minimizing maximum edge length in grid
embeddings", Journal of Algorithms 6(1) (1985), 10-16, doi:10.1016/0196-6774(85)90016-1
(problem EDGE LENGTH);
S. N. Bhatt and S. S. Cosmadakis, "The complexity of minimizing wire lengths in VLSI
layouts", Information Processing Letters 25 (1987), 263-267,
doi:10.1016/0020-0190(87)90173-6 (the case `K = 1`, `G` a tree);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the one-dimensional
problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BandwidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalBandwidth

open Bandwidth (BandwidthInstance)

/-!
# 2-DIMENSIONAL BANDWIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` and a nonnegative integer `K`.
QUESTION: is there a one-to-one map `f` of `V` into the points of the integer lattice `ℤ²` such
that `|x(f(u)) - x(f(v))| + |y(f(u)) - y(f(v))| ≤ K` for every edge `uv`, that is, adjacent
vertices are at `ℓ¹` (grid) distance at most `K`?

This is Miller and Orlin's EDGE LENGTH problem ("Input: Graph G, integer k. Question: Is
B₂(G) ≤ k?", where `B₂(G)` is the minimum, over one-to-one maps `f : V(G) → ℤ²`, of the maximum
`L₁` distance between `f(x)` and `f(y)` over the edges `xy`), the two-dimensional analogue of
BANDWIDTH ([GT40], `BandwidthWanted`). It stays NP-complete for `K = 1` and `G` a tree (Bhatt and
Cosmadakis; `UnitLengthTreeGridEmbeddingWanted`, since an injective map with all edges at `ℓ¹`
distance at most `1` sends every edge to a grid edge), so it is NP-complete in the strong sense.

The instance and the well-formedness condition are those of BANDWIDTH (`BandwidthWanted`):
vertex count `n` (vertices `Fin n`), simple edge list, bound, checked by `Bandwidth.WellFormed`.
Miller and Orlin's `k` is any integer; `K : ℕ` covers every nonnegative bound (a negative bound is
a trivial no-instance), and for `K = 0` the answer is yes exactly for edgeless graphs. No upper
bound on `K` is imposed, as in `BandwidthWanted`; for `K ≥ n - 1` the answer is always yes (place
the vertices on one row). The lattice points are MathlibExt's `StatMech.Lattice.Site 2 =
Fin 2 → ℤ`, the sites of `hypercubicLattice 2`, and the distance is the `ℓ¹` distance
`∑ j, |p j - q j|` that defines adjacency there.

Membership in NP: a certificate gives the points of the vertices that lie on edges. A connected
component spans at most `(n - 1) K` in each coordinate, so translating the components into
disjoint boxes along one row keeps every coordinate below `n (2 (n - 1) K + 1)` in absolute value,
which has polynomially many bits. Vertices outside the edge list are isolated and can be placed
on any unused points, so they need no certificate and the binary vertex count does not make the
problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some one-to-one map of the vertices into `ℤ²` puts the endpoints of every edge at `ℓ¹`
distance at most `K`. -/
def TwoDimensionalBandwidthFeasible (i : BandwidthInstance) : Prop :=
  ∃ f : Fin i.1 → StatMech.Lattice.Site 2, Function.Injective f ∧
    ∀ u v, (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).Adj u v →
      ∑ j, (f u j - f v j).natAbs ≤ i.2.2

open Classical in
/-- 2-DIMENSIONAL BANDWIDTH as a decision problem over bitstrings. -/
noncomputable def twoDimensionalBandwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BandwidthInstance) x with
  | some i => decide (Bandwidth.WellFormed i ∧ TwoDimensionalBandwidthFeasible i)
  | none => false

/-- **2-DIMENSIONAL BANDWIDTH is NP-complete.** Source: Miller and Orlin (1985); Bhatt and
Cosmadakis (1987). -/
public theorem_wanted twoDimensionalBandwidth_npComplete :
    twoDimensionalBandwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDimensionalBandwidthDec

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalBandwidth
