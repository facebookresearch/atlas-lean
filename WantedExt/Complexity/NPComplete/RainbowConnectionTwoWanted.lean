/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RAINBOW CONNECTION NUMBER AT MOST 2 is NP-complete

Source:
S. Chakraborty, E. Fischer, A. Matsliah, and R. Yuster, "Hardness and algorithms for rainbow
connection", Journal of Combinatorial Optimization 21(3) (2011), 330-347,
doi:10.1007/s10878-009-9250-9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RainbowConnectionTwo

/-!
# RAINBOW CONNECTION NUMBER AT MOST 2 is NP-complete

INSTANCE: a connected graph `G = (V, E)` (finite, simple, undirected).
QUESTION: can the edges of `G` be colored with `2` colors so that every pair of vertices is
joined by a path whose edges have distinct colors, that is, is the rainbow connection number
`rc(G)` at most `2`?

An edge coloring is a Mathlib `SimpleGraph.EdgeLabeling` of `G` with labels `Fin 2`. A rainbow
path from `u` to `v` is a Mathlib walk `p : G.Walk u v` with `p.IsPath` whose edges, listed
along `p` by its darts, carry pairwise distinct labels (`List.Nodup`). With two colors a rainbow
path has at most two edges. Connectivity is part of the instance class, so it is a conjunct of
`WellFormed` (Mathlib's `SimpleGraph.Connected`, which also requires a vertex).

Chakraborty, Fischer, Matsliah and Yuster prove that deciding `rc(G) = 2` is NP-complete. The
question here is `rc(G) ≤ 2`; the two differ only on complete graphs (`rc(G) ≤ 1` exactly when
any two distinct vertices are adjacent), which are recognized in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev RainbowConnectionTwoInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RainbowConnectionTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and the graph is
connected. -/
def WellFormed (i : RainbowConnectionTwoInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).Connected

/-- The edge coloring `c` makes `G` rainbow connected: every two vertices are joined by a path
whose edges have pairwise distinct colors. -/
def IsRainbowConnected {n : ℕ} {G : SimpleGraph (Fin n)} {K : Type*} (c : G.EdgeLabeling K) :
    Prop :=
  ∀ u v : Fin n, ∃ p : G.Walk u v, p.IsPath ∧ (p.darts.map fun d => c.get d.fst d.snd d.adj).Nodup

/-- Some coloring of the edges with `2` colors makes the graph rainbow connected. -/
def RainbowConnectionTwoFeasible (i : RainbowConnectionTwoInstance) : Prop :=
  ∃ c : (Graph i).EdgeLabeling (Fin 2), IsRainbowConnected c

open Classical in
/-- RAINBOW CONNECTION NUMBER AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def rainbowConnectionTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RainbowConnectionTwoInstance) x with
  | some i => decide (WellFormed i ∧ RainbowConnectionTwoFeasible i)
  | none => false

/-- **RAINBOW CONNECTION NUMBER AT MOST 2 is NP-complete.** Source: Chakraborty, Fischer,
Matsliah, and Yuster (2011). -/
public theorem_wanted rainbowConnectionTwo_npComplete :
    rainbowConnectionTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rainbowConnectionTwoDec

end MetaMathlibExt.Complexity.NPComplete.RainbowConnectionTwo
