/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RAINBOW CONNECTION NUMBER AT MOST 2: definitions

Source:
S. Chakraborty, E. Fischer, A. Matsliah, and R. Yuster, "Hardness and algorithms for rainbow
connection", Journal of Combinatorial Optimization 21(3) (2011), 330-347,
doi:10.1007/s10878-009-9250-9.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RainbowConnectionTwo

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

end MetaMathlibExt.Complexity.NPComplete.RainbowConnectionTwo
