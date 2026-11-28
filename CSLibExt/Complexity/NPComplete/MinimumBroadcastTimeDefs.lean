/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BROADCAST TIME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME
(credited there to Garey and Johnson, unpublished: transformation from 3DM);
P. J. Slater, E. J. Cockayne and S. T. Hedetniemi, "Information dissemination in trees", SIAM
Journal on Computing 10 (1981), 692-701, doi:10.1137/0210052.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTime

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the base set `V₀` as a
list of vertices, and the time bound `K`. -/
abbrev MinimumBroadcastTimeInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumBroadcastTimeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The base set `V₀`: the vertices listed in the instance. -/
def baseSet (i : MinimumBroadcastTimeInstance) : Set (Fin i.1) :=
  {v | (v : ℕ) ∈ i.2.2.1}

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `V₀` is a list of
distinct vertices, and `K` is positive. -/
def WellFormed (i : MinimumBroadcastTimeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.Nodup ∧ (∀ v ∈ i.2.2.1, v < i.1) ∧ 0 < i.2.2.2

/-- One broadcast step from `V'` to `V''` along the edge set `F`: `F ⊆ E`, (1) each edge of `F`
has exactly one endpoint in `V'`, (2) no two edges of `F` share an endpoint, and (3)
`V'' = V' ∪ {v : {u, v} ∈ F}`. -/
def BroadcastStep (i : MinimumBroadcastTimeInstance) (V' : Set (Fin i.1))
    (F : Set (Sym2 (Fin i.1))) (V'' : Set (Fin i.1)) : Prop :=
  F ⊆ (Graph i).edgeSet ∧
    (∀ e ∈ F, ∃ u v, e = s(u, v) ∧ u ∈ V' ∧ v ∉ V') ∧
    (∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → ∀ x ∈ e, x ∉ e') ∧
    V'' = V' ∪ {v | ∃ u, s(u, v) ∈ F}

/-- Some sequence `V₀, E₁, V₁, …, E_K, V_K` starts at the base set, ends at `V_K = V`, and
consists of broadcast steps. -/
def MinimumBroadcastTimeFeasible (i : MinimumBroadcastTimeInstance) : Prop :=
  ∃ (V : ℕ → Set (Fin i.1)) (E : ℕ → Set (Sym2 (Fin i.1))),
    V 0 = baseSet i ∧ V i.2.2.2 = Set.univ ∧
      ∀ j, 1 ≤ j → j ≤ i.2.2.2 → BroadcastStep i (V (j - 1)) (E j) (V j)

open Classical in
/-- MINIMUM BROADCAST TIME as a decision problem over bitstrings. -/
noncomputable def minimumBroadcastTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumBroadcastTimeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumBroadcastTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTime
