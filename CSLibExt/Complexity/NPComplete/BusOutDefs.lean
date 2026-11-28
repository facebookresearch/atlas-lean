/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUS OUT: definitions

Source:
T. Ishibashi, R. Yoshinaka and A. Shinohara, "BusOut is NP-complete", arXiv:2505.09165 (2025),
Section 2 and Theorem 2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BusOut

/-- An instance: the bus labels `(color, capacity)`, the blocking edges `(u, v)` (bus `v` blocks
bus `u`), the passenger queue (colors, first passenger first), and the number `s` of spots. -/
abbrev BusOutInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × List ℕ × ℕ

/-- Bus `v` blocks bus `u`: the congestion graph has the edge `u → v`. -/
def Blocks (i : BusOutInstance) (u v : Fin i.1.length) : Prop :=
  ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- A state: the buses still in traffic, the remaining passenger queue, and the spots (`none`
for an empty spot, `some (x, k)` for a bus of color `x` with `k` remaining seats). -/
abbrev State (i : BusOutInstance) := Finset (Fin i.1.length) × List ℕ × List (Option (ℕ × ℕ))

/-- A board move is applicable: the first passenger's color matches a bus in a spot. -/
def CanBoard (i : BusOutInstance) (c : State i) : Prop :=
  ∃ (x : ℕ) (q : List ℕ), c.2.1 = x :: q ∧ ∃ (j k : ℕ), c.2.2[j]? = some (some (x, k))

/-- One move: board the first passenger, or, when no boarding is applicable, dispatch a free bus
to an empty spot. -/
def Step (i : BusOutInstance) (c c' : State i) : Prop :=
  (∃ (x : ℕ) (q : List ℕ) (j k : ℕ), c.2.1 = x :: q ∧ c.2.2[j]? = some (some (x, k + 1)) ∧
      c' = (c.1, q, c.2.2.set j (if k = 0 then none else some (x, k)))) ∨
    (¬ CanBoard i c ∧ ∃ u ∈ c.1, (∀ v ∈ c.1, ¬ Blocks i u v) ∧ ∃ j : ℕ, c.2.2[j]? = some none ∧
      c' = (c.1.erase u, c.2.1, c.2.2.set j (some (i.1.get u))))

/-- Well-formedness: the edges join buses, the congestion graph has no cycle, every capacity
and the number of spots are positive, and for every color the capacities of its buses sum to
its number of passengers. -/
def WellFormed (i : BusOutInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length) ∧
    (∀ u, ¬ Relation.TransGen (Blocks i) u u) ∧ (∀ b ∈ i.1, 0 < b.2) ∧ 0 < i.2.2.2 ∧
    ∀ x, ((i.1.filter fun b => b.1 = x).map Prod.snd).sum = i.2.2.1.count x

/-- From `(G, Q, εˢ)` some sequence of moves reaches the empty configuration. -/
def BusOutFeasible (i : BusOutInstance) : Prop :=
  Relation.ReflTransGen (Step i) (Finset.univ, i.2.2.1, List.replicate i.2.2.2 none)
    (∅, [], List.replicate i.2.2.2 none)

open Classical in
/-- BUS OUT as a decision problem over bitstrings. -/
noncomputable def busOutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BusOutInstance) x with
  | some i => decide (WellFormed i ∧ BusOutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BusOut
