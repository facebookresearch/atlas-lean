/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# HOTARU BEAM: definitions

Otsuji, Fulla and Fukunaga, Section 2: "Hotaru Beam is played on a rectangular grid. Several
circles, called fireflies, are placed on the intersections of the grid. For each firefly, there is
a dot placed on one of the intersections of its boundary and grid lines, and there also may be a
number inside the circle." "The task is to draw a beam from each firefly. The beam starts from the
dot, follows the grid lines, and stops when it reaches a firefly's boundary (possibly the same one
as it started from)." The beams must satisfy:
- "Beams do not intersect nor do they branch; therefore a beam cannot end at a firefly's dot
  since another beam (or the same beam) starts at that point."
- "The number inside a firefly prescribes the number of bends of its beam." Without a number,
  the number of bends is not restricted.
- "All fireflies must end up connected into a single component by the beams."

INSTANCE: a rectangular grid with fireflies, their dots, and their optional numbers.
QUESTION: does the instance admit a solution? (Theorem 1: NP-complete.)

The grid has the intersections `(x, y)` with `x < W` and `y < H`. A firefly is given by its
intersection, the direction `d < 4` of its dot (`0`: `+x`, `1`: `+y`, `2`: `-x`, `3`: `-y`),
and `(numbered, number)`. A beam of firefly `f` is the list `B` of intersections it visits after
leaving `f`; `f :: B` is a lattice path of unit grid segments, its first step goes in the
direction of `f`'s dot, every intersection of `B` is in the grid, the intersections before the
last are not fireflies (a beam stops at the first firefly it reaches), and the last is the
firefly `g = tgt f` where the beam ends (possibly `f` itself). The beam enters `g` from the
intersection before the last one, which must not be the neighbor of `g` in the direction of
`g`'s dot (a beam cannot end at a dot). The bends of a beam are the interior points of the path
`f :: B` where it turns, i.e. where the two neighboring points are not symmetric about it. The
beams do not intersect: the intersections that beams pass through (all but the last point of
each beam) are pairwise distinct, within one beam and across beams; together with the dot rule
this also keeps the segments of different beams apart. Connectivity is
`SimpleGraph.Connected` of the graph on the fireflies joining `f` and `tgt f`, so an instance
has at least one firefly. An unnumbered firefly carries `(false, 0)`, so every instance has one
encoding.

Grid dimensions are given in unary (`W` and `H` are the lengths of lists of `true`s): a beam
can follow the grid lines through every intersection, so a solution has size proportional to
`W · H`, which a binary encoding would make exponential in the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
T. Otsuji, P. Fulla and T. Fukunaga, "NP-completeness and physical zero-knowledge proof of
Hotaru Beam", arXiv:2603.01393 (2026) (Section 2: the rules; Theorem 1).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HotaruBeam

/-- A firefly: its intersection `(x, y)`, the direction of its dot, and `(numbered, number)`. -/
abbrev Firefly := (ℕ × ℕ) × ℕ × Bool × ℕ

/-- An instance: the grid width `W` and height `H` in unary, and the fireflies. -/
abbrev HotaruBeamInstance := List Bool × List Bool × List Firefly

/-- `q` is the intersection one unit from `p` in direction `d` (`0`: `+x`, `1`: `+y`, `2`: `-x`,
`3`: `-y`). -/
def IsStep (p q : ℕ × ℕ) (d : ℕ) : Prop :=
  (d = 0 ∧ q = (p.1 + 1, p.2)) ∨ (d = 1 ∧ q = (p.1, p.2 + 1)) ∨
    (d = 2 ∧ q.1 + 1 = p.1 ∧ q.2 = p.2) ∨ (d = 3 ∧ q.1 = p.1 ∧ q.2 + 1 = p.2)

/-- `p` and `q` are joined by a unit grid segment. -/
def Adjacent (p q : ℕ × ℕ) : Prop :=
  ∃ d < 4, IsStep p q d

/-- The number of bends of the lattice path `P`: interior points `P[j + 1]` with
`P[j] + P[j + 2] ≠ 2 · P[j + 1]`. -/
def bends (P : List (ℕ × ℕ)) : ℕ :=
  ((List.range (P.length - 2)).filter fun j =>
    (P.getD j (0, 0)).1 + (P.getD (j + 2) (0, 0)).1 ≠ 2 * (P.getD (j + 1) (0, 0)).1 ∨
      (P.getD j (0, 0)).2 + (P.getD (j + 2) (0, 0)).2 ≠ 2 * (P.getD (j + 1) (0, 0)).2).length

/-- Well-formedness: the unary dimensions are lists of `true`s, every firefly lies on the grid
with a dot direction below `4` and, if unnumbered, the number `0`, and no two fireflies share an
intersection. -/
def WellFormed (i : HotaruBeamInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧ (∀ b ∈ i.2.1, b = true) ∧
    (∀ F ∈ i.2.2, F.1.1 < i.1.length ∧ F.1.2 < i.2.1.length ∧ F.2.1 < 4 ∧
      (F.2.2.1 = false → F.2.2.2 = 0)) ∧
    (i.2.2.map fun F => F.1).Nodup

/-- `B` is a legal beam for the firefly `F` that ends at the firefly `G`. -/
def BeamOK (i : HotaruBeamInstance) (F G : Firefly) (B : List (ℕ × ℕ)) : Prop :=
  B ≠ [] ∧
    -- it leaves `F` through the dot and follows unit grid segments
    IsStep F.1 (B.getD 0 (0, 0)) F.2.1 ∧ List.IsChain Adjacent (F.1 :: B) ∧
    -- it stays on the grid
    (∀ q ∈ B, q.1 < i.1.length ∧ q.2 < i.2.1.length) ∧
    -- it passes through no firefly before its last point, which is `G`
    (∀ j < B.length - 1, ∀ H ∈ i.2.2, B.getD j (0, 0) ≠ H.1) ∧
    B.getD (B.length - 1) (0, 0) = G.1 ∧
    -- it does not end at `G`'s dot
    ¬ IsStep G.1 ((F.1 :: B).getD (B.length - 1) (0, 0)) G.2.1 ∧
    -- a numbered firefly prescribes the number of bends
    (F.2.2.1 = true → bends (F.1 :: B) = F.2.2.2)

/-- Every firefly `f` has a beam `beam f` ending at `tgt f`, the beams do not intersect, and the
beams connect all fireflies into one component. -/
def HotaruBeamFeasible (i : HotaruBeamInstance) : Prop :=
  ∃ (beam : Fin i.2.2.length → List (ℕ × ℕ)) (tgt : Fin i.2.2.length → Fin i.2.2.length),
    (∀ f, BeamOK i i.2.2[f] i.2.2[tgt f] (beam f)) ∧
    (∀ f f', ∀ j < (beam f).length - 1, ∀ j' < (beam f').length - 1,
      (beam f).getD j (0, 0) = (beam f').getD j' (0, 0) → f = f' ∧ j = j') ∧
    (SimpleGraph.fromRel fun f g => tgt f = g).Connected

open Classical in
/-- HOTARU BEAM as a decision problem over bitstrings. -/
noncomputable def hotaruBeamDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HotaruBeamInstance) x with
  | some i => decide (WellFormed i ∧ HotaruBeamFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HotaruBeam
