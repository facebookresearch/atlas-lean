/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOTARU BEAM: definitions

Source:
T. Otsuji, P. Fulla and T. Fukunaga, "NP-completeness and physical zero-knowledge proof of
Hotaru Beam", arXiv:2603.01393 (2026) (Section 2: the rules; Theorem 1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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
