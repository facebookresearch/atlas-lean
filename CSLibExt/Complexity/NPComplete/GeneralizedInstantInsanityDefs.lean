/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED INSTANT INSANITY: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP15] GENERALIZED
INSTANT INSANITY;
E. Robertson and I. Munro, "NP-completeness, puzzles and games", Utilitas
Mathematica 13 (1978), 99-116.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity

/-- A colored cube: the colors of its three pairs of opposite faces. -/
abbrev Cube := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- An instance: the number of colors `|C|` and the list of cubes `Q`. -/
abbrev GeneralizedInstantInsanityInstance := ℕ × List Cube

/-- The `a`-th pair of opposite faces of a cube. -/
def oppositePair (c : Cube) : Fin 3 → ℕ × ℕ := ![c.1, c.2.1, c.2.2]

/-- The color of one face of the `a`-th pair: the second face if `s`, else the first. -/
def faceColor (c : Cube) (a : Fin 3) (s : Bool) : ℕ :=
  if s then (oppositePair c a).2 else (oppositePair c a).1

/-- Well-formedness of an instance: `|Q| = |C|` and every face color is one of the `|C|`
colors. -/
def WellFormed (i : GeneralizedInstantInsanityInstance) : Prop :=
  i.2.length = i.1 ∧
    ∀ c ∈ i.2, c.1.1 < i.1 ∧ c.1.2 < i.1 ∧ c.2.1.1 < i.1 ∧ c.2.1.2 < i.1 ∧
      c.2.2.1 < i.1 ∧ c.2.2.2 < i.1

/-- Each of the colors `0, ..., n - 1` appears exactly once on a side, where `side q` is the
color cube `q` shows on that side. -/
def ExactlyOnce (n : ℕ) {m : ℕ} (side : Fin m → ℕ) : Prop :=
  ∀ col < n, ∃! q, side q = col

/-- A stacking: for each cube `q`, a front-back axis `fb q`, a different right-left axis
`lr q`, and which face of each faces front (`sf q`) and right (`sr q`), such that each color
appears exactly once on the front, back, right, and left sides. -/
def GeneralizedInstantInsanityFeasible (i : GeneralizedInstantInsanityInstance) : Prop :=
  ∃ (fb lr : Fin i.2.length → Fin 3) (sf sr : Fin i.2.length → Bool),
    (∀ q, fb q ≠ lr q) ∧
    ExactlyOnce i.1 (fun q => faceColor (i.2.get q) (fb q) (sf q)) ∧
    ExactlyOnce i.1 (fun q => faceColor (i.2.get q) (fb q) (!sf q)) ∧
    ExactlyOnce i.1 (fun q => faceColor (i.2.get q) (lr q) (sr q)) ∧
    ExactlyOnce i.1 (fun q => faceColor (i.2.get q) (lr q) (!sr q))

open Classical in
/-- GENERALIZED INSTANT INSANITY as a decision problem over bitstrings. -/
noncomputable def generalizedInstantInsanityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedInstantInsanityInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedInstantInsanityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity
