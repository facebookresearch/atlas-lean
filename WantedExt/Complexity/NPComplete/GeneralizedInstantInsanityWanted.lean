/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED INSTANT INSANITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP15] GENERALIZED
INSTANT INSANITY;
E. Robertson and I. Munro, "NP-completeness, puzzles and games", Utilitas
Mathematica 13 (1978), 99-116.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity

/-!
# GENERALIZED INSTANT INSANITY is NP-complete

INSTANCE: a set `Q` of cubes and a set `C` of colors with `|Q| = |C|`, and for each cube
`q ∈ Q` an assignment of a color in `C` to each of the six faces of `q`. QUESTION: can the
cubes in `Q` be stacked in a vertical column such that each of the colors in `C` appears
exactly once on each of the four sides of the column?

A cube is given by its three pairs of opposite faces. Placing a cube in the column chooses a
front-back axis and a different right-left axis (the remaining axis is vertical and hidden),
and which face of each chosen pair faces front and right. These choices give exactly the side
colors of the 24 rotations of a cube: for each of the 3 vertical axes, the rotations about it
together with the half-turn that flips the cube over realize all 8 ways to put one remaining
pair front-back and the other right-left, in either order. The order of the cubes in the
column does not affect the side colors. Colors are `0, ..., |C| - 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **GENERALIZED INSTANT INSANITY is NP-complete.** Source: Garey and Johnson (1979), [GP15];
Robertson and Munro (1978). -/
public theorem_wanted generalizedInstantInsanity_npComplete :
    generalizedInstantInsanityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedInstantInsanityDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity
