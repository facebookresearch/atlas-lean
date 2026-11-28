/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALL SORT PUZZLE is NP-complete

Source:
T. Ito, J. Kawahara, S. Minato, Y. Otachi, T. Saitoh, A. Suzuki, R. Uehara, T. Uno,
K. Yamanaka and R. Yoshinaka, "Sorting balls and water: equivalence and computational
complexity", Theoretical Computer Science 978 (2023), 114158, doi:10.1016/j.tcs.2023.114158,
Theorem 9 (BSP); arXiv:2202.09495.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BallSortPuzzle

/-!
# BALL SORT PUZZLE is NP-complete

Ito et al. (2023), Section 1: "We are given `n + k` bins of capacity `h`. In an initial
configuration, `n` bins are full (i.e., filled with `h` units) and `k` bins are empty, where
each unit has a color in the color set `C`. Our task is to fill `n` bins monochromatically ...
We define BSP ... as the problem of deciding whether a given initial configuration can be
reconfigured to a sorted configuration by a sequence of ball moves." Section 2.1: a
configuration is a map `S : B → C^{≤h}` (each bin a sequence of at most `h` colors, bottom to
top); a bin is sorted under `S` if `S(b) ∈ {ε, c^h}` for some `c ∈ C`, and `S` is sorted if all
bins are; "A ball-move can modify a configuration `S` into `S'` ... if there are `b₁, b₂ ∈ B`
and `c ∈ C` such that `S(b₁) = S'(b₁) · c`, `TC(S(b₂)) ∈ {c, ε}`, `S'(b₂) = S(b₂) · c`, and
`S(b) = S'(b)` for all `b ∈ B \ {b₁, b₂}`", where `TC` is the top color (`ε` for an empty bin).
Theorem 9: BSP is NP-complete (even with two colors). The paper encodes the `k` empty bins by
the number `k` ("`Θ(nh log |C| + log k)` bits").

INSTANCE: a capacity `h`, a number `k` of empty bins, and `n` full bins, each a sequence of `h`
colors.
QUESTION: can ball moves turn the configuration (the `n` full bins and `k` empty bins) into one
in which every bin is empty or holds `h` balls of one color?

Representation. Colors are natural numbers; a bin is the list of its colors from bottom to top;
a configuration is the list of its bins (the full bins, then `k` empty ones). A ball move takes
the top ball `c` of bin `b₁` and puts it on bin `b₂ ≠ b₁` when `b₂` is empty or has top `c`, and
holds fewer than `h` balls (so that `S'(b₂)` has length at most `h`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(h, k, F)`: the capacity `h`, the number `k` of empty bins, and a list `F` of
lists of natural colors, read as the full bins, each from bottom to top. A bin of `F` may hold
more or fewer than `h` balls; that every bin of `F` is full, with exactly `h` balls, belongs to
`WellFormed`. -/
abbrev BallSortPuzzleInstance := ℕ × ℕ × List (List ℕ)

/-- The initial configuration: the full bins followed by `k` empty bins. -/
def initial (i : BallSortPuzzleInstance) : List (List ℕ) := i.2.2 ++ List.replicate i.2.1 []

/-- A ball move with capacity `h` from configuration `s` to `s'`: the top ball `c` of bin `b₁`
moves onto bin `b₂ ≠ b₁`, which is empty or has top color `c` and holds fewer than `h` balls. -/
def BallMove (h : ℕ) (s s' : List (List ℕ)) : Prop :=
  ∃ b₁ b₂ : Fin s.length, b₁ ≠ b₂ ∧ ∃ (c : ℕ) (rest : List ℕ), s[b₁] = rest ++ [c] ∧
    (s[b₂] = [] ∨ s[b₂].getLast? = some c) ∧ s[b₂].length + 1 ≤ h ∧
    s' = (s.set b₁ rest).set b₂ (s[b₂] ++ [c])

/-- A configuration is sorted: every bin is empty or holds `h` balls of one color. -/
def Sorted (h : ℕ) (s : List (List ℕ)) : Prop :=
  ∀ bin ∈ s, bin = [] ∨ ∃ c, bin = List.replicate h c

/-- Well-formedness: every given bin is full, with exactly `h` balls. -/
def WellFormed (i : BallSortPuzzleInstance) : Prop :=
  ∀ bin ∈ i.2.2, bin.length = i.1

/-- Some sequence of ball moves turns the initial configuration into a sorted one. -/
def BallSortPuzzleFeasible (i : BallSortPuzzleInstance) : Prop :=
  ∃ s, Relation.ReflTransGen (BallMove i.1) (initial i) s ∧ Sorted i.1 s

open Classical in
/-- BALL SORT PUZZLE as a decision problem over bitstrings. -/
noncomputable def ballSortPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BallSortPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ BallSortPuzzleFeasible i)
  | none => false

/-- **BALL SORT PUZZLE is NP-complete.** Source: Ito et al. (2023), Theorem 9. -/
public theorem_wanted ballSortPuzzle_npComplete :
    ballSortPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ballSortPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.BallSortPuzzle
