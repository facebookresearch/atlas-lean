/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Nim games on a cube

Statement-only targets from Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game
Played on a Cube*, INTEGERS 25 (2025), Article G2.

A position `p : Fin 6 → ℕ` lists the token counts `(a, b, c, A, B, C)` on the faces
`f_a, f_b, f_c, f_A, f_B, f_C` (indices `0, …, 5`; `f_A` is opposite `f_a`, and so on). In the
game `C_R` a move selects one of the three rotations `f_a - f_b - f_A - f_B`,
`f_a - f_c - f_A - f_C`, `f_b - f_c - f_B - f_C` (index sets `{0, 1, 3, 4}`, `{0, 2, 3, 5}`,
`{1, 2, 4, 5}`) and removes at least one token in total from the four faces of that rotation.
Play is normal (the player making the last move wins) unless stated otherwise.

The other variants select one vertex (`C_V`: the three faces at the vertex, one from each
opposite pair), one edge (`C_E`: two faces from different opposite pairs) or one face (`C_F`)
and remove at least one token in total from the selected faces. In the slow versions every
selected face loses at most one token. Under misère play the player making the last move
loses. Where the paper states its P-positions only up to the cube's symmetries, the statement
takes the P-positions `P` as given by their recursive characterization and describes `P` on
the normalized positions the paper fixes.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A move of the cube game `C_R`: `q` is obtained from `p` by removing at least one token in
total from the four faces of one rotation, leaving the other two faces unchanged.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 2 (the variation `C_R`). -/
def CubeRotationMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ i j : Fin 6, ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) ∧
    q ≤ p ∧ q ≠ p ∧
    ∀ k : Fin 6, k ≠ i → k ≠ j → k ≠ i + 3 → k ≠ j + 3 → q k = p k

/-- From `(0, 0, 0, 0, 0, 1)` the only moves empty the cube, and the empty cube has no move.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 2 (the variation `C_R`). -/
theorem cubeRotationMove_examples :
    CubeRotationMove ![0, 0, 0, 0, 0, 1] 0 ∧ ∀ q, ¬ CubeRotationMove 0 q := by
  refine ⟨⟨0, 2, by decide, fun k => Nat.zero_le _, fun h => by
    simpa using congrFun h 5, by decide⟩, ?_⟩
  rintro q ⟨i, j, -, hle, hne, -⟩
  exact hne (le_antisymm hle fun k => Nat.zero_le _)

/-- A move of the cube game `C_V`: `q` is obtained from `p` by removing at least one token in
total from the three faces at one vertex, one face from each opposite pair (indices `x`, `y`,
`z` with `x ≡ 0`, `y ≡ 1`, `z ≡ 2 (mod 3)`), leaving the other three faces unchanged.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_V`). -/
def CubeVertexMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ x y z : Fin 6, x.val % 3 = 0 ∧ y.val % 3 = 1 ∧ z.val % 3 = 2 ∧ q ≤ p ∧ q ≠ p ∧
    ∀ k : Fin 6, k ≠ x → k ≠ y → k ≠ z → q k = p k

/-- A move of the cube game `C_E`: `q` is obtained from `p` by removing at least one token in
total from the two faces sharing one edge (two faces from different opposite pairs), leaving
the other four faces unchanged.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_E`). -/
def CubeEdgeMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ x y : Fin 6, x.val % 3 ≠ y.val % 3 ∧ q ≤ p ∧ q ≠ p ∧ ∀ k : Fin 6, k ≠ x → k ≠ y → q k = p k

/-- A move of the cube game `C_F`: `q` is obtained from `p` by removing at least one token from
one face, leaving the other five faces unchanged (Nim on six heaps).

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_F`). -/
def CubeFaceMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ x : Fin 6, q ≤ p ∧ q ≠ p ∧ ∀ k : Fin 6, k ≠ x → q k = p k

/-- Vertex, edge and face moves from one token on each of `f_a, f_b, f_c` to the empty cube or
to `(0, 1, 1, 0, 0, 0)`, and the empty cube has no move in any of the three games.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1. -/
theorem cubeVertexEdgeFaceMove_examples :
    CubeVertexMove ![1, 1, 1, 0, 0, 0] 0 ∧ CubeEdgeMove ![1, 1, 0, 0, 0, 0] 0 ∧
      CubeFaceMove ![1, 1, 1, 0, 0, 0] ![0, 1, 1, 0, 0, 0] ∧
      ∀ q, ¬ CubeVertexMove 0 q ∧ ¬ CubeEdgeMove 0 q ∧ ¬ CubeFaceMove 0 q := by
  refine ⟨⟨0, 1, 2, by decide, by decide, by decide, fun k => Nat.zero_le _,
      fun h => by simpa using congrFun h 0, by decide⟩,
    ⟨0, 1, by decide, fun k => Nat.zero_le _, fun h => by simpa using congrFun h 0, by decide⟩,
    ⟨0, fun k => by revert k; decide, fun h => by simpa using congrFun h 0, by decide⟩,
    fun q => ⟨?_, ?_, ?_⟩⟩
  · rintro ⟨-, -, -, -, -, -, hle, hne, -⟩
    exact hne (le_antisymm hle fun k => Nat.zero_le _)
  · rintro ⟨-, -, -, hle, hne, -⟩
    exact hne (le_antisymm hle fun k => Nat.zero_le _)
  · rintro ⟨-, hle, hne, -⟩
    exact hne (le_antisymm hle fun k => Nat.zero_le _)

/-- In `C_R` the second-player winning positions (P-positions) are exactly those with
`a + A = b + B = c + C`: no move joins two such positions, and every other position has a
move to one (for this terminating game this characterizes the P-positions).

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 5 (`integers-2025-G2-thm-5`). -/
public theorem_wanted cubeRotationNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 + p 3 = p 1 + p 4 ∧ p 1 + p 4 = p 2 + p 5}
    (∀ p q, p ∈ P → CubeRotationMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeRotationMove p q ∧ q ∈ P

/-- In `C_V` the P-positions are exactly those with `a = A`, `b = B`, `c = C`: no move joins
two such positions, and every other position has a move to one.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 2 (`integers-2025-G2-thm-2`). -/
public theorem_wanted cubeVertexNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5}
    (∀ p q, p ∈ P → CubeVertexMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeVertexMove p q ∧ q ∈ P

/-- In `C_E` the P-positions are exactly those with `a ⊕ A = b ⊕ B = c ⊕ C` (`⊕` the Nim-sum):
no move joins two such positions, and every other position has a move to one.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 3 (`integers-2025-G2-thm-3`). -/
public theorem_wanted cubeEdgeNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 ^^^ p 3 = p 1 ^^^ p 4 ∧ p 1 ^^^ p 4 = p 2 ^^^ p 5}
    (∀ p q, p ∈ P → CubeEdgeMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeEdgeMove p q ∧ q ∈ P

/-- In `C_V` under misère play, for a position normalized as in the paper (`C = max p`,
`a ≤ A`, `b ≤ B`, `a ≤ b`), `p` is a P-position iff `a = A`, `b = B`, `c = C ≥ 2`, or `p` is
one of `(0, 0, 0, 0, 0, 1)`, `(0, 1, 1, 0, 1, 1)`, `(1, 1, 1, 1, 1, 1)`. Here `P` is the set of
misère P-positions, given by its recursion: `p ∈ P` iff `p` has a move and every move from `p`
leaves `P`.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 6 (`integers-2025-G2-thm-6`). -/
public theorem_wanted cubeVertexNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeVertexMove p q) ∧ ∀ q, CubeVertexMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5 ∧ 2 ≤ p 5) ∨ p = ![0, 0, 0, 0, 0, 1] ∨
      p = ![0, 1, 1, 0, 1, 1] ∨ p = ![1, 1, 1, 1, 1, 1]

/-- In `C_R` under misère play, for a position normalized as in the paper (`C = max p`,
`a ≤ A`, `b ≤ B`, `a ≤ b`), `p` is a P-position iff `C ≥ 2` and `a + A = b + B = c + C`, or `p`
is `(0, 0, 0, 0, 0, 1)` or `(1, 1, 1, 1, 1, 1)`. Here `P` is the set of misère P-positions,
given by its recursion: `p ∈ P` iff `p` has a move and every move from `p` leaves `P`.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 8 (`integers-2025-G2-thm-8`). -/
public theorem_wanted cubeRotationNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeRotationMove p q) ∧ ∀ q, CubeRotationMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 + p 3 = p 1 + p 4 ∧ p 1 + p 4 = p 2 + p 5) ∨
      p = ![0, 0, 0, 0, 0, 1] ∨ p = ![1, 1, 1, 1, 1, 1]

/-- In `C_F` (Nim on six heaps) under misère play, for a position normalized as in the paper
(`C = max p`, `a ≤ A`, `b ≤ B`, `a ≤ b`), `p` is a P-position iff `C ≥ 2` and
`a ⊕ b ⊕ c ⊕ A ⊕ B ⊕ C = 0`, or `C < 2` and `a ⊕ b ⊕ c ⊕ A ⊕ B ⊕ C = 1`. Here `P` is the set
of misère P-positions, given by its recursion: `p ∈ P` iff `p` has a move and every move from
`p` leaves `P`.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 9 (`integers-2025-G2-thm-9`). -/
public theorem_wanted cubeFaceNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 0) ∨
      (p 5 < 2 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 1)

/-- In the slow version of `C_V` (each face at the selected vertex loses at most one token)
the P-positions are exactly those with `a + A`, `b + B`, `c + C` all even: no move joins two
such positions, and every other position has a move to one.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 10 (`integers-2025-G2-thm-10`). -/
public theorem_wanted slowCubeVertexNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeVertexMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) :=
      {p | (p 0 + p 3) % 2 = 0 ∧ (p 1 + p 4) % 2 = 0 ∧ (p 2 + p 5) % 2 = 0}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P

/-- In the slow version of `C_E` (each face at the selected edge loses at most one token) the
P-positions are exactly those where `a + A`, `b + B`, `c + C` are all even or all odd: no move
joins two such positions, and every other position has a move to one.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 11 (`integers-2025-G2-thm-11`). -/
public theorem_wanted slowCubeEdgeNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeEdgeMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) :=
      {p | (p 0 + p 3) % 2 = (p 1 + p 4) % 2 ∧ (p 1 + p 4) % 2 = (p 2 + p 5) % 2}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P

/-- In the slow version of `C_F` (remove exactly one token from one face) the P-positions are
exactly those with `a + b + c + A + B + C` even: no move joins two such positions, and every
other position has a move to one.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 12 (`integers-2025-G2-thm-12`). -/
public theorem_wanted slowCubeFaceNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeFaceMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) := {p | (∑ k, p k) % 2 = 0}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P

/-- In the slow version of `C_R` (each face of the selected rotation loses at most one token),
for a position normalized as in the paper (`a ≤ A`, `b ≤ B`, `c ≤ C`), `p` is a P-position iff
its parity vector `(a, b, c, A, B, C) mod 2` lies in
`Q = {(e,e,e,e,e,e), (e,e,e,o,o,o), (o,o,o,e,e,e), (o,o,o,o,o,o)}`. Here `P` is the set of
P-positions, given by its recursion: `p ∈ P` iff every move from `p` leaves `P`.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 13 (`integers-2025-G2-thm-13`). -/
public theorem_wanted slowCubeRotationNim_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ ∀ q, (CubeRotationMove p q ∧ ∀ k, p k ≤ q k + 1) → q ∉ P)
    (p : Fin 6 → ℕ) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hc : p 2 ≤ p 5) :
    p ∈ P ↔ (fun k => p k % 2) ∈ ({![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 0],
      ![1, 1, 1, 1, 1, 1]} : Set (Fin 6 → ℕ))

end

end MetaMathlibExt
