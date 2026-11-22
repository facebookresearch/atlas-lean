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

/-- **Rotation move on the cube.** Label the faces of a cube $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and record a position as the tuple
$p = (a, b, c, A, B, C)$ of numbers of tokens on these faces. A rotation is one of the three
belts of four faces $\{f_a, f_b, f_A, f_B\}$, $\{f_a, f_c, f_A, f_C\}$ and
$\{f_b, f_c, f_B, f_C\}$. In the game $C_R$ there is a move from a position $p$ to a position $q$
when, for some rotation, $q$ agrees with $p$ on the two faces outside the rotation, $q \le p$ on
every face, and $q \ne p$; that is, at least one token in total is removed from the four faces
of the rotation.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 2 (the variation `C_R`). -/
def CubeRotationMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ i j : Fin 6, ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) ∧
    q ≤ p ∧ q ≠ p ∧
    ∀ k : Fin 6, k ≠ i → k ≠ j → k ≠ i + 3 → k ≠ j + 3 → q k = p k

/-- **Rotation moves at the empty cube.** Write positions as tuples $(a, b, c, A, B, C)$ of numbers
of tokens on the faces $f_a, f_b, f_c, f_A, f_B, f_C$ of a cube. In the game $C_R$ there is a
rotation move from $(0, 0, 0, 0, 0, 1)$ to the empty position $(0, 0, 0, 0, 0, 0)$, and there is
no rotation move from the empty position.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 2 (the variation `C_R`). -/
theorem cubeRotationMove_examples :
    CubeRotationMove ![0, 0, 0, 0, 0, 1] 0 ∧ ∀ q, ¬ CubeRotationMove 0 q := by
  refine ⟨⟨0, 2, by decide, fun k => Nat.zero_le _, fun h => by
    simpa using congrFun h 5, by decide⟩, ?_⟩
  rintro q ⟨i, j, -, hle, hne, -⟩
  exact hne (le_antisymm hle fun k => Nat.zero_le _)

/-- **Vertex move on the cube.** Label the faces of a cube $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and record a position as the tuple
$p = (a, b, c, A, B, C)$ of numbers of tokens on these faces. In the game $C_V$ there is a move
from a position $p$ to a position $q$ when, for some choice of one face from each opposite pair
$\{f_a, f_A\}$, $\{f_b, f_B\}$, $\{f_c, f_C\}$ (three faces that meet at a vertex), $q$ agrees
with $p$ on the other three faces, $q \le p$ on every face, and $q \ne p$; that is, at least one
token in total is removed from the three faces at one vertex.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_V`). -/
def CubeVertexMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ x y z : Fin 6, x.val % 3 = 0 ∧ y.val % 3 = 1 ∧ z.val % 3 = 2 ∧ q ≤ p ∧ q ≠ p ∧
    ∀ k : Fin 6, k ≠ x → k ≠ y → k ≠ z → q k = p k

/-- **Edge move on the cube.** Label the faces of a cube $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and record a position as the tuple
$p = (a, b, c, A, B, C)$ of numbers of tokens on these faces. In the game $C_E$ there is a move
from a position $p$ to a position $q$ when, for some two faces from different opposite pairs
(two faces that share an edge), $q$ agrees with $p$ on the other four faces, $q \le p$ on every
face, and $q \ne p$; that is, at least one token in total is removed from the two faces at one
edge.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_E`). -/
def CubeEdgeMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ x y : Fin 6, x.val % 3 ≠ y.val % 3 ∧ q ≤ p ∧ q ≠ p ∧ ∀ k : Fin 6, k ≠ x → k ≠ y → q k = p k

/-- **Face move on the cube.** Label the faces of a cube $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and record a position as the tuple
$p = (a, b, c, A, B, C)$ of numbers of tokens on these faces. In the game $C_F$ there is a move
from a position $p$ to a position $q$ when, for some face, $q$ agrees with $p$ on the other five
faces, $q \le p$ on every face, and $q \ne p$; that is, at least one token is removed from one
face. So $C_F$ is Nim with six heaps.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Section 1 (the variation `C_F`). -/
def CubeFaceMove (p q : Fin 6 → ℕ) : Prop :=
  ∃ x : Fin 6, q ≤ p ∧ q ≠ p ∧ ∀ k : Fin 6, k ≠ x → q k = p k

/-- **Examples of vertex, edge and face moves.** Write positions as tuples $(a, b, c, A, B, C)$ of
numbers of tokens on the faces $f_a, f_b, f_c, f_A, f_B, f_C$ of a cube. There is a vertex move
(game $C_V$) from $(1, 1, 1, 0, 0, 0)$ to the empty position $(0, 0, 0, 0, 0, 0)$, an edge move
(game $C_E$) from $(1, 1, 0, 0, 0, 0)$ to the empty position, and a face move (game $C_F$) from
$(1, 1, 1, 0, 0, 0)$ to $(0, 1, 1, 0, 0, 0)$. No vertex move, edge move or face move starts at
the empty position.

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

/-- **P-positions of rotation Nim on a cube.** Write positions of the game $C_R$ as tuples
$(a, b, c, A, B, C)$ of numbers of tokens on the faces $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$. Let $\mathcal P$ be the set of positions with
$a + A = b + B = c + C$. Then no rotation move leads from a position in $\mathcal P$ to a position
in $\mathcal P$, and from every position outside $\mathcal P$ there is a rotation move to a
position in $\mathcal P$.

Every move removes a token, so the game terminates and $\mathcal P$ is exactly the set of
P-positions (second-player wins) under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 5 (`integers-2025-G2-thm-5`). -/
public theorem_wanted cubeRotationNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 + p 3 = p 1 + p 4 ∧ p 1 + p 4 = p 2 + p 5}
    (∀ p q, p ∈ P → CubeRotationMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeRotationMove p q ∧ q ∈ P

/-- **P-positions of vertex Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$; a vertex move removes at
least one token in total from the three faces at one vertex (one face from each opposite pair).
Let $P$ be the set of positions with $a = A$, $b = B$ and $c = C$. Then no vertex move leads
from a position in $P$ to a position in $P$, and from every position not in $P$ some vertex
move leads to a position in $P$.

Since every play terminates, these two properties make $P$ the set of P-positions
(second-player wins) under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 2 (`integers-2025-G2-thm-2`). -/
public theorem_wanted cubeVertexNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5}
    (∀ p q, p ∈ P → CubeVertexMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeVertexMove p q ∧ q ∈ P

/-- **P-positions of edge Nim on a cube.** Write positions of the game $C_E$ as tuples
$(a, b, c, A, B, C)$ of numbers of tokens on the faces $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and let $\oplus$ be the Nim-sum (bitwise
exclusive or) of natural numbers. Let $\mathcal P$ be the set of positions with
$a \oplus A = b \oplus B = c \oplus C$. Then no edge move leads from a position in $\mathcal P$
to a position in $\mathcal P$, and from every position outside $\mathcal P$ there is an edge
move to a position in $\mathcal P$.

Every move removes a token, so the game terminates and $\mathcal P$ is exactly the set of
P-positions (second-player wins) under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 3 (`integers-2025-G2-thm-3`). -/
public theorem_wanted cubeEdgeNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 ^^^ p 3 = p 1 ^^^ p 4 ∧ p 1 ^^^ p 4 = p 2 ^^^ p 5}
    (∀ p q, p ∈ P → CubeEdgeMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeEdgeMove p q ∧ q ∈ P

/-- **Misère P-positions of vertex Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$; a vertex move removes at
least one token in total from the three faces at one vertex (one face from each opposite pair).
Let $P$ be any set of positions such that $p \in P$ if and only if $p$ has a vertex move and
no vertex move from $p$ leads to a position in $P$ (the misère P-positions). Then for every
position $p$ with $a \le A$, $b \le B$, $a \le b$ and $C$ at least every entry of $p$, we have
$p \in P$ if and only if either $a = A$, $b = B$, $c = C$ and $C \ge 2$ all hold, or $p$ is one
of $(0, 0, 0, 0, 0, 1)$, $(0, 1, 1, 0, 1, 1)$ and $(1, 1, 1, 1, 1, 1)$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 6 (`integers-2025-G2-thm-6`). -/
public theorem_wanted cubeVertexNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeVertexMove p q) ∧ ∀ q, CubeVertexMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5 ∧ 2 ≤ p 5) ∨ p = ![0, 0, 0, 0, 0, 1] ∨
      p = ![0, 1, 1, 0, 1, 1] ∨ p = ![1, 1, 1, 1, 1, 1]

/-- **Misère P-positions of rotation Nim on a cube.** Write positions of the game $C_R$ as tuples
$p = (a, b, c, A, B, C)$ of numbers of tokens on the faces $f_a, f_b, f_c, f_A, f_B, f_C$, where
$f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$. Let $\mathcal P$ be any set of positions
such that a position lies in $\mathcal P$ if and only if it has a rotation move and every
rotation move from it leads to a position outside $\mathcal P$; this is the set of P-positions
under misère play, where the player making the last move loses. Let $p$ be a position in which
every entry is at most $C$, and $a \le A$, $b \le B$ and $a \le b$. Then $p \in \mathcal P$ if
and only if either $C \ge 2$ and $a + A = b + B = c + C$, or $p = (0, 0, 0, 0, 0, 1)$, or
$p = (1, 1, 1, 1, 1, 1)$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 8 (`integers-2025-G2-thm-8`). -/
public theorem_wanted cubeRotationNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeRotationMove p q) ∧ ∀ q, CubeRotationMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 + p 3 = p 1 + p 4 ∧ p 1 + p 4 = p 2 + p 5) ∨
      p = ![0, 0, 0, 0, 0, 1] ∨ p = ![1, 1, 1, 1, 1, 1]

/-- **Misère P-positions of face Nim on a cube.** Write positions of the game $C_F$ (Nim with six
heaps) as tuples $p = (a, b, c, A, B, C)$ of numbers of tokens on the faces
$f_a, f_b, f_c, f_A, f_B, f_C$, where $f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and let
$\oplus$ be the Nim-sum (bitwise exclusive or) of natural numbers. Let $\mathcal P$ be any set
of positions such that a position lies in $\mathcal P$ if and only if it has a face move and
every face move from it leads to a position outside $\mathcal P$; this is the set of
P-positions under misère play, where the player making the last move loses. Let $p$ be a
position in which every entry is at most $C$, and $a \le A$, $b \le B$ and $a \le b$. Then
$p \in \mathcal P$ if and only if either $C \ge 2$ and $a \oplus b \oplus c \oplus A \oplus B
\oplus C = 0$, or $C < 2$ and $a \oplus b \oplus c \oplus A \oplus B \oplus C = 1$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 9 (`integers-2025-G2-thm-9`). -/
public theorem_wanted cubeFaceNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 0) ∨
      (p 5 < 2 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 1)

/-- **P-positions of slow vertex Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$. A slow vertex move is a vertex
move (removing at least one token in total from the three faces at one vertex, one face from
each opposite pair) in which each face loses at most one token. Let $P$ be the set of positions
for which $a + A$, $b + B$ and $c + C$ are all even. Then no slow vertex move leads from a
position in $P$ to a position in $P$, and from every position not in $P$ some slow vertex move
leads to a position in $P$.

Since every play terminates, these two properties make $P$ the set of P-positions of the slow
game under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 10 (`integers-2025-G2-thm-10`). -/
public theorem_wanted slowCubeVertexNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeVertexMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) :=
      {p | (p 0 + p 3) % 2 = 0 ∧ (p 1 + p 4) % 2 = 0 ∧ (p 2 + p 5) % 2 = 0}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P

/-- **P-positions of slow edge Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$. A slow edge move is an edge
move (removing at least one token in total from two faces in different opposite pairs) in which
each face loses at most one token. Let $P$ be the set of positions for which $a + A$, $b + B$
and $c + C$ are all even or all odd. Then no slow edge move leads from a position in $P$ to a
position in $P$, and from every position not in $P$ some slow edge move leads to a position in
$P$.

Since every play terminates, these two properties make $P$ the set of P-positions of the slow
game under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 11 (`integers-2025-G2-thm-11`). -/
public theorem_wanted slowCubeEdgeNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeEdgeMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) :=
      {p | (p 0 + p 3) % 2 = (p 1 + p 4) % 2 ∧ (p 1 + p 4) % 2 = (p 2 + p 5) % 2}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P

/-- **P-positions of slow face Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube. A slow face move is
a face move that removes exactly one token from one face. Let $P$ be the set of positions with
$a + b + c + A + B + C$ even. Then no slow face move leads from a position in $P$ to a position
in $P$, and from every position not in $P$ some slow face move leads to a position in $P$.

Since every play terminates, these two properties make $P$ the set of P-positions of the slow
game under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 12 (`integers-2025-G2-thm-12`). -/
public theorem_wanted slowCubeFaceNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeFaceMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) := {p | (∑ k, p k) % 2 = 0}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P

/-- **P-positions of slow rotation Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube, where the faces
carrying $A$, $B$, $C$ are opposite those carrying $a$, $b$, $c$. A slow rotation move is a
rotation move (removing at least one token in total from the four faces of one rotation, that is
from the faces of two opposite pairs) in which each face loses at most one token. Let $P$ be any
set of positions such that $p \in P$ if and only if no slow rotation move from $p$ leads to a
position in $P$ (the P-positions under normal play). Then for every position $p$ with
$a \le A$, $b \le B$ and $c \le C$, we have $p \in P$ if and only if the vector of remainders
$(a, b, c, A, B, C) \bmod 2$ is one of $(0, 0, 0, 0, 0, 0)$, $(0, 0, 0, 1, 1, 1)$,
$(1, 1, 1, 0, 0, 0)$ and $(1, 1, 1, 1, 1, 1)$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 13 (`integers-2025-G2-thm-13`). -/
public theorem_wanted slowCubeRotationNim_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ ∀ q, (CubeRotationMove p q ∧ ∀ k, p k ≤ q k + 1) → q ∉ P)
    (p : Fin 6 → ℕ) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hc : p 2 ≤ p 5) :
    p ∈ P ↔ (fun k => p k % 2) ∈ ({![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 0],
      ![1, 1, 1, 1, 1, 1]} : Set (Fin 6 → ℕ))

end

end MetaMathlibExt
