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
public import MathlibExt.Combinatorics.MisereCubeRotationNim
public import MathlibExt.Combinatorics.MisereCubeFaceNim
public import MathlibExt.Combinatorics.SlowCubeEdgeNim
public import MathlibExt.Combinatorics.SlowCubeFaceNim
public import MathlibExt.Combinatorics.SlowCubeVertexNim
public import MathlibExt.Combinatorics.CubeRotationNimCubeEdgeNimPPositions
public import MathlibExt.Combinatorics.CubeRotationPPositions

/-!
# Nim games on a cube

Statement-only targets from Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game
Played on a Cube*, INTEGERS 25 (2025), Article G2. The theorem `cubeEdgeNim_pPositions` is
proved in `MathlibExt.Combinatorics.CubeRotationNimCubeEdgeNimPPositions`, and
`cubeRotationNim_pPositions` is proved in `MathlibExt.Combinatorics.CubeRotationPPositions`.

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
