/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Basic
import Mathlib.Tactic.FinCases

/-!
# Nim on a cube

A position lists the six face counts in three opposite pairs. In vertex Nim a move can
reduce at most one count in each pair. The normal-play P-positions are the positions in
which all three pairs have equal counts.
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

namespace cubeVertexNim_pPositions

private theorem eq_opposite {p : Fin 6 → ℕ} (h : p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5)
    (k : Fin 6) : p k = p (k + 3) := by
  obtain ⟨ha, hb, hc⟩ := h
  fin_cases k <;> first | assumption | symm; assumption

end cubeVertexNim_pPositions

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
theorem cubeVertexNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 = p 3 ∧ p 1 = p 4 ∧ p 2 = p 5}
    (∀ p q, p ∈ P → CubeVertexMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeVertexMove p q ∧ q ∈ P := by
  constructor
  · rintro p q hp ⟨x, y, z, hx, hy, hz, -, hne, hfix⟩ hq
    apply hne
    funext k
    -- At least one face in the opposite pair lies outside the chosen vertex.
    have untouched : ∀ x y z k : Fin 6, x.val % 3 = 0 → y.val % 3 = 1 → z.val % 3 = 2 →
        (k ≠ x ∧ k ≠ y ∧ k ≠ z) ∨ (k + 3 ≠ x ∧ k + 3 ≠ y ∧ k + 3 ≠ z) := by decide
    rcases untouched x y z k hx hy hz with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact hfix k h₁ h₂ h₃
    · exact (cubeVertexNim_pPositions.eq_opposite hq k).trans
        ((hfix (k + 3) h₁ h₂ h₃).trans (cubeVertexNim_pPositions.eq_opposite hp k).symm)
  · intro p hp
    let a := min (p 0) (p 3)
    let b := min (p 1) (p 4)
    let c := min (p 2) (p 5)
    let q : Fin 6 → ℕ := ![a, b, c, a, b, c]
    have hq : q 0 = q 3 ∧ q 1 = q 4 ∧ q 2 = q 5 := ⟨rfl, rfl, rfl⟩
    -- Select a larger face in each pair. The other face already holds the pair's minimum.
    let larger (i j : Fin 6) := if p i ≤ p j then j else i
    have keep (i j : Fin 6) :
        (i ≠ larger i j → min (p i) (p j) = p i) ∧
        (j ≠ larger i j → min (p i) (p j) = p j) := by
      by_cases h : p i ≤ p j
      · simp [larger, h]
      · simp [larger, h, Nat.min_eq_right (Nat.le_of_not_ge h)]
    have axis (i j : Fin 6) (h : j.val % 3 = i.val % 3) :
        (larger i j).val % 3 = i.val % 3 := by
      dsimp only [larger]
      split <;> first | exact h | rfl
    refine ⟨q, ⟨larger 0 3, larger 1 4, larger 2 5, axis 0 3 rfl, axis 1 4 rfl,
      axis 2 5 rfl, ?_, ?_, ?_⟩, hq⟩
    · intro k
      fin_cases k <;> first | apply Nat.min_le_left | apply Nat.min_le_right
    · exact fun h => hp (h ▸ hq)
    · intro k hx hy hz
      fin_cases k
      · exact (keep 0 3).1 hx
      · exact (keep 1 4).1 hy
      · exact (keep 2 5).1 hz
      · exact (keep 0 3).2 hx
      · exact (keep 1 4).2 hy
      · exact (keep 2 5).2 hz

end

end MetaMathlibExt
