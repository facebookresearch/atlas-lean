/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim

/-! # Slow vertex Nim on a cube -/

namespace MetaMathlibExt

namespace slowCubeVertexNim_pPositions

private theorem move_add_iff (p q r : Fin 6 → ℕ) :
    CubeVertexMove (fun k => p k + r k) (fun k => q k + r k) ↔ CubeVertexMove p q := by
  simp [CubeVertexMove, Pi.le_def, funext_iff]

end slowCubeVertexNim_pPositions

open slowCubeVertexNim_pPositions in
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
public theorem slowCubeVertexNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeVertexMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) :=
      {p | (p 0 + p 3) % 2 = 0 ∧ (p 1 + p 4) % 2 = 0 ∧ (p 2 + p 5) % 2 = 0}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P := by
  constructor
  · rintro p q ⟨hp₀, hp₁, hp₂⟩ ⟨hm, hslow⟩ ⟨hq₀, hq₁, hq₂⟩
    -- The removed tokens form a binary position with an ordinary vertex move to zero.
    have hle : q ≤ p := by
      obtain ⟨_, _, _, _, _, _, hle, _⟩ := hm
      exact hle
    let d (k : Fin 6) := p k - q k
    have restore : (fun k => d k + q k) = p := funext fun k => Nat.sub_add_cancel (hle k)
    have hmove : CubeVertexMove d 0 := (move_add_iff d 0 q).mp (by simpa [restore] using hm)
    -- Even pair sums before and after the move force equal removals on opposite faces.
    have equal (i j : Fin 6) (hp : (p i + p j) % 2 = 0) (hq : (q i + q j) % 2 = 0) :
        d i = d j := by
      have bits (k : Fin 6) : p k = q k ∨ p k = q k + 1 := by
        have h₁ : q k ≤ p k := hle k
        have h₂ : p k ≤ q k + 1 := hslow k
        omega
      dsimp [d]
      rcases bits i with hi | hi <;> rcases bits j with hj | hj <;> omega
    exact cubeVertexNim_pPositions.1 d 0
      ⟨equal 0 3 hp₀ hq₀, equal 1 4 hp₁ hq₁, equal 2 5 hp₂ hq₂⟩ hmove ⟨rfl, rfl, rfl⟩
  · intro p hp
    -- Play ordinary vertex Nim on the parity bits, keeping the even part of each pile.
    let r (k : Fin 6) := p k % 2
    let b (k : Fin 6) := 2 * (p k / 2)
    have restore : (fun k => r k + b k) = p := funext fun k => Nat.mod_add_div _ _
    have even_of_eq (i j : Fin 6) (h : r i = r j) : (p i + p j) % 2 = 0 := by
      dsimp [r] at h
      omega
    obtain ⟨s, hm, ha, hb, hc⟩ := cubeVertexNim_pPositions.2 r fun ⟨ha, hb, hc⟩ =>
      hp ⟨even_of_eq 0 3 ha, even_of_eq 1 4 hb, even_of_eq 2 5 hc⟩
    refine ⟨fun k => s k + b k, ⟨restore ▸ (move_add_iff r s b).mpr hm, ?_⟩, ?_⟩
    · intro k
      dsimp [b]
      omega
    · have even_pair (i j : Fin 6) (h : s i = s j) :
          (s i + b i + (s j + b j)) % 2 = 0 := by
        dsimp [b]
        omega
      exact ⟨even_pair 0 3 ha, even_pair 1 4 hb, even_pair 2 5 hc⟩

end MetaMathlibExt
