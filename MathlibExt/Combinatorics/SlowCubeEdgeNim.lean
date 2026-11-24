/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# Slow edge Nim on a cube

`slowCubeEdgeNim_pPositions` characterizes the normal-play P-positions by equality of the
parities of the three opposite-pair totals.
-/

namespace MetaMathlibExt

namespace slowCubeEdgeNim_pPositions

private theorem opposite_opposite : ∀ k : Fin 6, k + 3 + 3 = k := by decide

private def parity (p : Fin 6 → ℕ) (k : Fin 6) : ℕ := (p k + p (k + 3)) % 2

private theorem common_parity {p : Fin 6 → ℕ}
    (h : parity p 0 = parity p 1 ∧ parity p 1 = parity p 2) (k : Fin 6) :
    parity p k = parity p 0 := by
  have opposite (i : Fin 6) : parity p (i + 3) = parity p i := by
    simp only [parity, opposite_opposite, Nat.add_comm (p (i + 3)) (p i)]
  fin_cases k
  · rfl
  · exact h.1.symm
  · exact (h.1.trans h.2).symm
  · exact opposite 0
  · exact (opposite 1).trans h.1.symm
  · exact (opposite 2).trans (h.1.trans h.2).symm

-- The changed faces fit on an edge exactly when every opposite pair has an unchanged
-- face and at least one pair has both faces unchanged.
private theorem edge_support (p q : Fin 6 → ℕ) :
    (∃ x y : Fin 6, x.val % 3 ≠ y.val % 3 ∧ ∀ k, k ≠ x → k ≠ y → q k = p k) ↔
      (∀ k, q k = p k ∨ q (k + 3) = p (k + 3)) ∧
      ∃ k, q k = p k ∧ q (k + 3) = p (k + 3) := by
  have geometry : ∀ fixed : Fin 6 → Bool,
      (∃ x y : Fin 6, x.val % 3 ≠ y.val % 3 ∧ ∀ k, k ≠ x → k ≠ y → fixed k = true) ↔
        (∀ k, fixed k = true ∨ fixed (k + 3) = true) ∧
        ∃ k, fixed k = true ∧ fixed (k + 3) = true := by decide
  simpa using geometry (fun k => decide (q k = p k))

-- In an odd pair remove one token from its unique odd pile.
private def trim (a b : ℕ) : ℕ := if b % 2 = 0 then a - a % 2 else a

private theorem trim_pair (a b : ℕ) :
    (trim a b + trim b a) % 2 = 0 ∧
      (trim a b = a ∨ trim b a = b) ∧
      ((a + b) % 2 = 0 → trim a b = a ∧ trim b a = b) := by
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;> simp [trim, ha, hb] <;> omega

end slowCubeEdgeNim_pPositions

open slowCubeEdgeNim_pPositions in
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
public theorem slowCubeEdgeNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeEdgeMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) :=
      {p | (p 0 + p 3) % 2 = (p 1 + p 4) % 2 ∧ (p 1 + p 4) % 2 = (p 2 + p 5) % 2}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P := by
  constructor
  · rintro p q hp ⟨⟨x, y, hxy, hle, hne, hfix⟩, hslow⟩ hq
    obtain ⟨oneFixed, k, hk, hk'⟩ := (edge_support p q).mp ⟨x, y, hxy, hfix⟩
    have same (i : Fin 6) : parity q i = parity p i := calc
      parity q i = parity q 0 := common_parity hq i
      _ = parity q k := (common_parity hq k).symm
      _ = parity p k := by simp only [parity, hk, hk']
      _ = parity p 0 := common_parity hp k
      _ = parity p i := (common_parity hp i).symm
    apply hne
    funext i
    rcases oneFixed i with hi | hi
    · exact hi
    · have heq := same i
      simp only [parity, hi] at heq
      by_contra h
      have lower : q i ≤ p i := hle i
      have upper := hslow i
      have step : p i = q i + 1 := by omega
      rw [step] at heq
      omega
  · intro p hp
    change ¬ (parity p 0 = parity p 1 ∧ parity p 1 = parity p 2) at hp
    have evenPair : ∃ k, parity p k = 0 := by
      by_contra! h
      have odd (k : Fin 6) : parity p k = 1 := by
        have hk := h k
        unfold parity at hk ⊢
        omega
      exact hp ⟨(odd 0).trans (odd 1).symm, (odd 1).trans (odd 2).symm⟩
    let q (k : Fin 6) := trim (p k) (p (k + 3))
    have pairs (k : Fin 6) :
        parity q k = 0 ∧ (q k = p k ∨ q (k + 3) = p (k + 3)) ∧
          (parity p k = 0 → q k = p k ∧ q (k + 3) = p (k + 3)) := by
      simpa only [parity, q, opposite_opposite] using trim_pair (p k) (p (k + 3))
    obtain ⟨k, hk⟩ := evenPair
    obtain ⟨x, y, hxy, hfix⟩ := (edge_support p q).mpr
      ⟨fun i => (pairs i).2.1, k, (pairs k).2.2 hk⟩
    have hq : parity q 0 = parity q 1 ∧ parity q 1 = parity q 2 :=
      ⟨(pairs 0).1.trans (pairs 1).1.symm, (pairs 1).1.trans (pairs 2).1.symm⟩
    refine ⟨q, ⟨⟨x, y, hxy, ?_, fun h => hp (h ▸ hq), hfix⟩, ?_⟩, hq⟩
    · intro i
      dsimp only [q, trim]
      split <;> omega
    · intro i
      dsimp only [q, trim]
      split <;> omega

end MetaMathlibExt
