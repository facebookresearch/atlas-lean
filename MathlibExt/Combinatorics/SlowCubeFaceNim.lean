/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import MathlibExt.Combinatorics.CubeNim
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Slow face Nim on a cube

`slowCubeFaceNim_pPositions` characterizes the normal-play P-positions by the parity of the
total number of tokens on the six faces.
-/

namespace MetaMathlibExt

namespace slowCubeFaceNim_pPositions

private theorem total_drop {p q : Fin 6 → ℕ} (hm : CubeFaceMove p q)
    (hslow : ∀ k, p k ≤ q k + 1) : (∑ k, p k) = (∑ k, q k) + 1 := by
  obtain ⟨i, hle, hne, hfix⟩ := hm
  have hi : q i ≠ p i := fun h => hne (funext ((and_forall_ne i).mp ⟨h, hfix⟩))
  have delta (k : Fin 6) : p k = q k + (if k = i then 1 else 0) := by
    obtain rfl | hk := eq_or_ne k i
    · have lower : q k ≤ p k := hle k
      have upper := hslow k
      simpa using (show p k = q k + 1 by omega)
    · simp [hk, hfix k hk]
  simp [delta, Finset.sum_add_distrib]

end slowCubeFaceNim_pPositions

open slowCubeFaceNim_pPositions in
/-- **P-positions of slow face Nim on a cube.** Write a position of the cube game as
$p = (a, b, c, A, B, C)$, the numbers of tokens on the six faces of a cube. A slow face move is
a face move that removes exactly one token from one face. Let $P$ be the set of positions with
$a + b + c + A + B + C$ even. Then no slow face move leads from a position in $P$ to a position
in $P$, and from every position not in $P$ some slow face move leads to a position in $P$.

Since every play terminates, these two properties make $P$ the set of P-positions of the slow
game under normal play.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 12 (`integers-2025-G2-thm-12`). -/
public theorem slowCubeFaceNim_pPositions :
    let M : (Fin 6 → ℕ) → (Fin 6 → ℕ) → Prop := fun p q =>
      CubeFaceMove p q ∧ ∀ k, p k ≤ q k + 1
    let P : Set (Fin 6 → ℕ) := {p | (∑ k, p k) % 2 = 0}
    (∀ p q, p ∈ P → M p q → q ∉ P) ∧ ∀ p, p ∉ P → ∃ q, M p q ∧ q ∈ P := by
  constructor
  · rintro p q hp ⟨hm, hslow⟩
    change (∑ k, p k) % 2 = 0 at hp
    change (∑ k, q k) % 2 ≠ 0
    have := total_drop hm hslow
    omega
  · intro p hp
    change (∑ k, p k) % 2 ≠ 0 at hp
    have hne : p ≠ 0 := by
      rintro rfl
      simp at hp
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    change p i ≠ 0 at hi
    let q := Function.update p i (p i - 1)
    have hm : CubeFaceMove p q :=
      ⟨i, by simp [q], Function.update_ne_self_iff.mpr (by omega),
        fun k hk => Function.update_of_ne hk _ _⟩
    have hslow (k : Fin 6) : p k ≤ q k + 1 := by
      obtain rfl | hk := eq_or_ne k i
      · simp [q]
        omega
      · simp [q, hk]
    refine ⟨q, ⟨hm, hslow⟩, ?_⟩
    change (∑ k, q k) % 2 = 0
    have := total_drop hm hslow
    omega

end MetaMathlibExt
