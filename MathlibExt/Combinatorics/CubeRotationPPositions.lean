/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim
import Mathlib.Tactic.FinCases

/-!
# P-positions of rotation Nim on a cube

A rotation move preserves one opposite-pair sum. To reach a P-position from an
unbalanced position, leave a pair of minimum sum fixed and reduce the other two
pair sums to that minimum.

## References

* Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
  INTEGERS 25 (2025), Article G2, pp. 1–14, Theorem 5 (p. 6).
-/

namespace MetaMathlibExt

private theorem exists_truncated_pair (x y t : ℕ) (ht : t ≤ x + y) :
    ∃ a b, a ≤ x ∧ b ≤ y ∧ a + b = t ∧ (t = x + y → a = x ∧ b = y) := by
  refine ⟨min x t, t - min x t, min_le_left _ _, ?_, ?_, ?_⟩
  · by_cases h : x ≤ t
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right (le_of_not_ge h)]
      omega
  · exact Nat.add_sub_of_le (min_le_right _ _)
  · rintro rfl
    have hx : x ≤ x + y := by omega
    rw [min_eq_left hx]
    exact ⟨rfl, by omega⟩

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
public theorem cubeRotationNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 + p 3 = p 1 + p 4 ∧ p 1 + p 4 = p 2 + p 5}
    (∀ p q, p ∈ P → CubeRotationMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeRotationMove p q ∧ q ∈ P := by
  constructor
  · rintro p q ⟨hp₁, hp₂⟩ ⟨i, j, hij, hle, hne, hfix⟩ ⟨hq₁, hq₂⟩
    -- The fixed pair determines the common sum at both endpoints.
    have hsum : q 0 + q 3 = p 0 + p 3 := by
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h₂ := hfix 2 (by decide) (by decide) (by decide) (by decide)
        have h₅ := hfix 5 (by decide) (by decide) (by decide) (by decide)
        omega
      · have h₁ := hfix 1 (by decide) (by decide) (by decide) (by decide)
        have h₄ := hfix 4 (by decide) (by decide) (by decide) (by decide)
        omega
      · rw [hfix 0 (by decide) (by decide) (by decide) (by decide),
          hfix 3 (by decide) (by decide) (by decide) (by decide)]
    have hsum₁ : q 1 + q 4 = p 1 + p 4 := hq₁.symm.trans (hsum.trans hp₁)
    have hsum₂ : q 2 + q 5 = p 2 + p 5 := hq₂.symm.trans (hsum₁.trans hp₂)
    -- A pair with unchanged sum cannot have lost any tokens.
    have eq_entries {a b x y : ℕ} (ha : a ≤ x) (hb : b ≤ y) (hs : a + b = x + y) :
        a = x ∧ b = y := by
      constructor <;> omega
    obtain ⟨e₀, e₃⟩ := eq_entries (hle 0) (hle 3) hsum
    obtain ⟨e₁, e₄⟩ := eq_entries (hle 1) (hle 4) hsum₁
    obtain ⟨e₂, e₅⟩ := eq_entries (hle 2) (hle 5) hsum₂
    apply hne
    funext k
    fin_cases k <;> assumption
  · intro p hp
    let t := min (p 0 + p 3) (min (p 1 + p 4) (p 2 + p 5))
    obtain ⟨a, A, ha, hA, haSum, haFix⟩ := exists_truncated_pair (p 0) (p 3) t (min_le_left _ _)
    obtain ⟨b, B, hb, hB, hbSum, hbFix⟩ :=
      exists_truncated_pair (p 1) (p 4) t ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨c, C, hc, hC, hcSum, hcFix⟩ :=
      exists_truncated_pair (p 2) (p 5) t ((min_le_right _ _).trans (min_le_right _ _))
    let q : Fin 6 → ℕ := ![a, b, c, A, B, C]
    have hq : q 0 + q 3 = q 1 + q 4 ∧ q 1 + q 4 = q 2 + q 5 :=
      ⟨haSum.trans hbSum.symm, hbSum.trans hcSum.symm⟩
    have hle : q ≤ p := by
      intro k
      fin_cases k <;> assumption
    have hne : q ≠ p := fun h => hp (h ▸ hq)
    have ht : t = p 0 + p 3 ∨ t = p 1 + p 4 ∨ t = p 2 + p 5 := by
      rcases min_choice (p 0 + p 3) (min (p 1 + p 4) (p 2 + p 5)) with h | h
      · exact Or.inl h
      · rcases min_choice (p 1 + p 4) (p 2 + p 5) with h' | h'
        · exact Or.inr (Or.inl (h.trans h'))
        · exact Or.inr (Or.inr (h.trans h'))
    refine ⟨q, ?_, hq⟩
    rcases ht with ht | ht | ht
    · obtain ⟨h₀, h₃⟩ := haFix ht
      refine ⟨1, 2, by decide, hle, hne, ?_⟩
      intro k hk₁ hk₂ hk₄ hk₅
      fin_cases k <;> first | exact h₀ | exact h₃ | contradiction
    · obtain ⟨h₁, h₄⟩ := hbFix ht
      refine ⟨0, 2, by decide, hle, hne, ?_⟩
      intro k hk₀ hk₂ hk₃ hk₅
      fin_cases k <;> first | exact h₁ | exact h₄ | contradiction
    · obtain ⟨h₂, h₅⟩ := hcFix ht
      refine ⟨0, 1, by decide, hle, hne, ?_⟩
      intro k hk₀ hk₁ hk₃ hk₄
      fin_cases k <;> first | exact h₂ | exact h₅ | contradiction

end MetaMathlibExt
