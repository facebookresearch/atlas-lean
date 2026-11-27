/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases

/-!
# P-positions of edge Nim on a cube

No edge move connects two positions with equal Nim-sums on all three opposite pairs.
Every other position has an edge move to one of these positions.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 3.
-/

namespace MetaMathlibExt

private theorem pair_value {p : Fin 6 → ℕ}
    (hp : p 0 ^^^ p 3 = p 1 ^^^ p 4 ∧ p 1 ^^^ p 4 = p 2 ^^^ p 5)
    (k : Fin 6) : p k ^^^ p (k + 3) = p 0 ^^^ p 3 := by
  fin_cases k
  · rfl
  · exact hp.1.symm
  · exact (hp.1.trans hp.2).symm
  · exact Nat.xor_comm _ _
  · exact (Nat.xor_comm _ _).trans hp.1.symm
  · exact (Nat.xor_comm _ _).trans (hp.1.trans hp.2).symm

private theorem reduce_pair (a b t : ℕ) (ht : t ≤ a ^^^ b) :
    ∃ a' b', a' ≤ a ∧ b' ≤ b ∧ a' ^^^ b' = t ∧ (a' = a ∨ b' = b) ∧
      (t = a ^^^ b → a' = a ∧ b' = b) := by
  rcases lt_or_eq_of_le ht with h | h
  · rcases Nat.lt_xor_cases h with ha | hb
    · refine ⟨t ^^^ b, b, ha.le, le_rfl, by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero],
        Or.inr rfl, ?_⟩
      exact fun he => (h.ne he).elim
    · refine ⟨a, t ^^^ a, le_rfl, hb.le, ?_, Or.inl rfl, ?_⟩
      · rw [Nat.xor_comm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · exact fun he => (h.ne he).elim
  · exact ⟨a, b, le_rfl, le_rfl, h.symm, Or.inl rfl, fun _ => ⟨rfl, rfl⟩⟩

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
public theorem cubeEdgeNim_pPositions :
    let P : Set (Fin 6 → ℕ) := {p | p 0 ^^^ p 3 = p 1 ^^^ p 4 ∧ p 1 ^^^ p 4 = p 2 ^^^ p 5}
    (∀ p q, p ∈ P → CubeEdgeMove p q → q ∉ P) ∧
      ∀ p, p ∉ P → ∃ q, CubeEdgeMove p q ∧ q ∈ P
    := by
  constructor
  · rintro p q hp ⟨x, y, hxy, -, hne, hfix⟩ hq
    have untouched : ∀ x y : Fin 6, x.val % 3 ≠ y.val % 3 →
        ∃ i : Fin 6, i ≠ x ∧ i ≠ y ∧ i + 3 ≠ x ∧ i + 3 ≠ y := by decide
    obtain ⟨i, hix, hiy, hix', hiy'⟩ := untouched x y hxy
    have common : q 0 ^^^ q 3 = p 0 ^^^ p 3 := by
      calc
        q 0 ^^^ q 3 = q i ^^^ q (i + 3) := (pair_value hq i).symm
        _ = p i ^^^ p (i + 3) := by rw [hfix i hix hiy, hfix (i + 3) hix' hiy']
        _ = p 0 ^^^ p 3 := pair_value hp i
    apply hne
    funext k
    have untouched_pair : ∀ x y k : Fin 6, x.val % 3 ≠ y.val % 3 →
        (k ≠ x ∧ k ≠ y) ∨ (k + 3 ≠ x ∧ k + 3 ≠ y) := by decide
    rcases untouched_pair x y k hxy with ⟨hkx, hky⟩ | ⟨hkx, hky⟩
    · exact hfix k hkx hky
    · have hs : q k ^^^ q (k + 3) = p k ^^^ p (k + 3) :=
        (pair_value hq k).trans (common.trans (pair_value hp k).symm)
      rw [hfix (k + 3) hkx hky] at hs
      simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using
        congrArg (fun n => n ^^^ p (k + 3)) hs
  · intro p hp
    let t := min (p 0 ^^^ p 3) (min (p 1 ^^^ p 4) (p 2 ^^^ p 5))
    obtain ⟨a, A, ha, hA, hax, hkeepA, heqA⟩ :=
      reduce_pair (p 0) (p 3) t (Nat.min_le_left _ _)
    obtain ⟨b, B, hb, hB, hbx, hkeepB, heqB⟩ :=
      reduce_pair (p 1) (p 4) t ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))
    obtain ⟨c, C, hc, hC, hcx, hkeepC, heqC⟩ :=
      reduce_pair (p 2) (p 5) t ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))
    let q : Fin 6 → ℕ := ![a, b, c, A, B, C]
    have hq : q 0 ^^^ q 3 = q 1 ^^^ q 4 ∧ q 1 ^^^ q 4 = q 2 ^^^ q 5 :=
      ⟨hax.trans hbx.symm, hbx.trans hcx.symm⟩
    have hle : q ≤ p := by
      intro k
      fin_cases k <;> assumption
    have hne : q ≠ p := fun h => hp (h ▸ hq)
    let x : Fin 6 := if a = p 0 then 3 else 0
    let y : Fin 6 := if b = p 1 then 4 else 1
    let z : Fin 6 := if c = p 2 then 5 else 2
    have hx : x.val % 3 = 0 := by dsimp [x]; split <;> rfl
    have hy : y.val % 3 = 1 := by dsimp [y]; split <;> rfl
    have hz : z.val % 3 = 2 := by dsimp [z]; split <;> rfl
    have keepA : (0 ≠ x → a = p 0) ∧ (3 ≠ x → A = p 3) := by
      by_cases h : a = p 0
      · simp [x, h]
      · simp [x, h, hkeepA.resolve_left h]
    have keepB : (1 ≠ y → b = p 1) ∧ (4 ≠ y → B = p 4) := by
      by_cases h : b = p 1
      · simp [y, h]
      · simp [y, h, hkeepB.resolve_left h]
    have keepC : (2 ≠ z → c = p 2) ∧ (5 ≠ z → C = p 5) := by
      by_cases h : c = p 2
      · simp [z, h]
      · simp [z, h, hkeepC.resolve_left h]
    have hmin : t = p 0 ^^^ p 3 ∨ t = p 1 ^^^ p 4 ∨ t = p 2 ^^^ p 5 := by
      rcases min_choice (p 0 ^^^ p 3) (min (p 1 ^^^ p 4) (p 2 ^^^ p 5)) with h | h
      · exact Or.inl h
      · rcases min_choice (p 1 ^^^ p 4) (p 2 ^^^ p 5) with h' | h'
        · exact Or.inr (Or.inl (h.trans h'))
        · exact Or.inr (Or.inr (h.trans h'))
    refine ⟨q, ?_, hq⟩
    rcases hmin with ht | ht | ht
    · obtain ⟨ha', hA'⟩ := heqA ht
      refine ⟨y, z, by rw [hy, hz]; decide, hle, hne, ?_⟩
      intro k hky hkz
      fin_cases k
      · exact ha'
      · exact keepB.1 hky
      · exact keepC.1 hkz
      · exact hA'
      · exact keepB.2 hky
      · exact keepC.2 hkz
    · obtain ⟨hb', hB'⟩ := heqB ht
      refine ⟨x, z, by rw [hx, hz]; decide, hle, hne, ?_⟩
      intro k hkx hkz
      fin_cases k
      · exact keepA.1 hkx
      · exact hb'
      · exact keepC.1 hkz
      · exact keepA.2 hkx
      · exact hB'
      · exact keepC.2 hkz
    · obtain ⟨hc', hC'⟩ := heqC ht
      refine ⟨x, y, by rw [hx, hy]; decide, hle, hne, ?_⟩
      intro k hkx hky
      fin_cases k
      · exact keepA.1 hkx
      · exact keepB.1 hky
      · exact hc'
      · exact keepA.2 hkx
      · exact keepB.2 hky
      · exact hC'

end MetaMathlibExt
