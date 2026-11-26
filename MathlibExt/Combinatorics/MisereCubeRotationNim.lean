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
# Misère rotation Nim on a cube

`cubeRotationNim_misere_pPositions` classifies the misère P-positions using the totals on
the three pairs of opposite faces.
-/

namespace MetaMathlibExt

namespace cubeRotationNim_misere_pPositions

private abbrev Heaps := ℕ × ℕ × ℕ

private def heaps (p : Fin 6 → ℕ) : Heaps :=
  (p 0 + p 3, p 1 + p 4, p 2 + p 5)

private def total (s : Heaps) : ℕ := s.1 + s.2.1 + s.2.2

-- A rotation can reduce any two heaps and must leave one heap untouched.
private def Reduces (s t : Heaps) : Prop :=
  t ≤ s ∧ total t < total s ∧ (t.1 = s.1 ∨ t.2.1 = s.2.1 ∨ t.2.2 = s.2.2)

private def Losing (s : Heaps) : Prop :=
  total s = 1 ∨ (2 ≤ s.1 ∧ s.1 = s.2.1 ∧ s.2.1 = s.2.2)

private theorem move_iff {p q : Fin 6 → ℕ} :
    CubeRotationMove p q ↔ q ≤ p ∧ q ≠ p ∧
      ((q 0 = p 0 ∧ q 3 = p 3) ∨ (q 1 = p 1 ∧ q 4 = p 4) ∨ (q 2 = p 2 ∧ q 5 = p 5)) := by
  constructor
  · rintro ⟨i, j, hij, hle, hne, hfix⟩
    refine ⟨hle, hne, ?_⟩
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; right
      constructor <;> apply hfix <;> decide
    · right; left
      constructor <;> apply hfix <;> decide
    · left
      constructor <;> apply hfix <;> decide
  · rintro ⟨hle, hne, hfix⟩
    rcases hfix with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    case' inl => refine ⟨1, 2, by decide, hle, hne, ?_⟩
    case' inr.inl => refine ⟨0, 2, by decide, hle, hne, ?_⟩
    case' inr.inr => refine ⟨0, 1, by decide, hle, hne, ?_⟩
    all_goals
      intro k hi hj hi' hj'
      fin_cases k <;> first | assumption | contradiction

private theorem reduces_of_move {p q : Fin 6 → ℕ} (hm : CubeRotationMove p q) :
    Reduces (heaps p) (heaps q) := by
  obtain ⟨hle, hne, hfix⟩ := move_iff.mp hm
  have hlt : total (heaps q) < total (heaps p) := by
    by_contra! h
    apply hne
    dsimp [total, heaps] at h
    change ∀ k, q k ≤ p k at hle
    rw [funext_iff]
    simp [Fin.forall_fin_succ] at hle ⊢
    omega
  refine ⟨⟨Nat.add_le_add (hle 0) (hle 3), Nat.add_le_add (hle 1) (hle 4),
    Nat.add_le_add (hle 2) (hle 5)⟩, hlt, ?_⟩
  dsimp [heaps]
  omega

-- To leave n tokens on a pair, keep as many as possible on its first face.
private theorem lift_move {p : Fin 6 → ℕ} {t : Heaps} (hm : Reduces (heaps p) t) :
    ∃ q, CubeRotationMove p q ∧ heaps q = t := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨⟨ha, hb, hc⟩, hlt, hfix⟩ := hm
  dsimp [heaps] at ha hb hc hfix
  let q : Fin 6 → ℕ := ![min (p 0) a, min (p 1) b, min (p 2) c, a - p 0, b - p 1, c - p 2]
  have hq : heaps q = (a, b, c) := by
    dsimp [heaps, q]
    congr 2 <;> omega
  refine ⟨q, move_iff.mpr ⟨?_, ?_, ?_⟩, hq⟩
  · intro k
    fin_cases k <;> dsimp [q] <;> omega
  · intro heq
    rw [← hq, heq] at hlt
    exact (Nat.lt_irrefl _) hlt
  · dsimp [q]
    omega

private theorem losing_no_move {s t : Heaps} (hs : Losing s) (hm : Reduces s t) : ¬ Losing t := by
  obtain ⟨⟨ha, hb, hc⟩, hlt, hfix⟩ := hm
  dsimp [Losing, total] at *
  omega

private theorem exists_reduction {s : Heaps} (hs : Losing s) : ∃ t, Reduces s t := by
  obtain ⟨a, b, c⟩ := s
  by_cases ha : a = 0
  · refine ⟨(a, 0, 0), ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩, ?_, Or.inl rfl⟩
    dsimp [Losing, total] at *
    omega
  · exact ⟨(0, b, c), ⟨Nat.zero_le _, le_rfl, le_rfl⟩, by dsimp [total]; omega,
      Or.inr (Or.inl rfl)⟩

private theorem move_to_losing {s : Heaps} (hne : 0 < total s) (hs : ¬ Losing s) :
    ∃ t, Reduces s t ∧ Losing t := by
  obtain ⟨a, b, c⟩ := s
  let m := min a (min b c)
  by_cases h : m < 2
  · -- Preserve a heap of size one, or preserve an empty heap and trim the others to one token.
    suffices Reduces (a, b, c) (1, 0, 0) ∨ Reduces (a, b, c) (0, 1, 0) ∨
        Reduces (a, b, c) (0, 0, 1) by
      rcases this with hm | hm | hm <;> exact ⟨_, hm, Or.inl rfl⟩
    simp only [Reduces, Prod.le_def, total, Losing, m] at *
    omega
  · -- Trim the other two heaps to the minimum.
    refine ⟨(m, m, m), ?_, Or.inr ⟨by omega, rfl, rfl⟩⟩
    simp only [Reduces, Prod.le_def, total, Losing, m] at *
    omega

private theorem classification (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeRotationMove p q) ∧ ∀ q, CubeRotationMove p q → q ∉ P)
    (p : Fin 6 → ℕ) : p ∈ P ↔ Losing (heaps p) := by
  have ih (q) (hm : CubeRotationMove p q) : q ∈ P ↔ Losing (heaps q) :=
    classification P hP q
  constructor
  · intro hp
    obtain ⟨⟨q, hm⟩, hout⟩ := (hP p).mp hp
    by_contra hs
    obtain ⟨t, ht, htlose⟩ :=
      move_to_losing (Nat.zero_lt_of_lt (reduces_of_move hm).2.1) hs
    obtain ⟨r, hr, rfl⟩ := lift_move ht
    exact hout r hr ((ih r hr).mpr htlose)
  · intro hs
    apply (hP p).mpr
    obtain ⟨t, ht⟩ := exists_reduction hs
    obtain ⟨q, hq, -⟩ := lift_move ht
    exact ⟨⟨q, hq⟩, fun r hr hmem => losing_no_move hs (reduces_of_move hr) ((ih r hr).mp hmem)⟩
termination_by total (heaps p)
decreasing_by exact (reduces_of_move hm).2.1

end cubeRotationNim_misere_pPositions

open cubeRotationNim_misere_pPositions in
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
public theorem cubeRotationNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeRotationMove p q) ∧ ∀ q, CubeRotationMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 + p 3 = p 1 + p 4 ∧ p 1 + p 4 = p 2 + p 5) ∨
      p = ![0, 0, 0, 0, 0, 1] ∨ p = ![1, 1, 1, 1, 1, 1] := by
  rw [classification P hP]
  simp [Fin.forall_fin_succ] at hC
  dsimp [Losing, heaps, total]
  constructor
  · rintro (hsingle | hequal)
    · right; left
      funext k
      fin_cases k <;> dsimp <;> omega
    · by_cases h : 2 ≤ p 5
      · exact Or.inl ⟨h, hequal.2⟩
      · right; right
        funext k
        fin_cases k <;> dsimp <;> omega
  · rintro (⟨h, hab', hbc⟩ | rfl | rfl)
    · right
      omega
    · decide
    · decide

end MetaMathlibExt
