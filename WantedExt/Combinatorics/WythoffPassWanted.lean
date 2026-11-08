/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- Grundy numbers of Wythoff's game (a Queen moving left, down, or diagonally down-left on the
quarter plane, positions `(x, y)`) augmented by a third coordinate `p` and one extra move from
`(x, y, true)` to `(x, y, false)`. With `strict = true` the extra move is the one-time pass of
Wythoff's game with a pass, unavailable at the terminal position `x + y = 0`; with
`strict = false` it is the move in an added pile of one stone (always available while
`p = true`). The value is the mex (least natural number not attained) of the Grundy numbers of
the positions reachable in one move. With `p = false` both games are classical Wythoff's game.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (the move sets `M₁, M₂, M₃, M₄, M₄'` and the
Grundy numbers `𝒢₁`, `𝒢₂`). -/
noncomputable def wythoffExtraMoveGrundy (strict : Bool) : ℕ → ℕ → Bool → ℕ
  | x, y, p =>
    sInf {m | (∀ u, u < x → wythoffExtraMoveGrundy strict u y p ≠ m) ∧
      (∀ v, v < y → wythoffExtraMoveGrundy strict x v p ≠ m) ∧
      (∀ t, 1 ≤ t → t ≤ x → t ≤ y → wythoffExtraMoveGrundy strict (x - t) (y - t) p ≠ m) ∧
      (p = true → (strict = false ∨ 0 < x + y) →
        wythoffExtraMoveGrundy strict x y false ≠ m)}
termination_by x y p => 2 * (x + y) + p.toNat
decreasing_by
  all_goals first
    | omega
    | (subst_vars; simp only [Bool.toNat_true, Bool.toNat_false]; omega)

/-- `𝒢₁(x, y, p)`: Grundy numbers of Wythoff's game with a one-time pass; `p = true` means the
pass is still available.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (Grundy numbers `𝒢₁`). -/
noncomputable abbrev wythoffPassGrundy (x y : ℕ) (p : Bool) : ℕ :=
  wythoffExtraMoveGrundy true x y p

/-- `𝒢₂(x, y, p)`: Grundy numbers of the sum of Wythoff's game and a pile of `p` stones
(`p = true`: one stone).

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (Grundy numbers `𝒢₂`). -/
noncomputable abbrev wythoffPlusStoneGrundy (x y : ℕ) (p : Bool) : ℕ :=
  wythoffExtraMoveGrundy false x y p

/-- The set `A` of the positions `(x, y, 0)` listed in the paper (third coordinate dropped).

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4 (the set `A`, Definition 12). -/
def wythoffPassSetA : Finset (ℕ × ℕ) :=
  {(0, 0), (1, 2), (2, 1), (3, 5), (4, 7), (5, 3), (7, 4)}

/-- The set `B` of the positions `(x, y, 1)` listed in the paper (third coordinate dropped).

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4 (the set `B`). -/
def wythoffPassSetB : Finset (ℕ × ℕ) :=
  {(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)}

/-- The set `C` of the positions `(x, y, 1)` listed in the paper (third coordinate dropped).

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4 (the set `C`). -/
def wythoffPassSetC : Finset (ℕ × ℕ) :=
  {(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)}

/-- The defining mex recursion of `wythoffExtraMoveGrundy`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 1 (Grundy numbers as mex over moves). -/
theorem wythoffExtraMoveGrundy_eq (strict : Bool) (x y : ℕ) (p : Bool) :
    wythoffExtraMoveGrundy strict x y p =
      sInf {m | (∀ u, u < x → wythoffExtraMoveGrundy strict u y p ≠ m) ∧
        (∀ v, v < y → wythoffExtraMoveGrundy strict x v p ≠ m) ∧
        (∀ t, 1 ≤ t → t ≤ x → t ≤ y →
          wythoffExtraMoveGrundy strict (x - t) (y - t) p ≠ m) ∧
        (p = true → (strict = false ∨ 0 < x + y) →
          wythoffExtraMoveGrundy strict x y false ≠ m)} := by
  rw [wythoffExtraMoveGrundy]

/-- The terminal position `(0, 0)` has Grundy number `0` in Wythoff's game with a pass, with or
without the pass available (the pass is not allowed from a terminal position).

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (`M₄(x, y, p) = ∅` if `x + y = 0`). -/
theorem wythoffPassGrundy_zero_zero (p : Bool) : wythoffPassGrundy 0 0 p = 0 := by
  rw [wythoffPassGrundy, wythoffExtraMoveGrundy_eq]
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  refine ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun v hv => absurd hv (Nat.not_lt_zero v),
    fun t h1 h2 _ => by omega, fun _ h => by simp at h⟩

/-- With a pile of one stone added, `(0, 0, 1)` has Grundy number `1`: its only move is to the
terminal position `(0, 0, 0)`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (`M₄'(x, y, 1) = {(x, y, 0)}`). -/
theorem wythoffPlusStoneGrundy_zero_zero_true : wythoffPlusStoneGrundy 0 0 true = 1 := by
  have h0 : wythoffPlusStoneGrundy 0 0 false = 0 := by
    rw [wythoffPlusStoneGrundy, wythoffExtraMoveGrundy_eq]
    refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
    refine ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun v hv => absurd hv (Nat.not_lt_zero v),
      fun t h1 h2 _ => by omega, fun h => by simp at h⟩
  rw [wythoffPlusStoneGrundy] at h0 ⊢
  rw [wythoffExtraMoveGrundy_eq]
  have h1 : (1 : ℕ) ∈ {m | (∀ u, u < 0 → wythoffExtraMoveGrundy false u 0 true ≠ m) ∧
      (∀ v, v < 0 → wythoffExtraMoveGrundy false 0 v true ≠ m) ∧
      (∀ t, 1 ≤ t → t ≤ 0 → t ≤ 0 →
        wythoffExtraMoveGrundy false (0 - t) (0 - t) true ≠ m) ∧
      (true = true → (false = false ∨ 0 < 0 + 0) →
        wythoffExtraMoveGrundy false 0 0 false ≠ m)} :=
    ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun v hv => absurd hv (Nat.not_lt_zero v),
      fun t h1 h2 _ => by omega, fun _ _ => by rw [h0]; omega⟩
  apply le_antisymm (Nat.sInf_le h1)
  refine le_csInf ⟨1, h1⟩ fun m hm => ?_
  have := hm.2.2.2 rfl (Or.inl rfl)
  rw [h0] at this
  omega

/-- `B` and `C` have nine elements each.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4. -/
theorem wythoffPassSetB_card_wythoffPassSetC_card :
    wythoffPassSetB.card = 9 ∧ wythoffPassSetC.card = 9 := by
  decide

/-- `A` has seven elements.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4. -/
theorem wythoffPassSetA_card : wythoffPassSetA.card = 7 := by
  decide

/-- Wythoff's theorem: the positions of classical Wythoff's game with Grundy number `0`
(the P-positions) are exactly `(⌊nφ⌋, ⌊nφ⌋ + n)` and `(⌊nφ⌋ + n, ⌊nφ⌋)` for `n ≥ 0`, where
`φ = (1 + √5)/2`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 2 (`integers-2025-G4-thm-2`), quoting Wythoff. -/
public theorem_wanted wythoffGrundy_eq_zero_iff (x y : ℕ) :
    wythoffPassGrundy x y false = 0 ↔
      ∃ n : ℕ, (x = ⌊(n : ℝ) * Real.goldenRatio⌋₊ ∧ y = ⌊(n : ℝ) * Real.goldenRatio⌋₊ + n) ∨
        (x = ⌊(n : ℝ) * Real.goldenRatio⌋₊ + n ∧ y = ⌊(n : ℝ) * Real.goldenRatio⌋₊)

/-- Every position with Grundy number `1` in classical Wythoff's game lies within Euclidean
distance `√20` of a position with Grundy number `0` (a P-position).

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Corollary 1 (`integers-2025-G4-cor-1`). -/
public theorem_wanted wythoffGrundy_one_near_zero (x y : ℕ)
    (h : wythoffPassGrundy x y false = 1) :
    ∃ v w : ℕ, wythoffPassGrundy v w false = 0 ∧
      ((x : ℤ) - v) ^ 2 + ((y : ℤ) - w) ^ 2 ≤ 20

/-- The P-positions (Grundy number `0`) with `x, y ≤ 8`: (i) without the pass they are the set
`A`; (ii) with the pass available they are the set `B`; (iii) in the sum of Wythoff's game and a
pile of one stone, with the stone present, they are the set `C`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Lemma 1 (`integers-2025-G4-lem-1`). -/
public theorem_wanted wythoffPass_pPositions_le_eight (x y : ℕ) (hx : x ≤ 8) (hy : y ≤ 8) :
    (wythoffPassGrundy x y false = 0 ↔ (x, y) ∈ wythoffPassSetA) ∧
      (wythoffPassGrundy x y true = 0 ↔ (x, y) ∈ wythoffPassSetB) ∧
      (wythoffPlusStoneGrundy x y true = 0 ↔ (x, y) ∈ wythoffPassSetC)

/-- For `x ≥ 9` or `y ≥ 9`: (i) if `y ≤ 8`, horizontal moves from `(x, y, 1)` reach both `B`
and `C` and vertical moves reach neither; (ii) symmetrically if `x ≤ 8`; (iii) if
`x ≤ y + 4` and `y ≤ x + 4`, diagonal moves reach both `B` and `C`; (iv) if `x ≥ y + 5` or
`y ≥ x + 5`, diagonal moves reach neither.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Lemma 2 (`integers-2025-G4-lem-2`). -/
public theorem_wanted wythoffPass_moves_meet_setB_setC (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    (y ≤ 8 →
      (∃ u < x, (u, y) ∈ wythoffPassSetB) ∧ (∃ u < x, (u, y) ∈ wythoffPassSetC) ∧
        (∀ v < y, (x, v) ∉ wythoffPassSetC) ∧ (∀ v < y, (x, v) ∉ wythoffPassSetB)) ∧
    (x ≤ 8 →
      (∃ v < y, (x, v) ∈ wythoffPassSetB) ∧ (∃ v < y, (x, v) ∈ wythoffPassSetC) ∧
        (∀ u < x, (u, y) ∉ wythoffPassSetC) ∧ (∀ u < x, (u, y) ∉ wythoffPassSetB)) ∧
    (x ≤ y + 4 → y ≤ x + 4 →
      (∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetB) ∧
        (∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetC)) ∧
    (y + 5 ≤ x ∨ x + 5 ≤ y →
      (∀ t, 1 ≤ t → t ≤ x → t ≤ y → (x - t, y - t) ∉ wythoffPassSetB) ∧
        (∀ t, 1 ≤ t → t ≤ x → t ≤ y → (x - t, y - t) ∉ wythoffPassSetC))

/-- For `x ≥ 9` or `y ≥ 9`, each of the horizontal, vertical, and diagonal move sets of
`(x, y, 1)` meets `B` if and only if it meets `C`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Lemma 3 (`integers-2025-G4-lem-3`). -/
public theorem_wanted wythoffPass_moves_meet_setB_iff_setC (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    ((∃ u < x, (u, y) ∈ wythoffPassSetB) ↔ ∃ u < x, (u, y) ∈ wythoffPassSetC) ∧
    ((∃ v < y, (x, v) ∈ wythoffPassSetB) ↔ ∃ v < y, (x, v) ∈ wythoffPassSetC) ∧
    ((∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetB) ↔
      ∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetC)

/-- For `x ≥ 9` or `y ≥ 9`, `𝒢₁(x, y, 1) = 0` if and only if `𝒢₂(x, y, 1) = 0`: away from
the `9 × 9` corner, Wythoff's game with an available pass has the same P-positions as
Wythoff's game plus a pile of one stone.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 4 (`integers-2025-G4-thm-4`). -/
public theorem_wanted wythoffPassGrundy_eq_zero_iff_plusStone (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    wythoffPassGrundy x y true = 0 ↔ wythoffPlusStoneGrundy x y true = 0

/-- For `x ≥ 9` or `y ≥ 9`, `𝒢₁(x, y, 1) = 0` if and only if `𝒢₁(x, y, 0) = 1`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Corollary 2 (`integers-2025-G4-cor-2`). -/
public theorem_wanted wythoffPassGrundy_true_eq_zero_iff (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    wythoffPassGrundy x y true = 0 ↔ wythoffPassGrundy x y false = 1

/-- Every position `(x, y, 1)` with `𝒢₁(x, y, 1) = 0` lies within Euclidean distance `√20` of
some `(v, w)` with `𝒢₁(v, w, 0) = 0`.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 5 (`integers-2025-G4-thm-5`). -/
public theorem_wanted wythoffPass_pPosition_near_wythoff_pPosition (x y : ℕ)
    (h : wythoffPassGrundy x y true = 0) :
    ∃ v w : ℕ, wythoffPassGrundy v w false = 0 ∧
      ((x : ℤ) - v) ^ 2 + ((y : ℤ) - w) ^ 2 ≤ 20

end

end MetaMathlibExt
