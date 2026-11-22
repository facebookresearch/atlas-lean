/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Inversion sequences avoiding sets of length-3 patterns

Statements from Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*,
INTEGERS 24 (2024), Article A76.

An inversion sequence of length `n` is `e : Fin n → ℕ` with `e i ≤ i` (zero-based
`e₀ e₁ ⋯ e_{n-1}`). It contains a pattern `p : Fin 3 → ℕ` (written as a digit string, `101` is
`![1, 0, 1]`) when some subsequence `e_a e_b e_c`, `a < b < c`, is order-isomorphic to `p`.
`I_n(B)` is the set of length-`n` inversion sequences avoiding every pattern in `B`, two pattern
sets are I-Wilf-equivalent (`A ∼ B`) when `|I_n(A)| = |I_n(B)|` for all `n`, and
`F_B(x) = ∑_{n ≥ 1} |I_n(B)| xⁿ`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- The inversion sequence `e` contains the length-3 pattern `p`: some increasing triple of
positions carries values order-isomorphic to `p`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
def InvSeqContainsPattern {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) : Prop :=
  ∃ f : Fin 3 ↪o Fin n, ∀ a b, e (f a) < e (f b) ↔ p a < p b

/-- A sequence of length less than three contains no length-3 pattern.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
theorem not_invSeqContainsPattern_of_lt {n : ℕ} (hn : n < 3) (e : Fin n → ℕ)
    (p : Fin 3 → ℕ) : ¬ InvSeqContainsPattern e p := by
  rintro ⟨f, -⟩
  have := Fintype.card_le_of_embedding f.toEmbedding
  simp at this
  omega

/-- `|I_n(B)|`: the number of inversion sequences of length `n` avoiding every pattern in `B`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
noncomputable def invSeqAvoidCount (B : Set (Fin 3 → ℕ)) (n : ℕ) : ℕ :=
  Nat.card {e : Fin n → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ B, ¬ InvSeqContainsPattern e p}

/-- There is exactly one inversion sequence of length one, `0`, and it avoids every length-3
pattern.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Introduction. -/
theorem invSeqAvoidCount_one (B : Set (Fin 3 → ℕ)) : invSeqAvoidCount B 1 = 1 := by
  rw [invSeqAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e e' => Subtype.ext (funext fun i => ?_)⟩, ⟨⟨fun _ => 0, ?_⟩⟩⟩
  · have h := e.2.1 i
    have h' := e'.2.1 i
    have hi : (i : ℕ) = 0 := by omega
    omega
  · exact ⟨fun i => Nat.zero_le _, fun p _ => not_invSeqContainsPattern_of_lt (by omega) _ p⟩

/-- The paper's generating function `F_B(x) = ∑_{n ≥ 1} |I_n(B)| xⁿ` in `ℚ⟦X⟧`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Section 2. -/
noncomputable def invSeqAvoidGF (B : Set (Fin 3 → ℕ)) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (invSeqAvoidCount B n : ℚ)

/-- The coefficients of `F_B`: `[x⁰] F_B = 0` and `[x^{n+1}] F_B = |I_{n+1}(B)|`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Section 2. -/
theorem coeff_invSeqAvoidGF (B : Set (Fin 3 → ℕ)) (n : ℕ) :
    coeff 0 (invSeqAvoidGF B) = 0 ∧
      coeff (n + 1) (invSeqAvoidGF B) = (invSeqAvoidCount B (n + 1) : ℚ) := by
  simp [invSeqAvoidGF]

/-- **Theorem 4.** With `B_τ = {000, 010, 100, τ, 120}`, `B_101` and `B_110` are I-Wilf-equivalent.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 4 (`integers-2024-A76-thm-4`). -/
public theorem_wanted invSeq_wilf_000_010_100_120_101_110 :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 5.** `{000, 010, 101, 120, 201}`, `{000, 010, 101, 120, 210}` and `{000, 010, 110,
120, 210}` are I-Wilf-equivalent.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 5 (`integers-2024-A76-thm-5`). -/
public theorem_wanted invSeq_wilf_000_010_120_five_class :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 6.** For `B = {011, 102, 120}`, `F_B(x) = x(1 - x)² / (1 - 2x)²`, stated after
clearing the unit denominator `(1 - 2x)²` in `ℚ⟦X⟧`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 6 (`integers-2024-A76-thm-6`). -/
public theorem_wanted invSeqAvoidGF_011_102_120 :
    (1 - 2 * X) ^ 2 * invSeqAvoidGF ({![0, 1, 1], ![1, 0, 2], ![1, 2, 0]} : Set (Fin 3 → ℕ)) =
      X * (1 - X) ^ 2

/-- **Theorem 7.** `{000, 101, 102, 120, 201}`, `{000, 101, 102, 120, 210}` and `{000, 102, 110,
120, 210}` are I-Wilf-equivalent.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 7 (`integers-2024-A76-thm-7`). -/
public theorem_wanted invSeq_wilf_000_102_120_five_class :
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 8.** With `A_τ = {000, 100, 101, 120, τ}` and `B_τ = {000, 100, 110, 120, τ}`, `A_201
∼ A_210` and `B_201 ∼ B_210` (I-Wilf-equivalence).

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 8 (`integers-2024-A76-thm-8`). -/
public theorem_wanted invSeq_wilf_000_100_120_201_210 :
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 9.** (1) With `A_τ = {010, τ, 102, 120, 201}`, `A_100 ∼ A_110`. (2) With `A_τ = {010,
τ, 102, 120, 210}` and `B = {010, 101, 102, 120, 201}`, `A_100 ∼ A_101 ∼ A_110 ∼ B`
(I-Wilf-equivalence).

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 9 (`integers-2024-A76-thm-9`). -/
public theorem_wanted invSeq_wilf_010_102_120_five_classes :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 11.** With `A_τ = {010, 100, 101, 120, τ}`, `A_201` and `A_210` are I-Wilf-equivalent.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 11 (`integers-2024-A76-thm-11`). -/
public theorem_wanted invSeq_wilf_010_100_101_120_201_210 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 13.** With `A_τ = {000, 010, 100, 101, 120, τ}`, `B_τ = {000, 010, 100, 110, 120, τ}`
and `C = {000, 010, 101, 110, 120, 201}`, `A_201 ∼ A_210 ∼ B_201 ∼ B_210 ∼ C` (I-Wilf-equivalence).

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 13 (`integers-2024-A76-thm-13`). -/
public theorem_wanted invSeq_wilf_000_010_120_six_class :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 14.** With `A_τ = {011, 101, 102, 110, 120, τ}` and `B = {011, 021, 102, 110, 201,
210}`, `A_201 ∼ A_210 ∼ B` (I-Wilf-equivalence).

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 14 (`integers-2024-A76-thm-14`). -/
public theorem_wanted invSeq_wilf_102_110_six_class :
    invSeqAvoidCount ({![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 1], ![0, 2, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 16.** For each of the three sets `B` below,
`F_B(x) = x/(1 - x) + x²(1 - x)/(1 - 2x)²`, stated after clearing the unit denominator
`(1 - x)(1 - 2x)²` in `ℚ⟦X⟧`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 16 (`integers-2024-A76-thm-16`). -/
public theorem_wanted invSeqAvoidGF_010_011_102_201_210_seven :
    ∀ B : Set (Fin 3 → ℕ),
      (B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]} ∨
        B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]} ∨
        B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}) →
      (1 - X) * (1 - 2 * X) ^ 2 * invSeqAvoidGF B =
        X * (1 - 2 * X) ^ 2 + X ^ 2 * (1 - X) ^ 2

/-- **Theorem 17.** With `B_τ = {000, 010, 100, 101, 102, 110, 120, τ}`, `B_201 ∼ B_210`, and
`F_{B_201}(x) = (1 - x² - 4x³ - 7x⁴ - 5x⁵ - 2x⁶ - (1 + x + 2x² + 2x³ + x⁴) √(1 - 2x - 3x²)) /
(2x³ (1 + x)(x² + 2x + 2))`, stated after clearing the denominator.
`s` is the power series square root of `1 - 2x - 3x²` with constant term `1`; the record's
radical `√(1 - 2x - 3x²)` multiplies the polynomial printed just before it.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 17 (`integers-2024-A76-thm-17`). -/
public theorem_wanted invSeq_wilf_eight_201_210_and_gf :
    invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
        ![1, 2, 0], ![2, 0, 1]} : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
        ![1, 2, 0], ![2, 1, 0]} : Set (Fin 3 → ℕ)) ∧
    ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
      2 * X ^ 3 * (1 + X) * (X ^ 2 + 2 * X + 2) *
          invSeqAvoidGF ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
            ![1, 2, 0], ![2, 0, 1]} : Set (Fin 3 → ℕ)) =
        1 - X ^ 2 - 4 * X ^ 3 - 7 * X ^ 4 - 5 * X ^ 5 - 2 * X ^ 6 -
          (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * s

/-- **Theorem 18.** For `B₁ = {000, 010, 100, 101, 102, 120, 201, 210}`,
`B₂ = {000, 010, 100, 102, 110, 120, 201, 210}` and `B₃ = {000, 010, 101, 102, 110, 120, 201, 210}`,
`F_{B_j}(x) = (1 - 2x - x² + x³ - (1 - x) √(1 - 2x - 3x²)) / x²`, stated after clearing `x²`;
`s` is the power series square root of `1 - 2x - 3x²` with constant term `1` (the record's
radical `√(1 - 2x - 3x²)` multiplies the polynomial printed just before it).

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 18 (`integers-2024-A76-thm-18`). -/
public theorem_wanted invSeqAvoidGF_eight_radical_three :
    ∀ B : Set (Fin 3 → ℕ),
      (B = {![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1],
          ![2, 1, 0]} ∨
        B = {![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1],
          ![2, 1, 0]} ∨
        B = {![0, 0, 0], ![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1],
          ![2, 1, 0]}) →
      ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
        X ^ 2 * invSeqAvoidGF B = 1 - 2 * X - X ^ 2 + X ^ 3 - (1 - X) * s

/-- **Theorem 21.** For `B = {000, 100, 101, 102, 110, 120, 201, 210}`,
`F_B(x) = (2 - 2x - 5x² - x³ - (2 - x²) √(1 - 2x - 3x²)) / (2x² (1 + x))`, stated after clearing
the denominator.
`s` is the power series square root of `1 - 2x - 3x²` with constant term `1`; the record's
radical `√(1 - 2x - 3x²)` multiplies the polynomial printed just before it.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 21 (`integers-2024-A76-thm-21`). -/
public theorem_wanted invSeqAvoidGF_000_100_101_102_110_120_201_210 :
    ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
      2 * X ^ 2 * (1 + X) *
          invSeqAvoidGF ({![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0],
            ![2, 0, 1], ![2, 1, 0]} : Set (Fin 3 → ℕ)) =
        2 - 2 * X - 5 * X ^ 2 - X ^ 3 - (2 - X ^ 2) * s

/-- **Theorem 22.** For the nine patterns `B = {000, 010, 100, 101, 102, 110, 120, 201, 210}`,
`F_B(x) = (2 - 3x - 3x² + (x - 2) √(1 - 2x - 3x²)) / (2x² (1 + x))`, stated after clearing the
denominator.
`s` is the power series square root of `1 - 2x - 3x²` with constant term `1`; the record's
radical `√(1 - 2x - 3x²)` multiplies the polynomial printed just before it.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 22 (`integers-2024-A76-thm-22`). -/
public theorem_wanted invSeqAvoidGF_nine_patterns :
    ∀ s : ℚ⟦X⟧, constantCoeff s = 1 → s ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
      2 * X ^ 2 * (1 + X) *
          invSeqAvoidGF ({![0, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
            ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]} : Set (Fin 3 → ℕ)) =
        2 - 3 * X - 3 * X ^ 2 + (X - 2) * s

/-- **Theorem 1.** Let `w_d` be the number of I-Wilf-equivalence classes of sets of `d` of the
thirteen length-3 patterns `000, 001, 010, 011, 012, 021, 100, 101, 102, 110, 120, 201, 210`,
i.e. the number of distinct counting sequences `n ↦ |I_n(B)|` over the `d`-element sets `B`. Then
`w₅ = 219`, `w₆ = 167`, `w₇ = 105`, `w₈ = 61`, `w₉ = 35`, `w₁₀ = 21`, `w₁₁ = 10`, `w₁₂ = 4`, and
`w₁₃ = 1`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 1 (`integers-2024-A76-thm-1`). -/
public theorem_wanted invSeq_wilfClassCount :
    let P : Finset (Fin 3 → ℕ) := {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2],
      ![0, 2, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1],
      ![2, 1, 0]}
    let w : ℕ → ℕ := fun d =>
      Nat.card ↥((fun B : Finset (Fin 3 → ℕ) => invSeqAvoidCount (B : Set (Fin 3 → ℕ))) ''
        (P.powersetCard d : Set (Finset (Fin 3 → ℕ))))
    w 5 = 219 ∧ w 6 = 167 ∧ w 7 = 105 ∧ w 8 = 61 ∧ w 9 = 35 ∧ w 10 = 21 ∧ w 11 = 10 ∧
      w 12 = 4 ∧ w 13 = 1

/-- **Theorem 2** (reductions, quoted from [4]): for each listed pair `(C, τ)`, `C ∪ {τ}` reduces to
`C` (`C ∪ {τ} ∼ʳ C`), i.e. `I_n(C ∪ {τ}) = I_n(C)` for all `n`: every inversion sequence
avoiding `C` avoids `τ`. The pairs are the record's bullets, one pair per listed `τ`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 2 (`integers-2024-A76-thm-2`). -/
public theorem_wanted invSeq_reducible_pattern_sets :
    ∀ Cτ ∈ ([(({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 0, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 2, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 2, 1]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 0, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 0, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 0, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 0, 1], ![0, 1, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![0, 2, 1]),
        (({![0, 0, 1], ![1, 1, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![1, 2, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 1, 0], ![0, 1, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 1, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 0], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 0, 1]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 0]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 1]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 0, 2]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 1, 0]),
        (({![0, 1, 0], ![0, 2, 1]} : Set (Fin 3 → ℕ)), ![1, 2, 0]),
        (({![0, 0, 1], ![0, 1, 1], ![0, 1, 2]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 1], ![1, 0, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0]),
        (({![0, 0, 1], ![0, 1, 2], ![1, 0, 0]} : Set (Fin 3 → ℕ)), ![2, 1, 0])]
      : List (Set (Fin 3 → ℕ) × (Fin 3 → ℕ))),
      ∀ (n : ℕ) (e : Fin n → ℕ), (∀ i, e i ≤ i) → (∀ p ∈ Cτ.1, ¬ InvSeqContainsPattern e p) →
        ¬ InvSeqContainsPattern e Cτ.2

/-- **Theorem 3.** For `B = {010, 101, 102, 201, 210}` and `C = {011, 101, 110, 201, 210}`,
`F_B(x) = F_C(x) = x / ((1 - x)(2 - (1 - √(1 - 4x))/(2x)))`. Here `(1 - √(1 - 4x))/(2x)` is the
Catalan generating function `∑ Cₙ xⁿ` (Mathlib's `catalan`), and the identity is stated after
clearing the unit denominator `(1 - x)(2 - ∑ Cₙ xⁿ)` in `ℚ⟦X⟧`.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 3 (`integers-2024-A76-thm-3`). -/
public theorem_wanted invSeqAvoidGF_010_101_102_201_210_catalan :
    invSeqAvoidGF ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]} : Set (Fin 3 → ℕ)) =
        invSeqAvoidGF ({![0, 1, 1], ![1, 0, 1], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}
            : Set (Fin 3 → ℕ)) ∧
      (1 - X) * (2 - PowerSeries.mk fun n => (catalan n : ℚ)) *
          invSeqAvoidGF ({![0, 1, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]}
              : Set (Fin 3 → ℕ)) = X

/-- **Theorem 10**, parts `B` and `C`: with `B_τ = {100, τ, 102, 120, 210}` and
`C_τ = {τ, 102, 120, 201, 210}`, `B_101 ∼ B_110` and `C_101 ∼ C_110`. Partial: the first part
`A_101 ∼ A_110` with `A_τ = {100, τ, 102, 120, 201}` is false as printed
(`|I_6(A_101)| = 206 ≠ 205 = |I_6(A_110)|`) and is omitted.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 10 (`integers-2024-A76-thm-10`). -/
public theorem_wanted invSeq_wilf_102_120_101_110_parts_B_C :
    invSeqAvoidCount ({![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![1, 0, 0], ![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)) ∧
    invSeqAvoidCount ({![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![1, 1, 0], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 12**, part `A`: with `A_τ = {010, τ, 120, 201, 210}`, `A_101 ∼ A_110`. Partial: the
second part `B_101 ∼ B_110` with `B_τ = {100, τ, 120, 201, 210}` is false as printed
(`|I_5(B_101)| = 79 ≠ 81 = |I_5(B_110)|`) and is omitted.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 12 (`integers-2024-A76-thm-12`). -/
public theorem_wanted invSeq_wilf_010_120_201_210_101_110 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 1, 0], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

/-- **Theorem 15**, first equivalence: with `A_τ = {010, 100, 101, 102, 120, τ}`,
`A_201 ∼ A_210`. Partial: the further claims `A_210 ∼ B ∼ C` with
`B = {010, 100, 110, 102, 120, 201}` and `C = {010, 101, 110, 102, 120, 210}` are false as printed
(`|I_7| = 538, 537, 539` for `A_210, B, C`) and are omitted.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 15 (`integers-2024-A76-thm-15`). -/
public theorem_wanted invSeq_wilf_010_100_101_102_120_201_210 :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
        : Set (Fin 3 → ℕ)) =
      invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ))

end

end MetaMathlibExt
