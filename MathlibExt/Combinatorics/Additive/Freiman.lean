/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Additive.BalogSzemerediGowers
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Freiman's theorem

Freiman's theorem used in §7 of Gowers's proof of Szemerédi's theorem (`freiman`): a nonempty
finite set of integers `A` with `|A + A| ≤ C|A|` lies in a generalized arithmetic progression
whose dimension and size, relative to `|A|`, are bounded in terms of `C` alone.
This module also re-exports the Balog–Szemerédi–Gowers theorem.

Source: [G01] W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11 (2001)
465–588; numbering of the author's preprint `sz898.dvi`,
https://www.dpmms.cam.ac.uk/~wtg10/papers.html (journal numbering not checked).

## Proof

The proof follows Ruzsa's argument, which [G01] cites for Theorem 7.1.

1. The Plünnecke–Ruzsa inequality (Mathlib) bounds every `|mA - nA|` by `C ^ (m + n) |A|`.
2. Modelling (`modelling`): a subset `A'` of `A` with `|A| ≤ 8|A'|` is Freiman isomorphic of
   order `8` to a subset `B` of `ZMod N`, where `N ≤ 4|8A - 8A|`.
3. Bogolyubov's lemma (`bogolyubov`): `2B - 2B` contains the Bohr set of radius `1/4` of a
   set of at most `(N / |B|)²` frequencies.
4. Bohr sets contain large proper progressions (`bohr_progression`). Instead of Minkowski's
   second theorem we add one frequency at a time (`double_progression`): each coordinate of
   the current proper progression is restricted by a rank-one Bohr condition, and such a set
   contains a proper two-dimensional progression of proportional size, found by reducing a
   two-dimensional integer lattice (`rankOne_progression`). The dimension doubles at each step.
5. The progression pulls back through the Freiman isomorphism to a proper progression
   `P ⊆ 2A - 2A` with `|P| ≥ c(C)|A|` (`pullback`).
6. Ruzsa's covering lemma (Mathlib) covers `A` by boundedly many translates of `P - P`, which
   lie in one progression of the required dimension and size (`freiman_format`).
-/

open scoped Pointwise
open Finset

namespace MathlibExt.Combinatorics.Additive.FreimanBSGWanted

/-! ## A rank-one Bohr set in an interval contains a large proper two-dimensional progression -/

/-- For `A ≥ 0` and `B > 0` there is a largest natural number `S` with `4 S² B ≤ A`. -/
private lemma r1_exists_nat (A B : ℤ) (hA : 0 ≤ A) (hB : 0 < B) :
    ∃ S : ℕ, 4 * (S : ℤ) ^ 2 * B ≤ A ∧ A < 4 * ((S : ℤ) + 1) ^ 2 * B := by
  have hex : ∃ m : ℕ, A < 4 * ((m : ℤ) + 1) ^ 2 * B :=
    ⟨A.toNat, by rw [Int.toNat_of_nonneg hA]; nlinarith⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | m
  · simpa using hA
  · have hm := not_lt.mp (Nat.find_min hex (show m < Nat.find hex by omega))
    exact_mod_cast hm

/-- If `|2 B| ≤ Q₁` and `|2 B| ≤ Q₂`, then `4 B² ≤ Q₁ Q₂`. -/
private lemma r1_four_sq_le {Q₁ Q₂ B : ℤ} (h₁ : 0 ≤ Q₁ + 2 * B) (h₂ : 0 ≤ Q₁ - 2 * B)
    (h₃ : 0 ≤ Q₂ + 2 * B) (h₄ : 0 ≤ Q₂ - 2 * B) : 4 * B ^ 2 ≤ Q₁ * Q₂ := by
  nlinarith [mul_nonneg h₁ h₄, mul_nonneg h₂ h₃]

/-- A reduced basis of the lattice `{(q, q * s - k * n) | q k : ℤ}`. Write
`bᵢ = (qᵢ, qᵢ * s - kᵢ * n)`, `Q(q, y) = t² q² + l² y²` and `B` for the associated bilinear form.
A pair `(b₁, b₂)` with unimodular coefficient matrix minimizing `Q(b₁) + Q(b₂)` satisfies
`|2 B(b₁, b₂)| ≤ Q(b₁)` and `|2 B(b₁, b₂)| ≤ Q(b₂)`, hence `4 B(b₁, b₂)² ≤ Q(b₁) Q(b₂)`. -/
private lemma r1_reduced_basis (t l n s : ℤ) :
    ∃ q₁ k₁ q₂ k₂ : ℤ, q₂ * k₁ - q₁ * k₂ = 1 ∧
      4 * (t ^ 2 * q₁ * q₂ + l ^ 2 * (q₁ * s - k₁ * n) * (q₂ * s - k₂ * n)) ^ 2 ≤
        (t ^ 2 * q₁ ^ 2 + l ^ 2 * (q₁ * s - k₁ * n) ^ 2) *
          (t ^ 2 * q₂ ^ 2 + l ^ 2 * (q₂ * s - k₂ * n) ^ 2) := by
  obtain ⟨m, ⟨q₁, k₁, q₂, k₂, hdet, rfl⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun m => ∃ q₁ k₁ q₂ k₂ : ℤ, q₂ * k₁ - q₁ * k₂ = 1 ∧
      t ^ 2 * q₁ ^ 2 + l ^ 2 * (q₁ * s - k₁ * n) ^ 2 +
        (t ^ 2 * q₂ ^ 2 + l ^ 2 * (q₂ * s - k₂ * n) ^ 2) = m)
    ⟨0, by rintro z ⟨q₁, k₁, q₂, k₂, -, rfl⟩; positivity⟩ ⟨_, 0, 1, 1, 0, by ring, rfl⟩
  -- compare with the unimodular pairs `(b₁, b₂ ± b₁)` and `(b₁ ± b₂, b₂)`
  refine ⟨q₁, k₁, q₂, k₂, hdet, r1_four_sq_le ?_ ?_ ?_ ?_⟩
  · have := hmin _ ⟨q₁, k₁, q₂ + q₁, k₂ + k₁, by linear_combination hdet, rfl⟩
    linarith
  · have := hmin _ ⟨q₁, k₁, q₂ - q₁, k₂ - k₁, by linear_combination hdet, rfl⟩
    linarith
  · have := hmin _ ⟨q₁ + q₂, k₁ + k₂, q₂, k₂, by linear_combination hdet, rfl⟩
    linarith
  · have := hmin _ ⟨q₁ - q₂, k₁ - k₂, q₂, k₂, by linear_combination hdet, rfl⟩
    linarith

/-- Injectivity: two coefficient vectors giving the same first coordinate and small second
coordinates (`|y| ≤ t`, `2 t < n`) coincide, since the coefficient matrix is unimodular. -/
private lemma r1_inj {t n s q₁ k₁ q₂ k₂ a₁ a₂ b₁ b₂ : ℤ} (hn : 2 * t < n)
    (hdet : q₂ * k₁ - q₁ * k₂ = 1)
    (ha : |a₁ * (q₁ * s - k₁ * n) + a₂ * (q₂ * s - k₂ * n)| ≤ t)
    (hb : |b₁ * (q₁ * s - k₁ * n) + b₂ * (q₂ * s - k₂ * n)| ≤ t)
    (hq : a₁ * q₁ + a₂ * q₂ = b₁ * q₁ + b₂ * q₂) : a₁ = b₁ ∧ a₂ = b₂ := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  -- the difference of the second coordinates is `-K * n` with `|K * n| ≤ 2 t < n`, so `K = 0`
  have e : a₁ * (q₁ * s - k₁ * n) + a₂ * (q₂ * s - k₂ * n) -
      (b₁ * (q₁ * s - k₁ * n) + b₂ * (q₂ * s - k₂ * n)) =
      -(a₁ * k₁ + a₂ * k₂ - (b₁ * k₁ + b₂ * k₂)) * n := by
    linear_combination s * hq
  have hK : a₁ * k₁ + a₂ * k₂ = b₁ * k₁ + b₂ * k₂ := by
    rcases lt_trichotomy (a₁ * k₁ + a₂ * k₂) (b₁ * k₁ + b₂ * k₂) with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  constructor
  · linear_combination (-(a₁ - b₁)) * hdet + q₂ * hK - k₂ * hq
  · linear_combination (-(a₂ - b₂)) * hdet + k₁ * hq - q₁ * hK

/-- Parallelogram law: `Q(a₁ b₁ + a₂ b₂) ≤ 2 a₁² Q(b₁) + 2 a₂² Q(b₂)` for
`Q(q, y) = t² q² + l² y²`. -/
private lemma r1_parallelogram (t l a₁ a₂ q₁ q₂ y₁ y₂ : ℤ) :
    t ^ 2 * (a₁ * q₁ + a₂ * q₂) ^ 2 + l ^ 2 * (a₁ * y₁ + a₂ * y₂) ^ 2 ≤
      2 * a₁ ^ 2 * (t ^ 2 * q₁ ^ 2 + l ^ 2 * y₁ ^ 2) +
        2 * a₂ ^ 2 * (t ^ 2 * q₂ ^ 2 + l ^ 2 * y₂ ^ 2) := by
  nlinarith [sq_nonneg (t * (a₁ * q₁ - a₂ * q₂)), sq_nonneg (l * (a₁ * y₁ - a₂ * y₂))]

/-- Lagrange's identity for the reduced basis, using `det(b₁, b₂) = n`. -/
private lemma r1_lagrange (t l n s q₁ k₁ q₂ k₂ : ℤ) (hdet : q₂ * k₁ - q₁ * k₂ = 1) :
    (t ^ 2 * q₁ ^ 2 + l ^ 2 * (q₁ * s - k₁ * n) ^ 2) *
        (t ^ 2 * q₂ ^ 2 + l ^ 2 * (q₂ * s - k₂ * n) ^ 2) =
      (t ^ 2 * q₁ * q₂ + l ^ 2 * (q₁ * s - k₁ * n) * (q₂ * s - k₂ * n)) ^ 2 +
        t ^ 2 * l ^ 2 * n ^ 2 := by
  linear_combination t ^ 2 * l ^ 2 * n ^ 2 * (q₂ * k₁ - q₁ * k₂ + 1) * hdet

/-- Consequences of `4 B² ≤ Q₁ Q₂ = B² + C` with `C > 0`. -/
private lemma r1_gram {Q₁ Q₂ B C : ℤ} (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (hB : 4 * B ^ 2 ≤ Q₁ * Q₂)
    (hLag : Q₁ * Q₂ = B ^ 2 + C) (hC : 0 < C) : 0 < Q₁ ∧ 0 < Q₂ ∧ 3 * (Q₁ * Q₂) ≤ 4 * C := by
  have hpos : 0 < Q₁ * Q₂ := by nlinarith [sq_nonneg B]
  refine ⟨lt_of_le_of_ne hQ₁ ?_, lt_of_le_of_ne hQ₂ ?_, by linarith⟩
  · rintro rfl
    simp at hpos
  · rintro rfl
    simp at hpos

/-- Coordinate bounds for `a₁ b₁ + a₂ b₂ = (q, y)` when `|aᵢ| ≤ Sᵢ` and `4 Sᵢ² Qᵢ ≤ t² l²`. -/
private lemma r1_coord_bound {t l q y Q₁ Q₂ a₁ a₂ S₁ S₂ : ℤ} (ht : 0 < t) (hl : 0 < l)
    (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (ha₁ : |a₁| ≤ S₁) (ha₂ : |a₂| ≤ S₂)
    (hS₁ : 4 * S₁ ^ 2 * Q₁ ≤ t ^ 2 * l ^ 2) (hS₂ : 4 * S₂ ^ 2 * Q₂ ≤ t ^ 2 * l ^ 2)
    (hpar : t ^ 2 * q ^ 2 + l ^ 2 * y ^ 2 ≤ 2 * a₁ ^ 2 * Q₁ + 2 * a₂ ^ 2 * Q₂) :
    |q| ≤ l ∧ |y| ≤ t := by
  have e₁ := mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp ha₁).1 (abs_le.mp ha₁).2) hQ₁
  have e₂ := mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp ha₂).1 (abs_le.mp ha₂).2) hQ₂
  have hq : 0 ≤ t ^ 2 * q ^ 2 := by positivity
  have hy : 0 ≤ l ^ 2 * y ^ 2 := by positivity
  refine ⟨abs_le_of_sq_le_sq (le_of_mul_le_mul_left (a := t ^ 2) ?_ (by positivity)) hl.le,
    abs_le_of_sq_le_sq (le_of_mul_le_mul_left (a := l ^ 2) ?_ (by positivity)) ht.le⟩
  · linarith
  · linarith

/-- The size bound, from `t² l² < 4 (Sᵢ + 1)² Qᵢ` and `3 Q₁ Q₂ ≤ 4 t² l² n²`. -/
private lemma r1_size {t l n Q₁ Q₂ S₁ S₂ : ℤ} (ht : 0 < t) (hl : 0 < l) (hn : 0 < n)
    (hS₁0 : 0 ≤ S₁) (hS₂0 : 0 ≤ S₂) (hQ₁ : 0 < Q₁) (hQ₂ : 0 < Q₂)
    (h3 : 3 * (Q₁ * Q₂) ≤ 4 * (t ^ 2 * l ^ 2 * n ^ 2))
    (hS₁ : t ^ 2 * l ^ 2 < 4 * (S₁ + 1) ^ 2 * Q₁) (hS₂ : t ^ 2 * l ^ 2 < 4 * (S₂ + 1) ^ 2 * Q₂) :
    t * (2 * l + 1) ≤ 14 * n * ((2 * S₁ + 1) * (2 * S₂ + 1)) := by
  have hA : 0 < t ^ 2 * l ^ 2 := by positivity
  have hf₁ : t ^ 2 * l ^ 2 < 4 * (2 * S₁ + 1) ^ 2 * Q₁ := by
    have := mul_nonneg (mul_nonneg hS₁0 (by linarith : (0 : ℤ) ≤ 3 * S₁ + 2)) hQ₁.le
    linarith
  have hf₂ : t ^ 2 * l ^ 2 < 4 * (2 * S₂ + 1) ^ 2 * Q₂ := by
    have := mul_nonneg (mul_nonneg hS₂0 (by linarith : (0 : ℤ) ≤ 3 * S₂ + 2)) hQ₂.le
    linarith
  have hprod := mul_lt_mul'' hf₁ hf₂ hA.le hA.le
  have hP : 0 ≤ 16 * ((2 * S₁ + 1) ^ 2 * (2 * S₂ + 1) ^ 2) := by positivity
  have h3' := mul_le_mul_of_nonneg_left h3 hP
  -- `t² l² · 3 t² l² < t² l² · 64 n² F²`, where `F = (2 S₁ + 1) (2 S₂ + 1)`
  have key : 3 * (t ^ 2 * l ^ 2) < 64 * n ^ 2 * ((2 * S₁ + 1) ^ 2 * (2 * S₂ + 1) ^ 2) := by
    refine lt_of_mul_lt_mul_left (a := t ^ 2 * l ^ 2) ?_ hA.le
    linarith
  have h1 : 0 ≤ t * (2 * l + 1) := by positivity
  have h2 : (t * (2 * l + 1)) ^ 2 ≤ (3 * (t * l)) ^ 2 :=
    pow_le_pow_left₀ h1 (by nlinarith) 2
  have hlt : (t * (2 * l + 1)) ^ 2 < (14 * n * ((2 * S₁ + 1) * (2 * S₂ + 1))) ^ 2 := by
    have : 0 ≤ n ^ 2 * ((2 * S₁ + 1) ^ 2 * (2 * S₂ + 1) ^ 2) := by positivity
    linarith
  exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt).le

/-- The integer core of `rankOne_progression`. -/
private lemma r1_main (t l n s : ℤ) (ht : 0 < t) (hl : 0 < l) (hn : 2 * t < n) :
    ∃ (q₁ k₁ q₂ k₂ : ℤ) (S₁ S₂ : ℕ), q₂ * k₁ - q₁ * k₂ = 1 ∧
      (∀ a₁ a₂ : ℤ, |a₁| ≤ S₁ → |a₂| ≤ S₂ →
        |a₁ * q₁ + a₂ * q₂| ≤ l ∧ |a₁ * (q₁ * s - k₁ * n) + a₂ * (q₂ * s - k₂ * n)| ≤ t) ∧
      t * (2 * l + 1) ≤ 14 * n * ((2 * S₁ + 1) * (2 * S₂ + 1)) := by
  obtain ⟨q₁, k₁, q₂, k₂, hdet, hB⟩ := r1_reduced_basis t l n s
  have hQ₁ : 0 ≤ t ^ 2 * q₁ ^ 2 + l ^ 2 * (q₁ * s - k₁ * n) ^ 2 := by positivity
  have hQ₂ : 0 ≤ t ^ 2 * q₂ ^ 2 + l ^ 2 * (q₂ * s - k₂ * n) ^ 2 := by positivity
  have hA : 0 < t ^ 2 * l ^ 2 := by positivity
  have hn0 : 0 < n := by linarith
  obtain ⟨hQ₁pos, hQ₂pos, h3⟩ :=
    r1_gram hQ₁ hQ₂ hB (r1_lagrange t l n s q₁ k₁ q₂ k₂ hdet) (by positivity)
  obtain ⟨S₁, hS₁, hS₁'⟩ := r1_exists_nat _ _ hA.le hQ₁pos
  obtain ⟨S₂, hS₂, hS₂'⟩ := r1_exists_nat _ _ hA.le hQ₂pos
  refine ⟨q₁, k₁, q₂, k₂, S₁, S₂, hdet, fun a₁ a₂ ha₁ ha₂ =>
    r1_coord_bound ht hl hQ₁ hQ₂ ha₁ ha₂ hS₁ hS₂ (r1_parallelogram _ _ _ _ _ _ _ _),
    r1_size ht hl hn0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hQ₁pos hQ₂pos h3 hS₁' hS₂'⟩

/-- A rank-one Bohr set in an interval contains a large proper two-dimensional progression:
the integers `q` with `|q| ≤ L` for which `q * σ` has an integer representative of absolute value
at most `T` contain `{a₁ u₁ + a₂ u₂ : |a₁| ≤ S₁, |a₂| ≤ S₂}`, injectively parametrised, with
`T (2L + 1) ≤ 14 N (2S₁ + 1)(2S₂ + 1)`. The generators come from a reduced basis of the lattice
`{(q, y) ∈ ℤ² : y ≡ q σ [ZMOD N]}` for the quadratic form `T² q² + L² y²`. -/
private theorem rankOne_progression {N : ℕ} [NeZero N] (σ : ZMod N) (L T : ℕ) (hT : 2 * T < N) :
    ∃ (u₁ u₂ : ℤ) (S₁ S₂ : ℕ),
      (∀ a₁ a₂ : ℤ, |a₁| ≤ S₁ → |a₂| ≤ S₂ →
        |a₁ * u₁ + a₂ * u₂| ≤ L ∧
          ∃ y : ℤ, |y| ≤ T ∧ (y : ZMod N) = ((a₁ * u₁ + a₂ * u₂ : ℤ) : ZMod N) * σ) ∧
      (∀ a₁ a₂ b₁ b₂ : ℤ, |a₁| ≤ S₁ → |a₂| ≤ S₂ → |b₁| ≤ S₁ → |b₂| ≤ S₂ →
        a₁ * u₁ + a₂ * u₂ = b₁ * u₁ + b₂ * u₂ → a₁ = b₁ ∧ a₂ = b₂) ∧
      T * (2 * L + 1) ≤ 14 * N * ((2 * S₁ + 1) * (2 * S₂ + 1)) := by
  by_cases h0 : T = 0 ∨ L = 0
  · -- degenerate case: the progression `{0}`
    refine ⟨0, 0, 0, 0, fun a₁ a₂ _ _ => ⟨by simp, 0, by simp⟩,
      fun a₁ a₂ b₁ b₂ h₁ h₂ h₃ h₄ _ => ?_, ?_⟩
    · simp only [Nat.cast_zero, abs_nonpos_iff] at h₁ h₂ h₃ h₄
      exact ⟨h₁.trans h₃.symm, h₂.trans h₄.symm⟩
    · rcases h0 with rfl | rfl <;> omega
  · obtain ⟨hT0, hL0⟩ := not_or.mp h0
    obtain ⟨q₁, k₁, q₂, k₂, S₁, S₂, hdet, hbd, hsize⟩ :=
      r1_main T L N σ.val (by omega) (by omega) (by exact_mod_cast hT)
    refine ⟨q₁, q₂, S₁, S₂, fun a₁ a₂ ha₁ ha₂ =>
      ⟨(hbd a₁ a₂ ha₁ ha₂).1, _, (hbd a₁ a₂ ha₁ ha₂).2, ?_⟩,
      fun a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hq =>
        r1_inj (by exact_mod_cast hT) hdet (hbd a₁ a₂ ha₁ ha₂).2 (hbd b₁ b₂ hb₁ hb₂).2 hq,
      by exact_mod_cast hsize⟩
    -- `y = q * σ.val - K * N` and `(σ.val : ZMod N) = σ`, `(N : ZMod N) = 0`
    push_cast [ZMod.natCast_zmod_val, ZMod.natCast_self]
    ring

/-! ## Bohr sets contain large proper progressions -/

/-- Rewriting a sum over the doubled progression as a sum over the old generators. -/
private lemma bohr_sum_append {N m : ℕ} (u₁ u₂ : Fin m → ℤ) (v : Fin m → ZMod N)
    (a : Fin (m + m) → ℤ) :
    ∑ j, (a j : ZMod N) *
        Fin.append (fun j => (u₁ j : ZMod N) * v j) (fun j => (u₂ j : ZMod N) * v j) j =
      ∑ j, ((a (Fin.castAdd m j) * u₁ j + a (Fin.natAdd m j) * u₂ j : ℤ) : ZMod N) * v j := by
  rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.append_left, Fin.append_right]
  push_cast
  ring

/-- A coefficient vector in the box `Fin.append S₁ S₂` restricts to the boxes `S₁` and `S₂`. -/
private lemma bohr_append_bound {m : ℕ} {S₁ S₂ : Fin m → ℕ} {a : Fin (m + m) → ℤ}
    (ha : ∀ j, |a j| ≤ Fin.append S₁ S₂ j) (j : Fin m) :
    |a (Fin.castAdd m j)| ≤ S₁ j ∧ |a (Fin.natAdd m j)| ≤ S₂ j := by
  have h₁ := ha (Fin.castAdd m j)
  have h₂ := ha (Fin.natAdd m j)
  rw [Fin.append_left] at h₁
  rw [Fin.append_right] at h₂
  exact ⟨h₁, h₂⟩

/-- One frequency at a time: a proper progression in `ZMod N` contains a proper progression of
twice the dimension on which `x ↦ x * r` takes values with integer representatives of absolute
value at most `m T`, losing a factor at most `(14 N / T) ^ m` in size. Each coordinate is cut down
with `rankOne_progression`. -/
private theorem double_progression {N : ℕ} [NeZero N] {m : ℕ} (v : Fin m → ZMod N) (L : Fin m → ℕ)
    (hv : ∀ a b : Fin m → ℤ, (∀ j, |a j| ≤ L j) → (∀ j, |b j| ≤ L j) →
      ∑ j, (a j : ZMod N) * v j = ∑ j, (b j : ZMod N) * v j → a = b)
    (r : ZMod N) (T : ℕ) (hT : 2 * T < N) :
    ∃ (v' : Fin (m + m) → ZMod N) (L' : Fin (m + m) → ℕ),
      (∀ a b : Fin (m + m) → ℤ, (∀ j, |a j| ≤ L' j) → (∀ j, |b j| ≤ L' j) →
        ∑ j, (a j : ZMod N) * v' j = ∑ j, (b j : ZMod N) * v' j → a = b) ∧
      (∀ a' : Fin (m + m) → ℤ, (∀ j, |a' j| ≤ L' j) →
        ∃ a : Fin m → ℤ, (∀ j, |a j| ≤ L j) ∧
          ∑ j, (a' j : ZMod N) * v' j = ∑ j, (a j : ZMod N) * v j) ∧
      (∀ a' : Fin (m + m) → ℤ, (∀ j, |a' j| ≤ L' j) →
        ∃ y : ℤ, |y| ≤ m * T ∧ (y : ZMod N) = (∑ j, (a' j : ZMod N) * v' j) * r) ∧
      (T : ℝ) ^ m * ∏ j, (2 * L j + 1 : ℝ) ≤ (14 * N) ^ m * ∏ j, (2 * L' j + 1 : ℝ) := by
  choose u₁ u₂ S₁ S₂ hbox hinj hsize using fun j => rankOne_progression (v j * r) (L j) T hT
  refine ⟨Fin.append (fun j => (u₁ j : ZMod N) * v j) (fun j => (u₂ j : ZMod N) * v j),
    Fin.append S₁ S₂, ?_, ?_, ?_, ?_⟩
  · -- properness
    intro a b ha hb hab
    rw [bohr_sum_append, bohr_sum_append] at hab
    have key := hv _ _
      (fun j => (hbox j _ _ (bohr_append_bound ha j).1 (bohr_append_bound ha j).2).1)
      (fun j => (hbox j _ _ (bohr_append_bound hb j).1 (bohr_append_bound hb j).2).1) hab
    have hj : ∀ j, a (Fin.castAdd m j) = b (Fin.castAdd m j) ∧
        a (Fin.natAdd m j) = b (Fin.natAdd m j) := fun j =>
      hinj j _ _ _ _ (bohr_append_bound ha j).1 (bohr_append_bound ha j).2
        (bohr_append_bound hb j).1 (bohr_append_bound hb j).2 (congrFun key j)
    funext i
    exact Fin.addCases (fun j => (hj j).1) (fun j => (hj j).2) i
  · -- containment
    intro a' ha'
    exact ⟨_, fun j => (hbox j _ _ (bohr_append_bound ha' j).1 (bohr_append_bound ha' j).2).1,
      bohr_sum_append u₁ u₂ v a'⟩
  · -- phase
    intro a' ha'
    choose y hy hyeq using fun j =>
      (hbox j _ _ (bohr_append_bound ha' j).1 (bohr_append_bound ha' j).2).2
    refine ⟨∑ j, y j, ?_, ?_⟩
    · calc |∑ j, y j| ≤ ∑ j, |y j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin m, (T : ℤ) := Finset.sum_le_sum fun j _ => hy j
        _ = m * T := by simp
    · rw [bohr_sum_append, Finset.sum_mul, Int.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hyeq j, mul_assoc]
  · -- size
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h : ∀ j, (T : ℝ) * (2 * L j + 1) ≤ 14 * N * ((2 * S₁ j + 1) * (2 * S₂ j + 1)) :=
      fun j => by exact_mod_cast hsize j
    calc (T : ℝ) ^ m * ∏ j, (2 * (L j : ℝ) + 1) = ∏ j, ((T : ℝ) * (2 * L j + 1)) := by
          rw [Finset.prod_mul_distrib, Fin.prod_const]
      _ ≤ ∏ j, (14 * (N : ℝ) * ((2 * S₁ j + 1) * (2 * S₂ j + 1))) :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => h j
      _ = _ := by rw [Finset.prod_mul_distrib, Fin.prod_const, Finset.prod_mul_distrib]

/-- **Bohr sets contain large proper progressions.** The Bohr set of radius `1/4` of at most `D`
frequencies in `ZMod N` contains a proper progression of dimension at most `2 ^ D` and size at
least `κ N`, where `κ > 0` depends only on `D`. -/
private theorem bohr_progression (D : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [NeZero N] (Γ : Finset (ZMod N)), Γ.card ≤ D →
      ∃ (m : ℕ) (v : Fin m → ZMod N) (L : Fin m → ℕ), m ≤ 2 ^ D ∧
        (∀ a b : Fin m → ℤ, (∀ j, |a j| ≤ L j) → (∀ j, |b j| ≤ L j) →
          ∑ j, (a j : ZMod N) * v j = ∑ j, (b j : ZMod N) * v j → a = b) ∧
        (∀ a : Fin m → ℤ, (∀ j, |a j| ≤ L j) → ∀ r ∈ Γ,
          ∃ y : ℤ, 4 * |y| ≤ N ∧ (y : ZMod N) = (∑ j, (a j : ZMod N) * v j) * r) ∧
        κ * N ≤ ∏ j, (2 * L j + 1 : ℝ) := by
  induction D with
  | zero =>
    refine ⟨1 / 2, by norm_num, fun N _ Γ hΓ => ?_⟩
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (N - 1) / 2 := ⟨_, rfl⟩
    have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hK₁ : 2 * (K : ℤ) < N := by exact_mod_cast (show 2 * K < N by omega)
    have hK₂ : (N : ℝ) ≤ 2 * (2 * K + 1) := by
      exact_mod_cast (show N ≤ 2 * (2 * K + 1) by omega)
    refine ⟨1, fun _ => 1, fun _ => K, by norm_num, ?_, ?_, ?_⟩
    · -- an interval of length less than `N` injects into `ZMod N`
      intro a b ha hb hab
      simp only [Finset.univ_unique, Finset.sum_singleton, mul_one] at hab
      have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hab
      have h₁ := abs_le.mp (ha default)
      have h₂ := abs_le.mp (hb default)
      have h₀ := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by linarith, by linarith⟩)
      funext j
      rw [Subsingleton.elim j default]
      linarith
    · intro a _ r hr
      simp [Finset.card_eq_zero.mp (Nat.le_zero.mp hΓ)] at hr
    · simp only [Finset.univ_unique, Finset.prod_singleton]
      linarith
  | succ D ih =>
    obtain ⟨κ, hκ, ih⟩ := ih
    -- `c` is the loss factor per coordinate in the inductive step
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (112 * 2 ^ D) := ⟨_, rfl⟩
    have hc₀ : 0 < c := by
      rw [hc]
      positivity
    have hc₁ : c ≤ 1 := by
      rw [hc, div_le_one (by positivity)]
      have : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
      linarith
    refine ⟨min (κ * c ^ 2 ^ D) (1 / (8 * 2 ^ D)), lt_min (by positivity) (by positivity), ?_⟩
    intro N _ Γ hΓ
    have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    -- split off one frequency `r`
    obtain ⟨r, Γ', hΓ', hsub⟩ : ∃ (r : ZMod N) (Γ' : Finset (ZMod N)), Γ'.card ≤ D ∧
        ∀ s ∈ Γ, s = r ∨ s ∈ Γ' := by
      rcases Γ.eq_empty_or_nonempty with h | ⟨r, hr⟩
      · exact ⟨0, ∅, by simp, by simp [h]⟩
      · refine ⟨r, Γ.erase r, ?_, fun s hs => ?_⟩
        · rw [Finset.card_erase_of_mem hr]
          omega
        · by_cases hsr : s = r
          · exact Or.inl hsr
          · exact Or.inr (Finset.mem_erase.mpr ⟨hsr, hs⟩)
    obtain ⟨m, v, L, hm, hprop, hbohr, hsize⟩ := ih N Γ' hΓ'
    obtain ⟨T, hT⟩ : ∃ T : ℕ, T = N / (4 * 2 ^ D) := ⟨_, rfl⟩
    have h2D : 1 ≤ 2 ^ D := Nat.one_le_two_pow
    have hTN : 4 * 2 ^ D * T ≤ N := by
      rw [hT]
      exact Nat.mul_div_le N _
    have hT2 : 2 * T < N := by
      have : 4 * T ≤ 4 * 2 ^ D * T := Nat.mul_le_mul_right T (by omega)
      omega
    obtain ⟨v', L', hprop', hcont, hphase, hsize'⟩ := double_progression v L hprop r T hT2
    refine ⟨m + m, v', L', by rw [pow_succ]; omega, hprop', ?_, ?_⟩
    · intro a' ha' s hs
      rcases hsub s hs with rfl | hs'
      · -- the new frequency: `|y| ≤ m * T` and `4 * m * T ≤ N`
        obtain ⟨y, hy, hyeq⟩ := hphase a' ha'
        refine ⟨y, ?_, hyeq⟩
        have h₁ : 4 * (m * T) ≤ N :=
          le_trans (by rw [← mul_assoc]; exact Nat.mul_le_mul_right T (by omega)) hTN
        have h₂ : (4 : ℤ) * (m * T) ≤ N := by exact_mod_cast h₁
        linarith
      · -- the old frequencies
        obtain ⟨a, ha, heq⟩ := hcont a' ha'
        obtain ⟨y, hy, hyeq⟩ := hbohr a ha s hs'
        exact ⟨y, hy, by rw [heq]; exact hyeq⟩
    · rcases lt_or_ge N (8 * 2 ^ D) with hsmall | hlarge
      · -- small `N`: the progression has at least one element
        have h₁ : (1 : ℝ) ≤ ∏ j, (2 * (L' j : ℝ) + 1) := by
          calc (1 : ℝ) = ∏ _j : Fin (m + m), (1 : ℝ) := by simp
            _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun j _ => by
              have : (0 : ℝ) ≤ L' j := Nat.cast_nonneg _
              linarith
        have h₂ : (N : ℝ) < 8 * 2 ^ D := by exact_mod_cast hsmall
        calc min (κ * c ^ 2 ^ D) (1 / (8 * 2 ^ D)) * (N : ℝ) ≤ 1 / (8 * 2 ^ D) * N :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg N)
          _ ≤ 1 := by
              rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
              exact h₂.le
          _ ≤ _ := h₁
      · -- large `N`: `T ≥ N / (8 * 2 ^ D)`, so each coordinate loses at most a factor `c`
        have hT1 : 1 ≤ T := by
          rw [hT]
          exact Nat.div_pos (by omega) (by positivity)
        have hNT : (N : ℝ) ≤ 8 * 2 ^ D * T := by
          have h₁ : N < 4 * 2 ^ D * (T + 1) := by
            rw [hT]
            exact Nat.lt_mul_div_succ N (by positivity)
          have h₂ : 4 * 2 ^ D * 1 ≤ 4 * 2 ^ D * T := Nat.mul_le_mul_left _ hT1
          have h₃ : N ≤ 8 * 2 ^ D * T := by nlinarith
          exact_mod_cast h₃
        have hcT : c * (14 * N) ≤ T := by
          rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          linarith
        have hpos : (0 : ℝ) < (14 * N) ^ m := by positivity
        have key : (14 * (N : ℝ)) ^ m * (c ^ m * (κ * N)) ≤
            (14 * N) ^ m * ∏ j, (2 * (L' j : ℝ) + 1) :=
          calc (14 * (N : ℝ)) ^ m * (c ^ m * (κ * N)) = (c * (14 * N)) ^ m * (κ * N) := by
                ring
            _ ≤ (T : ℝ) ^ m * ∏ j, (2 * (L j : ℝ) + 1) :=
                mul_le_mul (pow_le_pow_left₀ (by positivity) hcT m) hsize (by positivity)
                  (by positivity)
            _ ≤ _ := hsize'
        calc min (κ * c ^ 2 ^ D) (1 / (8 * 2 ^ D)) * (N : ℝ) ≤ κ * c ^ 2 ^ D * N :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)
          _ ≤ κ * c ^ m * N :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one hc₀.le hc₁ hm) hκ.le) (Nat.cast_nonneg N)
          _ = c ^ m * (κ * N) := by ring
          _ ≤ _ := le_of_mul_le_mul_left key hpos

/-! ## Bogolyubov's lemma -/

/-- Orthogonality for the standard additive character of `ZMod N`. -/
private lemma bog_sum_char {N : ℕ} [NeZero N] (b : ZMod N) :
    ∑ r : ZMod N, ZMod.stdAddChar (r * b) = if b = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

/-- The squared modulus of a Fourier coefficient of `B`, expanded as a double sum. -/
private lemma bog_normSq {N : ℕ} [NeZero N] (B : Finset (ZMod N)) (r : ZMod N) :
    ((‖∑ b ∈ B, ZMod.stdAddChar (r * b)‖ ^ 2 : ℝ) : ℂ) =
      ∑ b ∈ B, ∑ c ∈ B, ZMod.stdAddChar (r * (b - c)) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, mul_sub, sub_eq_add_neg]

/-- Parseval's identity for the indicator function of `B`. -/
private lemma bog_parseval {N : ℕ} [NeZero N] (B : Finset (ZMod N)) :
    ∑ r : ZMod N, ‖∑ b ∈ B, ZMod.stdAddChar (r * b)‖ ^ 2 = N * B.card := by
  have h : ((∑ r : ZMod N, ‖∑ b ∈ B, ZMod.stdAddChar (r * b)‖ ^ 2 : ℝ) : ℂ) =
      ((N * B.card : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [bog_normSq]
    -- move the sum over `r` innermost, then apply orthogonality
    rw [Finset.sum_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    simp_rw [bog_sum_char, sub_eq_zero]
    simp [mul_comm]
  exact_mod_cast h

/-- If `x` is not of the form `b₁ + b₂ - b₃ - b₄` with `bᵢ ∈ B`, then the fourth moment of the
Fourier transform of `B`, twisted by the character at `x`, vanishes. -/
private lemma bog_fourth {N : ℕ} [NeZero N] (B : Finset (ZMod N)) (x : ZMod N)
    (hx : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ b₃ ∈ B, ∀ b₄ ∈ B, x ≠ b₁ + b₂ - b₃ - b₄) :
    ∑ r : ZMod N, ((‖∑ b ∈ B, ZMod.stdAddChar (r * b)‖ ^ 2 : ℝ) : ℂ) ^ 2 *
      ZMod.stdAddChar (r * x) = 0 := by
  simp_rw [bog_normSq, sq, Finset.sum_mul_sum, Finset.sum_mul, ← AddChar.map_add_eq_mul]
  -- move the sum over `r` innermost, then apply orthogonality
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b₁ hb₁ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b₂ hb₂ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b₃ hb₃ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b₄ hb₄ => ?_
  have hne : b₁ - b₃ + (b₂ - b₄) + x ≠ 0 := fun h =>
    hx _ hb₃ _ hb₄ _ hb₁ _ hb₂ (by linear_combination h)
  simp_rw [← mul_add]
  rw [bog_sum_char, ite_eq_right hne]

/-- Counting large Fourier coefficients: if `∑ i, a i = n * β` with `a ≥ 0`, then at most
`n ^ 2 / β ^ 2` indices satisfy `β ^ 3 ≤ n * a i`. -/
private lemma bog_card {ι : Type*} [Fintype ι] (a : ι → ℝ) {n β : ℝ} (hβ : 0 < β) (hn : 0 ≤ n)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = n * β) (s : Finset ι)
    (hs : ∀ i ∈ s, β ^ 3 ≤ n * a i) : (s.card : ℝ) * β ^ 2 ≤ n ^ 2 := by
  have h : (s.card : ℝ) * β ^ 2 * β ≤ n ^ 2 * β := by
    calc (s.card : ℝ) * β ^ 2 * β = ∑ i ∈ s, β ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ s, n * a i := Finset.sum_le_sum hs
      _ = n * ∑ i ∈ s, a i := (Finset.mul_sum _ _ _).symm
      _ ≤ n * ∑ i, a i := by
          gcongr
          · exact fun i _ _ => ha i
          · exact Finset.subset_univ s
      _ = n ^ 2 * β := by rw [hsum]; ring
  exact le_of_mul_le_mul_right h hβ

/-- The final positivity estimate. Here `a i` plays the role of `‖F i‖ ^ 2` and `c i` of the real
part of the character at `x`, which is nonnegative on the large spectrum. -/
private lemma bog_ineq {ι : Type*} [Fintype ι] (a c : ι → ℝ) (i₀ : ι) {n β : ℝ}
    (hβ : 0 < β) (hn : 0 < n) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = n * β)
    (ha₀ : a i₀ = β ^ 2) (hc₀ : c i₀ = 1) (hc : ∀ i, -1 ≤ c i)
    (hcΓ : ∀ i, β ^ 3 ≤ n * a i → 0 ≤ c i) : 0 < ∑ i, a i ^ 2 * c i := by
  classical
  -- away from `i₀`, each term `a i ^ 2 * c i` is at least `-(β ^ 3 / n) * a i`
  have hterm : ∀ i ∈ univ.erase i₀, -(β ^ 3 * a i) ≤ n * (a i ^ 2 * c i) := by
    intro i _
    have hai := ha i
    by_cases h : β ^ 3 ≤ n * a i
    · have hci := hcΓ i h
      have : 0 ≤ n * (a i ^ 2 * c i) := by positivity
      nlinarith [pow_pos hβ 3]
    · replace h := not_le.mp h
      have hci := hc i
      nlinarith [mul_nonneg (mul_nonneg hn.le (sq_nonneg (a i))) (by linarith : 0 ≤ c i + 1),
        mul_nonneg hai (by linarith : 0 ≤ β ^ 3 - n * a i)]
  have h₁ := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h₁
  have h₂ := Finset.add_sum_erase univ a (mem_univ i₀)
  have h₃ := Finset.add_sum_erase univ (fun i => a i ^ 2 * c i) (mem_univ i₀)
  rw [hsum, ha₀] at h₂
  rw [← h₃, ha₀, hc₀]
  have hS : ∑ i ∈ univ.erase i₀, a i = n * β - β ^ 2 := by linarith
  rw [hS] at h₁
  have : 0 < n * ((β ^ 2) ^ 2 * 1 + ∑ i ∈ univ.erase i₀, a i ^ 2 * c i) := by
    nlinarith [pow_pos hβ 5]
  exact pos_of_mul_pos_right this hn.le

/-- If `z = y` in `ZMod N` with `4 |y| ≤ N`, then `e(z)` has nonnegative real part. -/
private lemma bog_re_nonneg {N : ℕ} [NeZero N] (z : ZMod N) (y : ℤ) (hy : 4 * |y| ≤ N)
    (hz : (y : ZMod N) = z) : 0 ≤ (ZMod.stdAddChar z : ℂ).re := by
  subst hz
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have h₁ : (4 : ℝ) * |(y : ℝ)| ≤ N := by exact_mod_cast hy
  have h₂ : 2 * ↑Real.pi * Complex.I * ↑y / ↑N =
      ((2 * Real.pi * y / N : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ZMod.stdAddChar_coe, h₂, Complex.exp_ofReal_mul_I_re]
  apply Real.cos_nonneg_of_mem_Icc
  rw [Set.mem_Icc, ← abs_le, abs_div, abs_of_pos hN, div_le_iff₀ hN, abs_mul, abs_mul, abs_two,
    abs_of_pos Real.pi_pos]
  nlinarith [mul_le_mul_of_nonneg_left h₁ Real.pi_pos.le]

/-- **Bogolyubov's lemma**: if `B ⊆ ZMod N` has density `α`, then `2B - 2B` contains the Bohr set
of radius `1/4` of a set `Γ` of at most `α⁻²` frequencies. -/
private theorem bogolyubov {N : ℕ} [NeZero N] (B : Finset (ZMod N)) (hB : B.Nonempty) :
    ∃ Γ : Finset (ZMod N), (Γ.card : ℝ) * (B.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 ∧
      ∀ x : ZMod N, (∀ r ∈ Γ, ∃ y : ℤ, 4 * |y| ≤ N ∧ (y : ZMod N) = x * r) →
        ∃ b₁ ∈ B, ∃ b₂ ∈ B, ∃ b₃ ∈ B, ∃ b₄ ∈ B, x = b₁ + b₂ - b₃ - b₄ := by
  have hB' : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hpars := bog_parseval B
  -- `Γ` is the large spectrum of `B`
  refine ⟨univ.filter fun r => (B.card : ℝ) ^ 3 ≤ N * ‖∑ b ∈ B, ZMod.stdAddChar (r * b)‖ ^ 2,
    bog_card _ hB' hN.le (fun _ => sq_nonneg _) hpars _ fun r hr => (mem_filter.mp hr).2, ?_⟩
  intro x hx
  by_contra hcon
  push Not at hcon
  have h₄ := congrArg Complex.re (bog_fourth B x hcon)
  rw [Complex.re_sum, Complex.zero_re] at h₄
  simp only [← Complex.ofReal_pow, Complex.re_ofReal_mul] at h₄
  refine (bog_ineq (fun r => ‖∑ b ∈ B, ZMod.stdAddChar (r * b)‖ ^ 2)
    (fun r => (ZMod.stdAddChar (r * x) : ℂ).re) 0 hB' hN (fun _ => sq_nonneg _) hpars ?_ ?_ ?_
    ?_).ne' h₄
  · simp
  · simp
  · intro r
    have h := Complex.abs_re_le_norm (ZMod.stdAddChar (r * x) : ℂ)
    rw [AddChar.norm_apply] at h
    exact (abs_le.mp h).1
  · intro r hr
    obtain ⟨y, hy, hyx⟩ := hx r (mem_filter.mpr ⟨mem_univ r, hr⟩)
    exact bog_re_nonneg _ y hy (hyx.trans (mul_comm x r))

/-! ## Ruzsa's modelling lemma -/

/-- Pigeonhole into eight classes: some class contains at least an eighth of `A`. -/
private lemma model_exists_large_class (A : Finset ℤ) (c : ℤ → ℕ) (hc : ∀ a ∈ A, c a < 8) :
    ∃ j, A.card ≤ 8 * (A.filter fun a ↦ c a = j).card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨0, by simp⟩
  obtain ⟨j, -, hj⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := A) (t := range 8)
    (n := (A.card - 1) / 8) (fun a ha ↦ mem_range.mpr (hc a ha))
    (by rw [card_range]; have := hA.card_pos; omega)
  exact ⟨j, by omega⟩

/-- If eight numbers `u i` all satisfy `m ≤ 8 * u i < m + p`, then so does their sum. -/
private lemma model_sum_window {m p : ℕ} (u : Fin 8 → ℕ)
    (hu : ∀ i, m ≤ 8 * u i ∧ 8 * u i < m + p) : m ≤ ∑ i, u i ∧ ∑ i, u i < m + p := by
  have h1 : ∑ _i : Fin 8, m ≤ ∑ i, 8 * u i := sum_le_sum fun i _ ↦ (hu i).1
  have h2 : ∑ i, 8 * u i < ∑ _i : Fin 8, (m + p) :=
    sum_lt_sum_of_nonempty univ_nonempty fun i _ ↦ (hu i).2
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum] at h1 h2
  omega

/-- **Ruzsa's modelling lemma.** If `D` contains every difference of two sums of eight elements
of `A`, then some `A' ⊆ A` with `|A| ≤ 8 |A'|` is Freiman isomorphic of order `8` to a subset of
`ZMod N` with `N ≤ 4 |D|`. -/
private theorem modelling (A D : Finset ℤ) (hA : A.Nonempty)
    (hD : ∀ x y : Fin 8 → ℤ, (∀ i, x i ∈ A) → (∀ i, y i ∈ A) → ∑ i, x i - ∑ i, y i ∈ D) :
    ∃ N : ℕ, 0 < N ∧ N ≤ 4 * D.card ∧
      ∃ (φ : ℤ → ZMod N) (A' : Finset ℤ), A' ⊆ A ∧ A.card ≤ 8 * A'.card ∧
        ∀ x y : Fin 8 → ℤ, (∀ i, x i ∈ A') → (∀ i, y i ∈ A') →
          (∑ i, x i = ∑ i, y i ↔ ∑ i, φ (x i) = ∑ i, φ (y i)) := by
  obtain ⟨a₀, ha₀⟩ := hA
  have h0D : (0 : ℤ) ∈ D := by
    simpa using hD (fun _ ↦ a₀) (fun _ ↦ a₀) (fun _ ↦ ha₀) (fun _ ↦ ha₀)
  have hM : 0 < D.card := card_pos.mpr ⟨0, h0D⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 4 * D.card := ⟨_, rfl⟩
  have hNpos : 0 < N := by omega
  -- A prime exceeding `2 * D.card` and the absolute value of every element of `D`.
  obtain ⟨p, hp, hpPrime⟩ := Nat.exists_infinite_primes (2 * D.card + D.sup Int.natAbs + 1)
  have : Fact p.Prime := ⟨hpPrime⟩
  have hpos : 0 < p := hpPrime.pos
  obtain ⟨K, hK⟩ : ∃ K, K = p / N := ⟨_, rfl⟩
  have hKN : K * N ≤ p := by rw [hK]; exact Nat.div_mul_le_self p N
  -- Bad multipliers `r`: those with `r * z = k * N` in `ZMod p` for some nonzero `z ∈ D`
  -- and some `|k| ≤ K`. There are fewer than `p` of them.
  set bad : Finset (ZMod p) := ((D.erase 0) ×ˢ Icc (-(K : ℤ)) K).image
    fun zk ↦ (zk.2 : ZMod p) * (N : ZMod p) / (zk.1 : ZMod p)
  have hbad : bad.card < p := by
    have hIcc : (Icc (-(K : ℤ)) K).card = 2 * K + 1 := by rw [Int.card_Icc]; omega
    calc bad.card ≤ (D.erase 0).card * (Icc (-(K : ℤ)) K).card :=
          card_image_le.trans_eq (card_product _ _)
      _ ≤ D.card * (2 * K + 1) := by rw [hIcc]; exact Nat.mul_le_mul_right _ (card_erase_le ..)
      _ < p := by
        have : 2 * (D.card * (2 * K + 1)) = K * N + 2 * D.card := by rw [hN]; ring
        omega
  have hlt : bad.card < (univ : Finset (ZMod p)).card := by simpa [ZMod.card] using hbad
  obtain ⟨r, hr⟩ : ∃ r, r ∉ bad := by
    by_contra! h
    exact hlt.not_ge (card_le_card fun x _ ↦ h x)
  -- Canonical representatives in `[0, p)` of the dilates `r * a`.
  obtain ⟨v, hvp, hvr⟩ : ∃ v : ℤ → ℕ, (∀ a, v a < p) ∧ ∀ a, (v a : ZMod p) = r * a :=
    ⟨fun a ↦ (r * a).val, fun a ↦ ZMod.val_lt _, fun a ↦ ZMod.natCast_zmod_val _⟩
  -- Split `[0, p)` into eight windows and keep the most popular one.
  obtain ⟨j, hj⟩ := model_exists_large_class A (fun a ↦ 8 * v a / p)
    fun a _ ↦ Nat.div_lt_of_lt_mul (by have := hvp a; omega)
  obtain ⟨m, hm⟩ : ∃ m, m = j * p := ⟨_, rfl⟩
  have hwin : ∀ a ∈ A.filter (fun a ↦ 8 * v a / p = j), m ≤ 8 * v a ∧ 8 * v a < m + p := by
    intro a ha
    have h := (mem_filter.mp ha).2
    rw [hm, ← h]
    exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hpos⟩
  refine ⟨N, hNpos, hN.le, fun a ↦ (v a : ZMod N), A.filter (fun a ↦ 8 * v a / p = j),
    filter_subset _ _, hj, ?_⟩
  intro x y hx hy
  have hSx := model_sum_window (fun i ↦ v (x i)) fun i ↦ hwin _ (hx i)
  have hSy := model_sum_window (fun i ↦ v (y i)) fun i ↦ hwin _ (hy i)
  -- The difference `w` of the two sums of representatives is less than `p` in absolute value,
  -- and is congruent to `r * (∑ x - ∑ y)` modulo `p`.
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = (∑ i, v (x i) : ℕ) - (∑ i, v (y i) : ℕ) := ⟨_, rfl⟩
  have hwp : (w : ZMod p) = r * ((∑ i, x i - ∑ i, y i : ℤ) : ZMod p) := by
    rw [hw]
    push_cast
    simp only [hvr, ← mul_sum, mul_sub]
  have hwlt : |w| < p := by
    rw [abs_lt, hw]
    constructor <;> omega
  constructor
  · intro hxy
    have hw0 : w = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd ?_ hwlt
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hwp, hxy, sub_self, Int.cast_zero, mul_zero]
    have : ∑ i, v (x i) = ∑ i, v (y i) := by omega
    simp only [← Nat.cast_sum, this]
  · intro hφ
    by_contra hne
    have hz : ∑ i, x i - ∑ i, y i ≠ 0 := sub_ne_zero.mpr hne
    have hzD : ∑ i, x i - ∑ i, y i ∈ D :=
      hD x y (fun i ↦ filter_subset _ _ (hx i)) (fun i ↦ filter_subset _ _ (hy i))
    -- A nonzero element of `D` stays nonzero modulo `p`.
    have hzp : ((∑ i, x i - ∑ i, y i : ℤ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      have hle : p ≤ (∑ i, x i - ∑ i, y i).natAbs := by
        simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natAbs_dvd_natAbs.mpr h)
      have := le_sup (f := Int.natAbs) hzD
      omega
    -- `w` is a multiple `N * k` of `N` with `|k| ≤ K`.
    have hwN : (w : ZMod N) = 0 := by
      rw [hw]
      push_cast
      rw [sub_eq_zero]
      exact hφ
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd w N).1 hwN
    have hKz : (K : ℤ) = (p : ℤ) / (N : ℤ) := by rw [hK]; exact Int.natCast_div p N
    have hNz : (0 : ℤ) < N := by exact_mod_cast hNpos
    rw [hk, abs_lt] at hwlt
    have hk1 : k ≤ K := by
      rw [hKz, Int.le_ediv_iff_mul_le hNz]
      linarith [hwlt.2]
    have hk2 : -k ≤ K := by
      rw [hKz, Int.le_ediv_iff_mul_le hNz]
      linarith [hwlt.1]
    -- Then `r = k * N / z` would be a bad multiplier.
    apply hr
    refine mem_image.mpr ⟨(∑ i, x i - ∑ i, y i, k),
      mem_product.mpr ⟨mem_erase.mpr ⟨hz, hzD⟩, mem_Icc.mpr ⟨by omega, hk1⟩⟩, ?_⟩
    dsimp only
    rw [div_eq_iff hzp, ← hwp, hk]
    push_cast
    ring

/-! ## Pulling a progression back through a Freiman isomorphism -/

/-- If `φ` is a Freiman isomorphism of order `8` on `A'`, then for elements
`tᵢ = b₁ + b₂ - b₃ - b₄` of `2A' - 2A'` with images `sᵢ = φ b₁ + φ b₂ - φ b₃ - φ b₄`,
we have `t₁ + t₂ = t₃ + t₄ ↔ s₁ + s₂ = s₃ + s₄`. -/
private lemma pull_key {N : ℕ} {A' : Finset ℤ} {φ : ℤ → ZMod N}
    (hφ : ∀ x y : Fin 8 → ℤ, (∀ i, x i ∈ A') → (∀ i, y i ∈ A') →
      (∑ i, x i = ∑ i, y i ↔ ∑ i, φ (x i) = ∑ i, φ (y i)))
    {t₁ t₂ t₃ t₄ : ℤ} {s₁ s₂ s₃ s₄ : ZMod N}
    (h₁ : ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
      t₁ = b₁ + b₂ - b₃ - b₄ ∧ s₁ = φ b₁ + φ b₂ - φ b₃ - φ b₄)
    (h₂ : ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
      t₂ = b₁ + b₂ - b₃ - b₄ ∧ s₂ = φ b₁ + φ b₂ - φ b₃ - φ b₄)
    (h₃ : ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
      t₃ = b₁ + b₂ - b₃ - b₄ ∧ s₃ = φ b₁ + φ b₂ - φ b₃ - φ b₄)
    (h₄ : ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
      t₄ = b₁ + b₂ - b₃ - b₄ ∧ s₄ = φ b₁ + φ b₂ - φ b₃ - φ b₄) :
    t₁ + t₂ = t₃ + t₄ ↔ s₁ + s₂ = s₃ + s₄ := by
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, rfl, rfl⟩ := h₁
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, c₄, hc₄, rfl, rfl⟩ := h₂
  obtain ⟨d₁, hd₁, d₂, hd₂, d₃, hd₃, d₄, hd₄, rfl, rfl⟩ := h₃
  obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, e₄, he₄, rfl, rfl⟩ := h₄
  -- move the negative terms to the other side to get an identity between two `8`-term sums
  have H := hφ ![b₁, b₂, c₁, c₂, d₃, d₄, e₃, e₄] ![d₁, d₂, e₁, e₂, b₃, b₄, c₃, c₄]
    (by intro i; fin_cases i <;> simpa) (by intro i; fin_cases i <;> simpa)
  simp only [Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    at H
  constructor
  · intro h
    linear_combination H.1 (by linear_combination h)
  · intro h
    linear_combination H.2 (by linear_combination h)

/-- A function on the box `{a | ∀ j, |a j| ≤ L j}` which vanishes at `0` and satisfies
`g a + g b = g c + g d` whenever `a + b = c + d` inside the box is linear on the box. -/
private lemma pull_box_linear {m : ℕ} (L : Fin m → ℕ) (g : (Fin m → ℤ) → ℤ) (h0 : g 0 = 0)
    (hadd : ∀ a b c d : Fin m → ℤ, (∀ j, |a j| ≤ L j) → (∀ j, |b j| ≤ L j) →
      (∀ j, |c j| ≤ L j) → (∀ j, |d j| ≤ L j) → a + b = c + d → g a + g b = g c + g d)
    (a : Fin m → ℤ) (ha : ∀ j, |a j| ≤ L j) :
    g a = ∑ j, a j * g (Pi.single j 1) := by
  have hz : ∀ j, |(0 : Fin m → ℤ) j| ≤ L j := fun j => by simp
  -- induction on `∑ j, (a j).natAbs`
  suffices H : ∀ n : ℕ, ∀ a : Fin m → ℤ, (∀ j, |a j| ≤ L j) → ∑ j, (a j).natAbs = n →
      g a = ∑ j, a j * g (Pi.single j 1) from H _ a ha rfl
  intro n
  induction n with
  | zero =>
    intro a ha hn
    obtain rfl : a = 0 := by
      funext j
      simpa using (Finset.sum_eq_zero_iff.mp hn) j (mem_univ j)
    simp [h0]
  | succ n ih =>
    intro a ha hn
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
      by_contra! h
      simp [h] at hn
    -- `Pi.single j 1` lies in the box since `1 ≤ |a j| ≤ L j`
    have hL : 1 ≤ (L j : ℤ) := (Int.one_le_abs hj).trans (ha j)
    have he : ∀ i, |(Pi.single j 1 : Fin m → ℤ) i| ≤ L i := by
      intro i
      rcases eq_or_ne i j with rfl | hi
      · simpa using hL
      · simp [hi]
    -- the case `0 < b j`, via `b + 0 = (b - Pi.single j 1) + Pi.single j 1`
    have key : ∀ b : Fin m → ℤ, (∀ i, |b i| ≤ L i) → ∑ i, (b i).natAbs = n + 1 → 0 < b j →
        g b = ∑ i, b i * g (Pi.single i 1) := by
      intro b hb hbn hbj
      have hb' : ∀ i, |(b - Pi.single j 1 : Fin m → ℤ) i| ≤ L i := by
        intro i
        rcases eq_or_ne i j with rfl | hi
        · have := abs_le.mp (hb i)
          rw [abs_le, Pi.sub_apply, Pi.single_eq_same]
          constructor <;> omega
        · simpa [hi] using hb i
      have hbn' : ∑ i, ((b - Pi.single j 1 : Fin m → ℤ) i).natAbs = n := by
        have : ∀ i, (b i).natAbs =
            ((b - Pi.single j 1 : Fin m → ℤ) i).natAbs + (Pi.single j 1 : Fin m → ℕ) i := by
          intro i
          rcases eq_or_ne i j with rfl | hi
          · rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_same]
            omega
          · simp [hi]
        simpa [this, Finset.sum_add_distrib] using hbn
      have h := hadd b 0 _ _ hb hz hb' he (by simp)
      rw [ih _ hb' hbn', h0] at h
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte] at h
      linarith
    rcases hj.lt_or_gt with hneg | hpos
    · -- `a j < 0`: apply `key` to `-a` and use `g a + g (-a) = g 0 + g 0`
      have hna : ∀ i, |(-a) i| ≤ L i := by simpa using ha
      have h₁ := key (-a) hna (by simpa using hn) (by simpa using hneg)
      have h₂ := hadd a (-a) 0 0 ha hna hz hz (by simp)
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at h₁
      linarith
    · exact key a ha hn hpos

/-- A proper progression inside `2φ(A') - 2φ(A')`, for a Freiman isomorphism `φ` of order `8`
on `A'`, pulls back to a proper progression with the same lengths inside `2A' - 2A'`. -/
private theorem pullback {N : ℕ} [NeZero N] (A' : Finset ℤ) (hA' : A'.Nonempty) (φ : ℤ → ZMod N)
    (hφ : ∀ x y : Fin 8 → ℤ, (∀ i, x i ∈ A') → (∀ i, y i ∈ A') →
      (∑ i, x i = ∑ i, y i ↔ ∑ i, φ (x i) = ∑ i, φ (y i)))
    {m : ℕ} (w : Fin m → ZMod N) (L : Fin m → ℕ)
    (hw : ∀ a b : Fin m → ℤ, (∀ j, |a j| ≤ L j) → (∀ j, |b j| ≤ L j) →
      ∑ j, (a j : ZMod N) * w j = ∑ j, (b j : ZMod N) * w j → a = b)
    (hsub : ∀ a : Fin m → ℤ, (∀ j, |a j| ≤ L j) →
      ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
        ∑ j, (a j : ZMod N) * w j = φ b₁ + φ b₂ - φ b₃ - φ b₄) :
    ∃ v : Fin m → ℤ,
      (∀ a b : Fin m → ℤ, (∀ j, |a j| ≤ L j) → (∀ j, |b j| ≤ L j) →
        ∑ j, a j * v j = ∑ j, b j * v j → a = b) ∧
      (∀ a : Fin m → ℤ, (∀ j, |a j| ≤ L j) →
        ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A', ∑ j, a j * v j = b₁ + b₂ - b₃ - b₄) := by
  obtain ⟨a₀, ha₀⟩ := hA'
  -- choose an integer lift `g a ∈ 2A' - 2A'` of every point `a` of the box
  have hex : ∀ a : Fin m → ℤ, ∃ t : ℤ, (∀ j, |a j| ≤ L j) →
      ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
        t = b₁ + b₂ - b₃ - b₄ ∧ ∑ j, (a j : ZMod N) * w j = φ b₁ + φ b₂ - φ b₃ - φ b₄ := by
    intro a
    by_cases ha : ∀ j, |a j| ≤ L j
    · obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, h⟩ := hsub a ha
      exact ⟨b₁ + b₂ - b₃ - b₄, fun _ => ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, rfl, h⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose g hg using hex
  -- `0 = a₀ + a₀ - a₀ - a₀` is a lift of `0`
  have hzero : ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
      (0 : ℤ) = b₁ + b₂ - b₃ - b₄ ∧ (0 : ZMod N) = φ b₁ + φ b₂ - φ b₃ - φ b₄ :=
    ⟨a₀, ha₀, a₀, ha₀, a₀, ha₀, a₀, ha₀, by ring, by ring⟩
  have hz : ∀ j, |(0 : Fin m → ℤ) j| ≤ L j := fun j => by simp
  have hg0 : g 0 = 0 := by
    simpa using (pull_key hφ (hg 0 hz) hzero hzero hzero).2 (by simp)
  have hW : ∀ a b : Fin m → ℤ, ∑ j, ((a + b) j : ZMod N) * w j =
      ∑ j, (a j : ZMod N) * w j + ∑ j, (b j : ZMod N) * w j := by
    intro a b
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  have hadd : ∀ a b c d : Fin m → ℤ, (∀ j, |a j| ≤ L j) → (∀ j, |b j| ≤ L j) →
      (∀ j, |c j| ≤ L j) → (∀ j, |d j| ≤ L j) → a + b = c + d → g a + g b = g c + g d := by
    intro a b c d ha hb hc hd habcd
    refine (pull_key hφ (hg a ha) (hg b hb) (hg c hc) (hg d hd)).2 ?_
    rw [← hW, ← hW, habcd]
  have hlin := pull_box_linear L g hg0 hadd
  refine ⟨fun j => g (Pi.single j 1), ?_, ?_⟩
  · intro a b ha hb hab
    rw [← hlin a ha, ← hlin b hb] at hab
    apply hw a b ha hb
    simpa using (pull_key hφ (hg a ha) hzero (hg b hb) hzero).1 (by rw [hab])
  · intro a ha
    obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, h, -⟩ := hg a ha
    exact ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, by rw [← hlin a ha, h]⟩

/-! ## Proof of Freiman's theorem -/

/-- Plünnecke–Ruzsa in the form used below. -/
private theorem freiman_pluennecke {A : Finset ℤ} (hA : A.Nonempty) {C : ℝ}
    (hAC : ((A + A).card : ℝ) ≤ C * A.card) (m n : ℕ) :
    ((m • A - n • A).card : ℝ) ≤ C ^ (m + n) * A.card := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA A m n
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have h' : ((m • A - n • A).card : ℝ) ≤ (((A + A).card : ℝ) / A.card) ^ (m + n) * A.card := by
    have := (NNRat.cast_le (K := ℝ)).mpr h
    simpa using this
  have hq : ((A + A).card : ℝ) / A.card ≤ C := by rwa [div_le_iff₀ hA0]
  calc ((m • A - n • A).card : ℝ) ≤ (((A + A).card : ℝ) / A.card) ^ (m + n) * A.card := h'
    _ ≤ C ^ (m + n) * A.card := by gcongr

/-- A sum of `n` elements of `A` lies in `n • A`. -/
private theorem freiman_sum_mem_nsmul {A : Finset ℤ} {n : ℕ} (x : Fin n → ℤ)
    (hx : ∀ i, x i ∈ A) : ∑ i, x i ∈ n • A := by
  rw [Finset.mem_nsmul]
  exact ⟨fun i => ⟨x i, hx i⟩, by simp [List.sum_ofFn]⟩

private theorem freiman_three_mem {A : Finset ℤ} {a b c : ℤ} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) : a + b + c ∈ 3 • A := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  exact add_mem_add (add_mem_add ha hb) hc

private theorem freiman_two_mem {A : Finset ℤ} {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) :
    a + b ∈ 2 • A := by
  rw [two_nsmul]
  exact add_mem_add ha hb

/-- Converting a covering by translates of a symmetric progression into the shape of the
statement. -/
private theorem freiman_format {m : ℕ} (v : Fin m → ℤ) (L : Fin m → ℕ) (X : Finset ℤ)
    (hX : X.Nonempty) (A : Finset ℤ)
    (hcover : ∀ a ∈ A, ∃ x ∈ X, ∃ g : Fin m → ℤ, (∀ j, |g j| ≤ 2 * (L j : ℤ)) ∧
      a = x + ∑ j, g j * v j) :
    ∃ (x₀ : ℤ) (x : Fin (X.card + m) → ℤ) (k : Fin (X.card + m) → ℕ),
      (∀ i, 0 < x i) ∧ (∀ i, 0 < k i) ∧
      (∏ i, k i) ≤ 2 ^ (X.card + m) * ∏ j, (2 * L j + 1) ∧
      ∀ a ∈ A, ∃ c : Fin (X.card + m) → ℕ, (∀ i, c i < k i) ∧
        a = x₀ + ∑ i, (c i : ℤ) * x i := by
  classical
  set μ := X.min' hX with hμ
  let e : Fin X.card ≃ X := X.equivFin.symm
  let gX : Fin X.card → ℤ := fun i => (e i : ℤ) - μ + 1
  let h : Fin m → ℤ := fun j => if v j = 0 then 1 else |v j|
  refine ⟨μ - 1 - ∑ j, 2 * (L j : ℤ) * |v j|, Fin.append gX h,
    Fin.append (fun _ => 2) (fun j => 4 * L j + 1), ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      have : μ ≤ (e i : ℤ) := X.min'_le _ (e i).2
      simp only [gX]
      omega
    · rw [Fin.append_right]
      simp only [h]
      split_ifs with hv
      · exact one_pos
      · exact abs_pos.mpr hv
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp
    · simp
  · rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, pow_add, mul_assoc]
    gcongr
    calc ∏ j, (4 * L j + 1) ≤ ∏ j : Fin m, (2 * (2 * L j + 1)) :=
          Finset.prod_le_prod fun j _ => by omega
      _ = 2 ^ m * ∏ j, (2 * L j + 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro a ha
    obtain ⟨x, hx, g, hg, rfl⟩ := hcover a ha
    let i₀ : Fin X.card := e.symm ⟨x, hx⟩
    have hi₀ : (e i₀ : ℤ) = x := by simp [i₀]
    refine ⟨Fin.append (fun i => if (e i : ℤ) = x then 1 else 0)
      (fun j => if v j = 0 then 0 else (2 * (L j : ℤ) + g j * Int.sign (v j)).toNat), ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        split_ifs <;> omega
      · simp only [Fin.append_right]
        split_ifs with hv
        · omega
        · have hgj := hg j
          have hs : |g j * Int.sign (v j)| ≤ 2 * (L j : ℤ) := by
            rw [abs_mul]
            rcases Int.sign_trichotomy (v j) with h1 | h1 | h1 <;> simp [h1, hgj]
          have := abs_le.mp hs
          omega
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      have h1 : ∑ i : Fin X.card, ((if (e i : ℤ) = x then 1 else 0 : ℕ) : ℤ) * gX i
          = x - μ + 1 := by
        rw [Finset.sum_eq_single i₀]
        · simp [hi₀, gX]
        · intro b _ hb
          have : (e b : ℤ) ≠ x := by
            intro hbx
            apply hb
            apply e.injective
            apply Subtype.ext
            simp [i₀, hbx]
          simp [this]
        · simp
      have h2 : ∀ j, (((if v j = 0 then 0 else (2 * (L j : ℤ) + g j * Int.sign (v j)).toNat :
          ℕ) : ℤ)) * h j = 2 * (L j : ℤ) * |v j| + g j * v j := by
        intro j
        by_cases hv : v j = 0
        · simp [hv]
        · have hnn : 0 ≤ 2 * (L j : ℤ) + g j * Int.sign (v j) := by
            have hgj := hg j
            have hs : |g j * Int.sign (v j)| ≤ 2 * (L j : ℤ) := by
              rw [abs_mul]
              rcases Int.sign_trichotomy (v j) with h1 | h1 | h1 <;> simp [h1, hgj]
            have := abs_le.mp hs
            omega
          simp only [hv, ite_false, h, Int.toNat_of_nonneg hnn]
          have := Int.sign_mul_abs (v j)
          linear_combination g j * this
      rw [h1, Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_add_distrib]
      ring

/-- **Freiman's theorem.** For every constant `C` there are `d₀` and `K` such that every
nonempty finite `A ⊆ ℤ` with `|A + A| ≤ C|A|` lies in a `d`-dimensional arithmetic progression
`{x₀ + ∑ aᵢ xᵢ : 0 ≤ aᵢ < kᵢ}` with `d ≤ d₀`, positive integers `xᵢ, kᵢ` and size
`k₁ ⋯ k_d ≤ K|A|`: Theorem 7.1 of Gowers [G01] (Freiman's theorem, with Ruzsa's proof). The
nonemptiness hypothesis is implicit there (`|A| = m` and the size bound `≤ Km` fail for
`A = ∅`). -/
public theorem freiman (C : ℝ) :
    ∃ (d₀ : ℕ) (K : ℝ), ∀ A : Finset ℤ, A.Nonempty → ((A + A).card : ℝ) ≤ C * A.card →
      ∃ (d : ℕ) (x₀ : ℤ) (x : Fin d → ℤ) (k : Fin d → ℕ),
        d ≤ d₀ ∧ (∀ i, 0 < x i) ∧ (∀ i, 0 < k i) ∧ ((∏ i, k i : ℕ) : ℝ) ≤ K * A.card ∧
        ∀ a ∈ A, ∃ c : Fin d → ℕ, (∀ i, c i < k i) ∧ a = x₀ + ∑ i, (c i : ℤ) * x i := by
  classical
  set C' := max C 1 with hC'
  set D₀ : ℕ := ⌊1024 * C' ^ 32⌋₊ with hD₀
  obtain ⟨κ, hκ, hbohr⟩ := bohr_progression D₀
  set d₀ : ℕ := ⌊8 * C' ^ 5 / κ⌋₊ + 2 ^ D₀ with hd₀
  refine ⟨d₀, 2 ^ d₀ * C' ^ 4, ?_⟩
  intro A hA hAC
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  -- `C ≥ 1` because `|A| ≤ |A + A|`.
  have hC1 : 1 ≤ C := by
    have h1 : (A.card : ℝ) ≤ (A + A).card := by exact_mod_cast Finset.card_le_card_add_left hA
    nlinarith
  have hCC' : C' = C := max_eq_left hC1
  have hpl := freiman_pluennecke hA hAC
  -- Step 1: a cyclic model of a large part of `A`.
  set D := 8 • A - 8 • A with hDdef
  have hD : ∀ x y : Fin 8 → ℤ, (∀ i, x i ∈ A) → (∀ i, y i ∈ A) → ∑ i, x i - ∑ i, y i ∈ D :=
    fun x y hx hy => sub_mem_sub (freiman_sum_mem_nsmul x hx) (freiman_sum_mem_nsmul y hy)
  obtain ⟨N, hN0, hND, φ, A', hA'A, hA'card, hφ⟩ := modelling A D hA hD
  have : NeZero N := ⟨hN0.ne'⟩
  have hDcard : (D.card : ℝ) ≤ C ^ 16 * A.card := hpl 8 8
  have hA'card' : (A.card : ℝ) ≤ 8 * A'.card := by exact_mod_cast hA'card
  have hA'ne : A'.Nonempty := by
    rw [← Finset.card_pos]
    have : 0 < A.card := hA.card_pos
    omega
  obtain ⟨a₀, ha₀⟩ := hA'ne
  -- `φ` is injective on `A'`.
  have hinj : Set.InjOn φ A' := by
    intro a ha b hb hab
    let x : Fin 8 → ℤ := fun i => if i = 0 then a else a₀
    let y : Fin 8 → ℤ := fun i => if i = 0 then b else a₀
    have hx : ∀ i, x i ∈ A' := fun i => by simp only [x]; split_ifs <;> assumption
    have hy : ∀ i, y i ∈ A' := fun i => by simp only [y]; split_ifs <;> assumption
    have := (hφ x y hx hy).mpr (by simp [x, y, Fin.sum_univ_succ, hab])
    simpa [x, y, Fin.sum_univ_succ] using this
  set B := A'.image φ with hBdef
  have hBcard : B.card = A'.card := Finset.card_image_of_injOn hinj
  have hBne : B.Nonempty := ⟨φ a₀, Finset.mem_image_of_mem φ ha₀⟩
  have hBN : (B.card : ℝ) ≤ N := by
    have := Finset.card_le_univ B
    simp only [ZMod.card] at this
    exact_mod_cast this
  -- Step 2: Bogolyubov's lemma in the model.
  obtain ⟨Γ, hΓcard, hΓ⟩ := bogolyubov B hBne
  have hΓD₀ : Γ.card ≤ D₀ := by
    apply Nat.le_floor
    have hN4 : (N : ℝ) ≤ 4 * (C ^ 16 * A.card) := by
      have : (N : ℝ) ≤ 4 * D.card := by exact_mod_cast hND
      linarith
    have hAB : (A.card : ℝ) ≤ 8 * B.card := by rw [hBcard]; exact hA'card'
    have hΓ0 : (0 : ℝ) ≤ Γ.card := Nat.cast_nonneg _
    have hC0 : (0 : ℝ) ≤ C ^ 16 := by positivity
    have hkey : (Γ.card : ℝ) * (A.card : ℝ) ^ 2 ≤ 1024 * C ^ 32 * (A.card : ℝ) ^ 2 := by
      calc (Γ.card : ℝ) * (A.card : ℝ) ^ 2 ≤ Γ.card * (8 * B.card) ^ 2 := by
            gcongr
        _ = 64 * (Γ.card * (B.card : ℝ) ^ 2) := by ring
        _ ≤ 64 * (N : ℝ) ^ 2 := by gcongr
        _ ≤ 64 * (4 * (C ^ 16 * A.card)) ^ 2 := by
            gcongr
        _ = 1024 * C ^ 32 * (A.card : ℝ) ^ 2 := by ring
    rw [hCC']
    exact le_of_mul_le_mul_right hkey (by positivity)
  -- Step 3: a large proper progression in the Bohr set.
  obtain ⟨m, w, L, hm, hw, hwBohr, hsize⟩ := hbohr N Γ hΓD₀
  have hsub : ∀ a : Fin m → ℤ, (∀ j, |a j| ≤ L j) →
      ∃ b₁ ∈ A', ∃ b₂ ∈ A', ∃ b₃ ∈ A', ∃ b₄ ∈ A',
        ∑ j, (a j : ZMod N) * w j = φ b₁ + φ b₂ - φ b₃ - φ b₄ := by
    intro a ha
    obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, c₄, hc₄, hc⟩ := hΓ _ (hwBohr a ha)
    obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp hc₁
    obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.mp hc₂
    obtain ⟨b₃, hb₃, rfl⟩ := Finset.mem_image.mp hc₃
    obtain ⟨b₄, hb₄, rfl⟩ := Finset.mem_image.mp hc₄
    exact ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, hc⟩
  -- Step 4: pull the progression back to `2A - 2A`.
  obtain ⟨v, hv, hvsub⟩ := pullback A' ⟨a₀, ha₀⟩ φ hφ w L hw hsub
  let box : Finset (Fin m → ℤ) := Fintype.piFinset fun j => Finset.Icc (-(L j : ℤ)) (L j)
  have hmembox : ∀ a, a ∈ box ↔ ∀ j, |a j| ≤ L j := by
    intro a
    simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  set P := box.image fun a => ∑ j, a j * v j with hPdef
  have hPcard : (P.card : ℝ) = ∏ j, (2 * L j + 1 : ℝ) := by
    rw [Finset.card_image_of_injOn]
    · simp only [box, Fintype.card_piFinset, Int.card_Icc]
      push_cast
      refine Finset.prod_congr rfl fun j _ => ?_
      have : ((L j : ℤ) + 1 - -(L j : ℤ)).toNat = 2 * L j + 1 := by omega
      rw [this]
      push_cast
      ring
    · intro a ha b hb hab
      exact hv a b ((hmembox a).mp ha) ((hmembox b).mp hb) hab
  have hPsub : P ⊆ 2 • A - 2 • A := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, hb⟩ := hvsub a ((hmembox a).mp ha)
    rw [hb, sub_sub]
    exact sub_mem_sub (freiman_two_mem (hA'A hb₁) (hA'A hb₂))
      (freiman_two_mem (hA'A hb₃) (hA'A hb₄))
  have hPne : P.Nonempty := by
    refine ⟨∑ j, (0 : Fin m → ℤ) j * v j, Finset.mem_image_of_mem _ ?_⟩
    rw [hmembox]
    intro j
    simp
  have hPupper : (P.card : ℝ) ≤ C ^ 4 * A.card := by
    have := hpl 2 2
    calc (P.card : ℝ) ≤ (2 • A - 2 • A).card := by exact_mod_cast Finset.card_le_card hPsub
      _ ≤ C ^ (2 + 2) * A.card := this
  have hPlower : κ * A.card ≤ 8 * P.card := by
    rw [hPcard]
    calc κ * A.card ≤ κ * (8 * B.card) := by
          gcongr
          rw [hBcard]
          exact hA'card'
      _ = 8 * (κ * B.card) := by ring
      _ ≤ 8 * (κ * N) := by gcongr
      _ ≤ 8 * ∏ j, (2 * L j + 1 : ℝ) := by gcongr
  -- Step 5: Ruzsa's covering lemma.
  have hAP : A + P ⊆ 3 • A - 2 • A := by
    intro z hz
    obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_sub.mp (hPsub hp)
    rw [two_nsmul] at hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Finset.mem_add.mp hs
    rw [← add_sub_assoc, ← add_assoc]
    exact sub_mem_sub (freiman_three_mem ha hs₁ hs₂) ht
  have hAPcard : ((A + P).card : ℝ) ≤ 8 * C ^ 5 / κ * P.card := by
    have h3 := hpl 3 2
    calc ((A + P).card : ℝ) ≤ (3 • A - 2 • A).card := by
          exact_mod_cast Finset.card_le_card hAP
      _ ≤ C ^ (3 + 2) * A.card := h3
      _ ≤ 8 * C ^ 5 / κ * P.card := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
          have hC5 : (0 : ℝ) ≤ C ^ 5 := by positivity
          have := mul_le_mul_of_nonneg_left hPlower hC5
          norm_num at this ⊢
          linarith
  obtain ⟨X, hXA, hXcard, hcov⟩ := Finset.ruzsa_covering_add hPne hAPcard
  have hXne : X.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨x, hx, -, -, -⟩ := Finset.mem_add.mp (hcov ha)
    exact ⟨x, hx⟩
  have hcover : ∀ a ∈ A, ∃ x ∈ X, ∃ g : Fin m → ℤ, (∀ j, |g j| ≤ 2 * (L j : ℤ)) ∧
      a = x + ∑ j, g j * v j := by
    intro a ha
    obtain ⟨x, hx, q, hq, rfl⟩ := Finset.mem_add.mp (hcov ha)
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Finset.mem_sub.mp hq
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hp₁
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hp₂
    refine ⟨x, hx, α - β, fun j => ?_, ?_⟩
    · have h1 := (hmembox α).mp hα j
      have h2 := (hmembox β).mp hβ j
      simp only [Pi.sub_apply]
      calc |α j - β j| ≤ |α j| + |β j| := abs_sub _ _
        _ ≤ L j + L j := add_le_add h1 h2
        _ = 2 * (L j : ℤ) := by ring
    · simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  -- Step 6: the final progression.
  obtain ⟨x₀, x, k, hxpos, hkpos, hprod, hrep⟩ := freiman_format v L X hXne A hcover
  have hXle : X.card ≤ ⌊8 * C' ^ 5 / κ⌋₊ := by
    apply Nat.le_floor
    rw [hCC']
    exact hXcard
  have hdle : X.card + m ≤ d₀ := by
    rw [hd₀]
    omega
  refine ⟨X.card + m, x₀, x, k, hdle, hxpos, hkpos, ?_, hrep⟩
  have hprod' : ((∏ i, k i : ℕ) : ℝ) ≤ 2 ^ (X.card + m) * ∏ j, (2 * L j + 1 : ℝ) := by
    exact_mod_cast hprod
  calc ((∏ i, k i : ℕ) : ℝ) ≤ 2 ^ (X.card + m) * ∏ j, (2 * L j + 1 : ℝ) := hprod'
    _ ≤ 2 ^ d₀ * (C ^ 4 * A.card) := by
        rw [← hPcard]
        gcongr
        · norm_num
    _ = 2 ^ d₀ * C' ^ 4 * A.card := by rw [hCC']; ring

end MathlibExt.Combinatorics.Additive.FreimanBSGWanted
