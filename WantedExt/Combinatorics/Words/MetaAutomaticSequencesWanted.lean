/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import MathlibExt.Combinatorics.Words.CobhamUniformMorphism
public import MathlibExt.Combinatorics.Words.RegularSequence

namespace MetaMathlibExt

open Filter Asymptotics

@[expose] public section

/-- The Thue–Morse Quarto sequence `𝒬 : ℕ → {0, 1}` (OEIS A298952 with `𝒬(0) = 0`),
valued in `Bool`: `𝒬(0) = 0`, `𝒬(1) = 1`, `𝒬(4n) = 𝒬(n)`, `𝒬(4n+1) = 1 - 𝒬(n)`,
`𝒬(4n+2) = 𝒬(2n)`, `𝒬(4n+3) = 1 - 𝒬(2n)`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2 (definition of `𝒬`). -/
public def thueMorseQuarto : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => thueMorseQuarto ((n + 2) / 4)
    | 1 => !thueMorseQuarto ((n + 2) / 4)
    | 2 => thueMorseQuarto (2 * ((n + 2) / 4))
    | _ => !thueMorseQuarto (2 * ((n + 2) / 4))
termination_by n => n
decreasing_by all_goals omega

/-- The meta-automatic sequence `ℳ₁` (OEIS A392736), valued in `Bool`: `ℳ₁(0) = 0`,
`ℳ₁(1) = 1`, `ℳ₁(4n) = ℳ₁(n)` and `ℳ₁(4n+1) = 1 - ℳ₁(n)` for `n ≥ 1`, and
`ℳ₁(4n+2) = ℳ₁(2n + 1 - ℳ₁(n))`, `ℳ₁(4n+3) = 1 - ℳ₁(2n + 1 - ℳ₁(n))` for `n ≥ 0`.
The nested index is written as a case split on `ℳ₁(n)`; the paper's recurrences are
`metaAutomaticOne_rec` below.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3 (definition of `ℳ₁`). -/
public def metaAutomaticOne : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => metaAutomaticOne ((n + 2) / 4)
    | 1 => !metaAutomaticOne ((n + 2) / 4)
    | 2 => if metaAutomaticOne ((n + 2) / 4) then metaAutomaticOne (2 * ((n + 2) / 4))
        else metaAutomaticOne (2 * ((n + 2) / 4) + 1)
    | _ => !(if metaAutomaticOne ((n + 2) / 4) then metaAutomaticOne (2 * ((n + 2) / 4))
        else metaAutomaticOne (2 * ((n + 2) / 4) + 1))
termination_by n => n
decreasing_by all_goals omega

/-- The meta-automatic sequence `ℳ₂` (OEIS A391614), valued in `Bool`: `ℳ₂(0) = 0`,
`ℳ₂(1) = 1`, `ℳ₂(4n) = ℳ₂(2n + ℳ₂(n))` and `ℳ₂(4n+1) = 1 - ℳ₂(4n)` for `n ≥ 1`, and
`ℳ₂(4n+2) = ℳ₂(2n + 1 - ℳ₂(n))`, `ℳ₂(4n+3) = 1 - ℳ₂(4n+2)` for `n ≥ 0`. The nested
indices are written as case splits on `ℳ₂(n)`; the paper's recurrences are
`metaAutomaticTwo_rec` below.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4 (definition of `ℳ₂`). -/
public def metaAutomaticTwo : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4) + 1)
        else metaAutomaticTwo (2 * ((n + 2) / 4))
    | 1 => !(if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4) + 1)
        else metaAutomaticTwo (2 * ((n + 2) / 4)))
    | 2 => if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4))
        else metaAutomaticTwo (2 * ((n + 2) / 4) + 1)
    | _ => !(if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4))
        else metaAutomaticTwo (2 * ((n + 2) / 4) + 1))
termination_by n => n
decreasing_by all_goals omega

/-- First sixteen values of `𝒬`: `0101100101101001`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2. -/
public theorem thueMorseQuarto_small : (List.range 16).map thueMorseQuarto =
    [false, true, false, true, true, false, false, true, false, true, true, false, true,
      false, false, true] := by
  simp [List.range_succ, thueMorseQuarto]

/-- First sixteen values of `ℳ₁`: `0110101010100101`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3. -/
public theorem metaAutomaticOne_small : (List.range 16).map metaAutomaticOne =
    [false, true, true, false, true, false, true, false, true, false, true, false, false,
      true, false, true] := by
  simp [List.range_succ, metaAutomaticOne]

/-- First sixteen values of `ℳ₂`: `0110011010011001`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4. -/
public theorem metaAutomaticTwo_small : (List.range 16).map metaAutomaticTwo =
    [false, true, true, false, false, true, true, false, true, false, false, true, true,
      false, false, true] := by
  simp [List.range_succ, metaAutomaticTwo]

/-- The recurrences of `𝒬`: `𝒬(4n) = 𝒬(n)` and `𝒬(4n+1) = 1 - 𝒬(n)` for `n ≥ 1`,
`𝒬(4n+2) = 𝒬(2n)` and `𝒬(4n+3) = 1 - 𝒬(2n)` for `n ≥ 0`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2. -/
public theorem thueMorseQuarto_rec (n : ℕ) :
    (1 ≤ n → thueMorseQuarto (4 * n) = thueMorseQuarto n) ∧
      (1 ≤ n → thueMorseQuarto (4 * n + 1) = !thueMorseQuarto n) ∧
      thueMorseQuarto (4 * n + 2) = thueMorseQuarto (2 * n) ∧
      thueMorseQuarto (4 * n + 3) = !thueMorseQuarto (2 * n) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, thueMorseQuarto]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n + 1 = k + 2 := ⟨4 * n - 1, by omega⟩
    rw [hk, thueMorseQuarto]
    simp only [show (k + 2) % 4 = 1 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, thueMorseQuarto]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, thueMorseQuarto]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega]

/-- The recurrences of `ℳ₁` in the paper's form, with `ℳ₁(n)` read as `0` or `1`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3, equations (6) and (7). -/
public theorem metaAutomaticOne_rec (n : ℕ) :
    (1 ≤ n → metaAutomaticOne (4 * n) = metaAutomaticOne n) ∧
      (1 ≤ n → metaAutomaticOne (4 * n + 1) = !metaAutomaticOne n) ∧
      metaAutomaticOne (4 * n + 2) =
        metaAutomaticOne (2 * n + 1 - (metaAutomaticOne n).toNat) ∧
      metaAutomaticOne (4 * n + 3) =
        !metaAutomaticOne (2 * n + 1 - (metaAutomaticOne n).toNat) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, metaAutomaticOne]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n + 1 = k + 2 := ⟨4 * n - 1, by omega⟩
    rw [hk, metaAutomaticOne]
    simp only [show (k + 2) % 4 = 1 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, metaAutomaticOne]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
    cases metaAutomaticOne n <;> simp
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, metaAutomaticOne]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega]
    cases metaAutomaticOne n <;> simp

/-- The recurrences of `ℳ₂` in the paper's form, with `ℳ₂(n)` read as `0` or `1`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4, equations (9) and (10). -/
public theorem metaAutomaticTwo_rec (n : ℕ) :
    (1 ≤ n → metaAutomaticTwo (4 * n) =
        metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) ∧
      (1 ≤ n → metaAutomaticTwo (4 * n + 1) = !metaAutomaticTwo (4 * n)) ∧
      metaAutomaticTwo (4 * n + 2) =
        metaAutomaticTwo (2 * n + 1 - (metaAutomaticTwo n).toNat) ∧
      metaAutomaticTwo (4 * n + 3) = !metaAutomaticTwo (4 * n + 2) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, metaAutomaticTwo]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
    cases metaAutomaticTwo n <;> simp
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, show k + 2 + 1 = (k + 1) + 2 by omega, metaAutomaticTwo, metaAutomaticTwo]
    simp only [show (k + 1 + 2) % 4 = 1 by omega, show (k + 1 + 2) / 4 = n by omega,
      show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, metaAutomaticTwo]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
    cases metaAutomaticTwo n <;> simp
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, metaAutomaticTwo, metaAutomaticTwo]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega,
      show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]

/-- The right-special factors of length `n` of an infinite binary word `a`: the
length-`n` blocks `u` such that both `u0` and `u1` are factors of `a`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 5 (definition of `RS_a(n)`). -/
public def rightSpecialFactors (a : ℕ → Bool) (n : ℕ) : Set (Fin n → Bool) :=
  {u | ∀ b : Bool, (Fin.snoc (α := fun _ => Bool) u b) ∈ InfiniteWord.factorSet a (n + 1)}

/-- A constant word has no right-special factors.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 5. -/
public theorem rightSpecialFactors_const_false (n : ℕ) :
    rightSpecialFactors (fun _ => false) n = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hu
  obtain ⟨i, hi⟩ := hu true
  have := congrFun hi (Fin.last n)
  simp at this

/-- Theorem 2 (Allouche and Shallit, 2012): let `U` take values in a finite set `A`
and `q ≥ 2`. If there are `t, a, b, n₀` and functions `f_j` (`0 ≤ j < q^{t+1}`) with
`U(q^{t+1} n + j) = f_j(U(n-a), …, U(n+b), U(q^i n + j') for (i, j') ≠ (0, 0),
i ≤ t, j' < q^i)` for all `n ≥ n₀`, then `U` is `q`-automatic. The argument tuple is
indexed by `Fin (a + b + 1) ⊕ {(i, j')}` (the paper notes the ordering plays no role);
shifts use natural subtraction, so for `n < a` the first arguments are truncated
(harmless, since only `n ≥ max n₀ a` matters). Automaticity is
`IsKAutomaticSequence`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 2, quoting Allouche and Shallit
(2012), Theorem 2.2 (`jis-2026-26.4.1-thm-2`). -/
public theorem_wanted isKAutomaticSequence_of_digit_recurrence {A : Type} [Fintype A]
    (U : ℕ → A) (q : ℕ) (hq : 2 ≤ q) (t a b n₀ : ℕ)
    (f : ℕ → ((Fin (a + b + 1) ⊕
      {p : ℕ × ℕ // p.1 ≤ t ∧ p.2 < q ^ p.1 ∧ p ≠ (0, 0)}) → A) → A)
    (hf : ∀ n, n₀ ≤ n → ∀ j, j < q ^ (t + 1) →
      U (q ^ (t + 1) * n + j) =
        f j (Sum.elim (fun i => U (n + i - a)) (fun p => U (q ^ p.1.1 * n + p.1.2)))) :
    IsKAutomaticSequence q U

/-- Lemma 5: if `a : ℕ → {0, 1}` is balanced (`a(2n) + a(2n+1) = 1`), then
`a(2n + a(n)) = a(2n) ⊕ a(n)` and `a(2n + 1 - a(n)) = a(2n+1) ⊕ a(n)` for all `n`.
Values are `Bool`, `0`/`1` via `Bool.toNat`, and `⊕` is `xor`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 5 (`jis-2026-26.4.1-lem-5`). -/
public theorem_wanted balanced_nested_xor (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1) (n : ℕ) :
    a (2 * n + (a n).toNat) = xor (a (2 * n)) (a n) ∧
      a (2 * n + 1 - (a n).toNat) = xor (a (2 * n + 1)) (a n)

/-- Lemma 6: let `a : ℕ → {0, 1}` be balanced. (a) If `a(2n) = a(n + a(n))` for all `n`,
then `a(0) = 0` and `a(2n) = 0`, `a(2n+1) = 1` for `n ≥ 2`; (b) if
`a(2n) = a(n + 1 - a(n))` for all `n`, then `a(0) = 1` and `a(2n) = 1`, `a(2n+1) = 0`
for `n ≥ 2`. The ultimate 2-periodicity is the displayed formula.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 6 (`jis-2026-26.4.1-lem-6`). -/
public theorem_wanted balanced_dyadic_nested_eventually_periodic (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1) :
    ((∀ n, a (2 * n) = a (n + (a n).toNat)) →
        a 0 = false ∧ ∀ n, 2 ≤ n → a (2 * n) = false ∧ a (2 * n + 1) = true) ∧
      ((∀ n, a (2 * n) = a (n + 1 - (a n).toNat)) →
        a 0 = true ∧ ∀ n, 2 ≤ n → a (2 * n) = true ∧ a (2 * n + 1) = false)

/-- Proposition 8: `𝒬(n) = t(n) ⊕ d(n)` where `t` is the Thue–Morse sequence and
`d(0) = 0`, `d(n) = ⌊log₂ n⌋ mod 2` (here `Nat.log 2 0 = 0` gives `d(0) = 0`).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 8 (`jis-2026-26.4.1-prop-8`). -/
public theorem_wanted thueMorseQuarto_eq_xor (n : ℕ) :
    thueMorseQuarto n = xor (thueMorse n) (decide (Nat.log 2 n % 2 = 1))

/-- Lemma 10: `ℳ₁` is balanced, `ℳ₁(2n) + ℳ₁(2n+1) = 1`. Well-definedness is the
termination of the definition `metaAutomaticOne`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 10 (`jis-2026-26.4.1-lem-10`). -/
public theorem_wanted metaAutomaticOne_balanced (n : ℕ) :
    (metaAutomaticOne (2 * n)).toNat + (metaAutomaticOne (2 * n + 1)).toNat = 1

/-- Lemma 12: with `b(n) = ℳ₁(2n + 1 - ℳ₁(n))`, `s(n) = (ℳ₁(n), b(n))`, `x = ℳ₁(n)`,
`y = b(n)` and `n ≥ 1`: `s(4n) = (x, y)`, `s(4n+1) = (1 ⊕ x, x ⊕ y)`,
`s(4n+2) = (y, 1 ⊕ x)`, `s(4n+3) = (1 ⊕ y, x ⊕ y ⊕ 1)`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 12 (`jis-2026-26.4.1-lem-12`). -/
public theorem_wanted metaAutomaticOne_pair_closure (b : ℕ → Bool)
    (hb : ∀ m, b m = metaAutomaticOne (2 * m + 1 - (metaAutomaticOne m).toNat))
    (n : ℕ) (hn : 1 ≤ n) :
    (metaAutomaticOne (4 * n), b (4 * n)) = (metaAutomaticOne n, b n) ∧
      (metaAutomaticOne (4 * n + 1), b (4 * n + 1)) =
        (!metaAutomaticOne n, xor (metaAutomaticOne n) (b n)) ∧
      (metaAutomaticOne (4 * n + 2), b (4 * n + 2)) = (b n, !metaAutomaticOne n) ∧
      (metaAutomaticOne (4 * n + 3), b (4 * n + 3)) =
        (!b n, !xor (metaAutomaticOne n) (b n))

/-- Theorem 13: `ℳ₁` is `4`-automatic and is computed MSB-first in base `4` by the
DFAO with states `{0, 1, 2, 3}`, initial state `0`, output `τ(q) = q mod 2`, and
transitions `δ(0, ·) = 0112`, `δ(1, ·) = 1230`, `δ(2, ·) = 2301`, `δ(3, ·) = 3023`.
The run reads `(Nat.digits 4 n).reverse` (most significant digit first).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 13 (`jis-2026-26.4.1-thm-13`). -/
public theorem_wanted metaAutomaticOne_dfao :
    IsKAutomaticSequence 4 metaAutomaticOne ∧
      ∀ n, metaAutomaticOne n = decide (((Nat.digits 4 n).reverse.foldl
        (fun q d => ([[0, 1, 1, 2], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 2, 3]].getD q []).getD d 0)
        0) % 2 = 1)

/-- Corollary 16: `ℳ₁` is the coding `0, 2 ↦ 0`, `1, 3 ↦ 1` of the fixed point
starting from `0` of the `4`-uniform morphism `0 ↦ 0112`, `1 ↦ 1230`, `2 ↦ 2301`,
`3 ↦ 3023`. The fixed point is a word `w` with `w(0) = 0` and
`w(4n + r) = σ(w(n))_r`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Corollary 16 (`jis-2026-26.4.1-cor-16`). -/
public theorem_wanted metaAutomaticOne_morphism_coding :
    ∃ w : ℕ → ℕ, w 0 = 0 ∧
      (∀ n r, r < 4 → w (4 * n + r) =
        ([[0, 1, 1, 2], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 2, 3]].getD (w n) []).getD r 0) ∧
      ∀ n, metaAutomaticOne n = decide (w n % 2 = 1)

/-- Theorem 18: `ℳ₂` is balanced, `ℳ₂(2n) + ℳ₂(2n+1) = 1`. Well-definedness is the
termination of the definition `metaAutomaticTwo`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 18 (`jis-2026-26.4.1-thm-18`). -/
public theorem_wanted metaAutomaticTwo_balanced (n : ℕ) :
    (metaAutomaticTwo (2 * n)).toNat + (metaAutomaticTwo (2 * n + 1)).toNat = 1

/-- Lemma 19: with `s(n) = (x, y) = (ℳ₂(n), ℳ₂(2n + ℳ₂(n)))`,
`ℳ₂(2n) = x ⊕ y` and `ℳ₂(2n+1) = x ⊕ y ⊕ 1`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 19 (`jis-2026-26.4.1-lem-19`). -/
public theorem_wanted metaAutomaticTwo_recover (n : ℕ) :
    metaAutomaticTwo (2 * n) = xor (metaAutomaticTwo n)
        (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) ∧
      metaAutomaticTwo (2 * n + 1) = !xor (metaAutomaticTwo n)
        (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat))

/-- Theorem 20: with `s(n) = (x, y) = (ℳ₂(n), ℳ₂(2n + ℳ₂(n)))`, for all `n`:
`s(4n) = (y, x ⊕ y)`, `s(4n+1) = (y ⊕ 1, x ⊕ y)`, `s(4n+2) = (y ⊕ 1, x ⊕ y ⊕ 1)`,
`s(4n+3) = (y, x ⊕ y ⊕ 1)`; consequently `ℳ₂` is `4`-automatic with at most `4`
states, stated as `IsKAutomaticSequence 4` together with an MSB-first DFAO on
`Fin 4` with initial state `0`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 20 (`jis-2026-26.4.1-thm-20`). -/
public theorem_wanted metaAutomaticTwo_affine (s : ℕ → Bool × Bool)
    (hs : ∀ m, s m = (metaAutomaticTwo m,
      metaAutomaticTwo (2 * m + (metaAutomaticTwo m).toNat))) :
    (∀ n, s (4 * n) = ((s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 1) = (!(s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 2) = (!(s n).2, !xor (s n).1 (s n).2) ∧
      s (4 * n + 3) = ((s n).2, !xor (s n).1 (s n).2)) ∧
    IsKAutomaticSequence 4 metaAutomaticTwo ∧
    ∃ δ : Fin 4 → Fin 4 → Fin 4, ∃ τ : Fin 4 → Bool, ∀ n,
      metaAutomaticTwo n = τ ((Nat.digits 4 n).reverse.foldl (fun q d => δ q (Fin.ofNat 4 d)) 0)

/-- Theorem 22: `ℳ₂` is computed MSB-first in base `4` by the DFAO with states
`{0, 1, 2, 3}` (encoding `0 = (0,0)`, `1 = (1,0)`, `2 = (0,1)`, `3 = (1,1)`), initial
state `0`, output `τ(q) = q mod 2`, and transitions `δ(0, ·) = 0132`,
`δ(1, ·) = 2310`, `δ(2, ·) = 3201`, `δ(3, ·) = 1023`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 22 (`jis-2026-26.4.1-thm-22`). -/
public theorem_wanted metaAutomaticTwo_dfao (n : ℕ) :
    metaAutomaticTwo n = decide (((Nat.digits 4 n).reverse.foldl
      (fun q d => ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD q []).getD d 0)
      0) % 2 = 1)

/-- Corollary 23: `ℳ₂` is the coding `0, 2 ↦ 0`, `1, 3 ↦ 1` of the fixed point
starting from `0` of the `4`-uniform morphism `0 ↦ 0132`, `1 ↦ 2310`, `2 ↦ 3201`,
`3 ↦ 1023` (fixed point as in `metaAutomaticOne_morphism_coding`).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Corollary 23 (`jis-2026-26.4.1-cor-23`). -/
public theorem_wanted metaAutomaticTwo_morphism_coding :
    ∃ w : ℕ → ℕ, w 0 = 0 ∧
      (∀ n r, r < 4 → w (4 * n + r) =
        ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD (w n) []).getD r 0) ∧
      ∀ n, metaAutomaticTwo n = decide (w n % 2 = 1)

/-- Theorem 25: with base-`4` digits `d_k = ⌊n / 4^k⌋ mod 4 = 2 j_k + i_k`,
`ℳ₂(n) = ⊕_{k ≡ 0 (3)} (i_k ⊕ j_k) ⊕ ⊕_{k ≡ 1 (3)} j_k ⊕ ⊕_{k ≡ 2 (3)} i_k`, written as
the parity of a sum over `k ≤ n` (digits beyond the length of `n` vanish).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 25 (`jis-2026-26.4.1-thm-25`). -/
public theorem_wanted metaAutomaticTwo_digit_formula (n : ℕ) :
    metaAutomaticTwo n = decide ((∑ k ∈ Finset.range (n + 1),
      (if k % 3 = 0 then n / 4 ^ k % 4 % 2 + n / 4 ^ k % 4 / 2
        else if k % 3 = 1 then n / 4 ^ k % 4 / 2 else n / 4 ^ k % 4 % 2)) % 2 = 1)

/-- Theorem 26: with `q(n) = ∑_{m ≢ 2 (mod 3)} b_m 2^m` (zeroing the binary digits of
`n` in positions `m ≡ 2 (mod 3)`), `ℳ₂(n) = t(q(n))`; equivalently `q(n) = ∑ d'_k 4^k`
with `d'_k = d_k`, `2 j_k`, `i_k` for `k ≡ 0, 1, 2 (mod 3)`. `q` is given by a
hypothesis equation, sums run over positions `≤ n`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 26 (`jis-2026-26.4.1-thm-26`). -/
public theorem_wanted metaAutomaticTwo_eq_thueMorse_mask (q : ℕ → ℕ)
    (hq : ∀ m, q m = ∑ i ∈ (Finset.range (m + 1)).filter (fun i => i % 3 ≠ 2),
      m / 2 ^ i % 2 * 2 ^ i) (n : ℕ) :
    metaAutomaticTwo n = thueMorse (q n) ∧
      q n = ∑ k ∈ Finset.range (n + 1),
        (if k % 3 = 0 then n / 4 ^ k % 4
          else if k % 3 = 1 then 2 * (n / 4 ^ k % 4 / 2) else n / 4 ^ k % 4 % 2) * 4 ^ k

/-- Lemma 27: for every infinite binary word `a` and `n ≥ 1`,
`p_a(n+1) - p_a(n) = #RS_a(n)`, stated additively in `ℕ`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 27 (`jis-2026-26.4.1-lem-27`). -/
public theorem_wanted wordFactorComplexity_succ_eq_add_rightSpecial (a : ℕ → Bool) (n : ℕ)
    (hn : 1 ≤ n) :
    wordFactorComplexity a (n + 1) = wordFactorComplexity a n + (rightSpecialFactors a n).ncard

/-- Lemma 28: if `a` is `k`-automatic then `n ↦ #RS_a(n)` is `k`-regular, and if it is
bounded (by `C`) then it is `k`-automatic (as a `Fin (C + 1)`-valued sequence). The
clause "effectively computable from any DFAO for `a`" is an algorithmic claim and is
omitted.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 28 (`jis-2026-26.4.1-lem-28`). -/
public theorem_wanted rightSpecial_count_regular (k : ℕ) (a : ℕ → Bool)
    (ha : IsKAutomaticSequence k a) :
    IsKRegularSequence k (fun n => ((rightSpecialFactors a n).ncard : ℤ)) ∧
      ∀ C : ℕ, (∀ n, (rightSpecialFactors a n).ncard ≤ C) →
        IsKAutomaticSequence k (fun n => Fin.ofNat (C + 1) (rightSpecialFactors a n).ncard)

/-- Lemma 29: the factors of the Thue–Morse word are closed under bitwise complement.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 29 (`jis-2026-26.4.1-lem-29`). -/
public theorem_wanted thueMorse_factor_complement (n : ℕ) (v : Fin n → Bool)
    (hv : v ∈ InfiniteWord.factorSet thueMorse n) :
    (fun i => !v i) ∈ InfiniteWord.factorSet thueMorse n

/-- Proposition 30: with `J_n` the length-`n` factors of `𝒬` that are not factors of
`t`, `p_𝒬(n) = p_t(n) + |J_n|`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 30 (`jis-2026-26.4.1-prop-30`). -/
public theorem_wanted thueMorseQuarto_complexity_eq (n : ℕ) :
    wordFactorComplexity thueMorseQuarto n = wordFactorComplexity thueMorse n +
      (InfiniteWord.factorSet thueMorseQuarto n \ InfiniteWord.factorSet thueMorse n).ncard

/-- Theorem 31: for `k ≥ 4`, `p_𝒬(2^k) = 13 · 2^{k-2} - 2`, `p_𝒬(2^k) = p_t(2^k) + 2^{k-2}`,
and `|J_{2^k}| = 2^{k-2}`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 31 (`jis-2026-26.4.1-thm-31`). -/
public theorem_wanted thueMorseQuarto_complexity_two_pow (k : ℕ) (hk : 4 ≤ k) :
    wordFactorComplexity thueMorseQuarto (2 ^ k) = 13 * 2 ^ (k - 2) - 2 ∧
      wordFactorComplexity thueMorseQuarto (2 ^ k) =
        wordFactorComplexity thueMorse (2 ^ k) + 2 ^ (k - 2) ∧
      (InfiniteWord.factorSet thueMorseQuarto (2 ^ k) \
        InfiniteWord.factorSet thueMorse (2 ^ k)).ncard = 2 ^ (k - 2)

/-- Proposition 33: for `n ≥ 16`, `k = ⌊log₂ n⌋`, `n = 2^k + i`: `p_𝒬(n)` equals
`13 · 2^{k-2} - 2` (`i = 0`), `4n - 3 · 2^{k-2} - 4` (`1 ≤ i ≤ 2^{k-1}`),
`3n + 3 · 2^{k-2} - 3` (`2^{k-1} < i ≤ 3 · 2^{k-2}`), `2n + 5 · 2^{k-1} - 2`
(`3 · 2^{k-2} < i`); moreover `#RS_𝒬(n) = p_𝒬(n+1) - p_𝒬(n)`, which is `4` for
`n ∈ (2^k, 3 · 2^{k-1}]`, `3` for `n ∈ (3 · 2^{k-1}, 7 · 2^{k-2}]`, and `2` for
`n ∈ (7 · 2^{k-2}, 2^{k+1})`. Arithmetic in `ℤ`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 33 (`jis-2026-26.4.1-prop-33`). -/
public theorem_wanted thueMorseQuarto_complexity_formula (n : ℕ) (hn : 16 ≤ n) :
    (n = 2 ^ Nat.log 2 n →
        (wordFactorComplexity thueMorseQuarto n : ℤ) = 13 * 2 ^ (Nat.log 2 n - 2) - 2) ∧
      (2 ^ Nat.log 2 n < n ∧ n ≤ 2 ^ Nat.log 2 n + 2 ^ (Nat.log 2 n - 1) →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          4 * n - 3 * 2 ^ (Nat.log 2 n - 2) - 4) ∧
      (2 ^ Nat.log 2 n + 2 ^ (Nat.log 2 n - 1) < n ∧
          n ≤ 2 ^ Nat.log 2 n + 3 * 2 ^ (Nat.log 2 n - 2) →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          3 * n + 3 * 2 ^ (Nat.log 2 n - 2) - 3) ∧
      (2 ^ Nat.log 2 n + 3 * 2 ^ (Nat.log 2 n - 2) < n →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          2 * n + 5 * 2 ^ (Nat.log 2 n - 1) - 2) ∧
      ((rightSpecialFactors thueMorseQuarto n).ncard : ℤ) =
        wordFactorComplexity thueMorseQuarto (n + 1) - wordFactorComplexity thueMorseQuarto n ∧
      (2 ^ Nat.log 2 n < n ∧ n ≤ 3 * 2 ^ (Nat.log 2 n - 1) →
        (rightSpecialFactors thueMorseQuarto n).ncard = 4) ∧
      (3 * 2 ^ (Nat.log 2 n - 1) < n ∧ n ≤ 7 * 2 ^ (Nat.log 2 n - 2) →
        (rightSpecialFactors thueMorseQuarto n).ncard = 3) ∧
      (7 * 2 ^ (Nat.log 2 n - 2) < n → (rightSpecialFactors thueMorseQuarto n).ncard = 2)

/-- Proposition 34: `p_{ℳ₁}(n) = Θ(n)` and `p_{ℳ₂}(n) = Θ(n)`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 34 (`jis-2026-26.4.1-prop-34`). -/
public theorem_wanted metaAutomatic_complexity_isTheta :
    (fun n : ℕ => (wordFactorComplexity metaAutomaticOne n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ)) ∧
      (fun n : ℕ => (wordFactorComplexity metaAutomaticTwo n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ))

/-- Proposition 36: for `k ≥ 3`, `p_{ℳ₂}(2^k) = (5/2) · 2^k - 2` (written `5 · 2^{k-1} - 2`)
if `3 ∣ k` and `3 · 2^k - 2` otherwise; and `p_{ℳ₂}(2^{k+3}) = 8 p_{ℳ₂}(2^k) + 14`.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 36 (`jis-2026-26.4.1-prop-36`). -/
public theorem_wanted metaAutomaticTwo_complexity_two_pow (k : ℕ) (hk : 3 ≤ k) :
    (3 ∣ k → wordFactorComplexity metaAutomaticTwo (2 ^ k) = 5 * 2 ^ (k - 1) - 2) ∧
      (¬ 3 ∣ k → wordFactorComplexity metaAutomaticTwo (2 ^ k) = 3 * 2 ^ k - 2) ∧
      wordFactorComplexity metaAutomaticTwo (2 ^ (k + 3)) =
        8 * wordFactorComplexity metaAutomaticTwo (2 ^ k) + 14

/-- Proposition 37: `p_{ℳ₂}(1) = 2`, and for `n ≥ 2` with `k = ⌊log₂ n⌋`, `r = k mod 3`:
for `r = 0`, `p = 2n + 2^{k-1} - 2` (`n ≤ 2^k + 1`), `4n - (3 · 2^{k-1} + 4)`
(`2^k + 1 ≤ n ≤ 7 · 2^{k-2} + 1`), `2n + 2^{k+1} - 2` (`7 · 2^{k-2} + 1 ≤ n`); for
`r = 1`, `p = 2n + 2^k - 2` (`n ≤ 2^k + 1`), `4n - (2^k + 4)`
(`2^k + 1 ≤ n ≤ 3 · 2^{k-1} + 1`), `2n + 2^{k+1} - 2` (`3 · 2^{k-1} + 1 ≤ n`); for
`r = 2`, `p = 2n + 2^k - 2`. Arithmetic in `ℤ`; `2^k ≤ n < 2^{k+1}` is automatic.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 37 (`jis-2026-26.4.1-prop-37`). -/
public theorem_wanted metaAutomaticTwo_complexity_formula :
    wordFactorComplexity metaAutomaticTwo 1 = 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      (Nat.log 2 n % 3 = 0 →
        (n ≤ 2 ^ Nat.log 2 n + 1 → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n - 1) - 2)) ∧
        (2 ^ Nat.log 2 n + 1 ≤ n ∧ n ≤ 7 * 2 ^ (Nat.log 2 n - 2) + 1 →
          (wordFactorComplexity metaAutomaticTwo n : ℤ) =
            4 * n - (3 * 2 ^ (Nat.log 2 n - 1) + 4)) ∧
        (7 * 2 ^ (Nat.log 2 n - 2) + 1 ≤ n → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n + 1) - 2))) ∧
      (Nat.log 2 n % 3 = 1 →
        (n ≤ 2 ^ Nat.log 2 n + 1 → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ Nat.log 2 n - 2)) ∧
        (2 ^ Nat.log 2 n + 1 ≤ n ∧ n ≤ 3 * 2 ^ (Nat.log 2 n - 1) + 1 →
          (wordFactorComplexity metaAutomaticTwo n : ℤ) = 4 * n - (2 ^ Nat.log 2 n + 4)) ∧
        (3 * 2 ^ (Nat.log 2 n - 1) + 1 ≤ n → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n + 1) - 2))) ∧
      (Nat.log 2 n % 3 = 2 →
        (wordFactorComplexity metaAutomaticTwo n : ℤ) = 2 * n + (2 ^ Nat.log 2 n - 2))

end

end MetaMathlibExt
