/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generalized Beatty sequences and the Wythoff sequences

A generalized Beatty sequence has terms `p * ⌊nφ⌋ + q * n + r`. To compose it with
one of the Wythoff sequences, write `nφ = a + δ`, where `a = ⌊nφ⌋` and `0 < δ < 1`.
Then `aφ` is just below `a + n`, while `(a + n)φ` lies between `2a + n` and `2a + n + 1`.
-/

open scoped goldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Beatty sequence.** Let $\varphi$ be the golden ratio. For integers $p, q, r$, the
generalized Beatty sequence $V(p, q, r)$ is the integer sequence defined for every natural number
$n$, including $n = 0$, by $V(p, q, r)(n) = p\lfloor n\varphi \rfloor + qn + r$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
noncomputable def generalizedBeatty (p q r : ℤ) (n : ℕ) : ℤ :=
  p * ⌊(n : ℝ) * φ⌋ + q * n + r

/-- **Generalized Beatty sequence at zero.** Let $\varphi$ be the golden ratio. For all integers
$p, q, r$, the generalized Beatty sequence $V(p, q, r)(n) = p\lfloor n\varphi \rfloor + qn + r$
takes the value $V(p, q, r)(0) = r$ at $n = 0$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6 (`V₀`). -/
theorem generalizedBeatty_zero (p q r : ℤ) : generalizedBeatty p q r 0 = r := by
  simp [generalizedBeatty]

/-- **Generalized Beatty sequence at one.** Let $\varphi$ be the golden ratio. For all integers
$p, q, r$, the generalized Beatty sequence $V(p, q, r)(n) = p\lfloor n\varphi \rfloor + qn + r$
takes the value $V(p, q, r)(1) = p + q + r$ at $n = 1$, since $\lfloor \varphi \rfloor = 1$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
theorem generalizedBeatty_one (p q r : ℤ) : generalizedBeatty p q r 1 = p + q + r := by
  have h : ⌊φ⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using Real.one_lt_goldenRatio.le, by
      simpa [one_add_one_eq_two] using Real.goldenRatio_lt_two⟩
  simp [generalizedBeatty, h]

/-- **Generalized Beatty sequences composed with the Wythoff sequences.** Let $\varphi$ be the
golden ratio and, for integers $a$, $b$, $c$ and natural numbers $n$, let
$V(a, b, c)(n) = a \lfloor n\varphi \rfloor + bn + c$. Let $A(n) = \lfloor n\varphi \rfloor$ and
$B(n) = \lfloor n\varphi \rfloor + n$ be the lower and upper Wythoff sequences. For all integers
$p$, $q$, $r$ and every natural number $n \ge 1$,
$V(p, q, r)(A(n)) = V(p + q, p, r - p)(n)$ and $V(p, q, r)(B(n)) = V(2p + q, p + q, r)(n)$.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 3 (`integers-2024-A24-lem-3`). -/
public theorem generalizedBeatty_comp_wythoff (p q r : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    generalizedBeatty p q r ⌊(n : ℝ) * φ⌋₊ = generalizedBeatty (p + q) p (r - p) n ∧
      generalizedBeatty p q r (⌊(n : ℝ) * φ⌋₊ + n) =
        generalizedBeatty (2 * p + q) (p + q) r n := by
  let a : ℤ := ⌊(n : ℝ) * φ⌋
  let δ : ℝ := (n : ℝ) * φ - a
  have ha : (⌊(n : ℝ) * φ⌋₊ : ℤ) = a := Int.natCast_floor_eq_floor
    (mul_nonneg (Nat.cast_nonneg n) (zero_le_one.trans Real.one_lt_goldenRatio.le))
  have haℝ : (⌊(n : ℝ) * φ⌋₊ : ℝ) = a := by rw [← ha, Int.cast_natCast]
  have hirr : Irrational ((n : ℝ) * φ) := Real.goldenRatio_irrational.natCast_mul (by omega)
  have hlt : (a : ℝ) < (n : ℝ) * φ :=
    lt_of_le_of_ne (Int.floor_le _) (hirr.ne_int a).symm
  have hδ₀ : 0 < δ := sub_pos.mpr hlt
  have hδ₁ : δ < 1 := by
    dsimp only [δ]
    linarith only [Int.lt_floor_add_one ((n : ℝ) * φ)]
  have h₁ : 0 < φ - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have h₂ : 0 < 2 - φ := sub_pos.mpr Real.goldenRatio_lt_two
  have hlow₀ := mul_pos h₁ hδ₀
  have hlow₁ : (φ - 1) * δ < 1 := calc
    _ < (φ - 1) * 1 := mul_lt_mul_of_pos_left hδ₁ h₁
    _ < 1 := by linarith only [Real.goldenRatio_lt_two]
  have hhigh₀ := mul_pos h₂ hδ₀
  have hhigh₁ : (2 - φ) * δ < 1 := calc
    _ < (2 - φ) * 1 := mul_lt_mul_of_pos_left hδ₁ h₂
    _ < 1 := by linarith only [Real.one_lt_goldenRatio]
  have hprod := congrArg (fun x : ℝ => (n : ℝ) * x) Real.goldenRatio_sq
  have hlower : (a : ℝ) * φ = a + (n : ℝ) - (φ - 1) * δ := by
    dsimp only [δ]
    nlinarith only [hprod]
  have hupper : ((a : ℝ) + n) * φ = 2 * (a : ℝ) + (n : ℝ) + (2 - φ) * δ := by
    dsimp only [δ]
    nlinarith only [hprod]
  have lo : ⌊(a : ℝ) * φ⌋ = a + n - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨by linarith only [hlower, hlow₁], by linarith only [hlower, hlow₀]⟩
  have hi : ⌊((a : ℝ) + n) * φ⌋ = 2 * a + n := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨by linarith only [hupper, hhigh₀], by linarith only [hupper, hhigh₁]⟩
  constructor
  · simp only [generalizedBeatty, haℝ, lo, ha]
    change p * (a + n - 1) + q * a + r = (p + q) * a + p * n + (r - p)
    ring
  · simp only [generalizedBeatty, Nat.cast_add, haℝ, hi, ha]
    change p * (2 * a + n) + q * (a + n) + r = (2 * p + q) * a + (p + q) * n + r
    ring

end

end MetaMathlibExt
