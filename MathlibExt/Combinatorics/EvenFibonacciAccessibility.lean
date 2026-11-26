/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AccessibleSets
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Accessibility of the even Fibonacci numbers

The even Fibonacci set is not two-accessible, and the even Fibonacci numbers have degree of
accessibility one. For the two-color obstruction, color a positive integer $x$ by the parity of
$\lfloor x/(2\varphi)\rfloor$, where $\varphi$ is the golden ratio. Along each monochromatic even
Fibonacci step, the fractional part of $x/(2\varphi)$ increases by at least $1/3$, so a
monochromatic sequence has at most three terms.
-/

namespace MetaMathlibExt

namespace evenFibonacciSet_degreeOfAccessibility_eq_one

/-- The Fibonacci number immediately preceding each even Fibonacci number is one modulo four. -/
private lemma fib_residues (n : ℕ) :
    Nat.fib (3 * n + 2) % 4 = 1 ∧ Nat.fib (3 * n + 3) % 2 = 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    let k := 3 * n + 2
    change Nat.fib k % 4 = 1 ∧ Nat.fib (k + 1) % 2 = 0 at ih
    change Nat.fib (k + 3) % 4 = 1 ∧ Nat.fib (k + 4) % 2 = 0
    have h₂ := Nat.fib_add_two (n := k)
    have h₃ : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h₄ : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
    omega

/-- A scaled even Fibonacci gap is between one third and two thirds above an even integer. -/
private lemma scaled_gap {d : ℕ} (hd : d ∈ evenFibonacciSet) :
    ∃ m : ℤ, 2 * m + 1 / 3 ≤ -Real.goldenConj * d / 2 ∧
      -Real.goldenConj * d / 2 ≤ 2 * m + 2 / 3 := by
  obtain ⟨n, rfl⟩ := hd
  let m := Nat.fib (3 * n + 2) / 4
  have hm : Nat.fib (3 * n + 2) = 4 * m + 1 := by
    have := (fib_residues n).1
    dsimp [m]
    omega
  have hid := Real.goldenConj_mul_fib_succ_add_fib (3 * n + 2)
  change Real.goldenConj * Nat.fib (3 * n + 3) + Nat.fib (3 * n + 2) =
    Real.goldenConj ^ (3 * n + 3) at hid
  rw [hm] at hid
  push_cast at hid
  have hψ : |Real.goldenConj| ≤ 2 / 3 := by
    rw [abs_of_neg Real.goldenConj_neg, Real.goldenConj]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hpow : |Real.goldenConj ^ (3 * n + 3)| ≤ 1 / 3 := calc
    _ = |Real.goldenConj| ^ (3 * n + 3) := abs_pow ..
    _ ≤ |Real.goldenConj| ^ 3 :=
      pow_le_pow_of_le_one (abs_nonneg _) (hψ.trans (by norm_num)) (by omega)
    _ ≤ (2 / 3 : ℝ) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hψ _
    _ ≤ _ := by norm_num
  obtain ⟨hlo, hhi⟩ := abs_le.mp hpow
  refine ⟨m, ?_⟩
  push_cast
  constructor <;> linarith

/-- Scaling by $1/(2\varphi)$ turns a gap into the displacement estimated by `scaled_gap`. -/
private noncomputable def phase (x : ℕ+) : ℝ :=
  -Real.goldenConj * (x : ℕ) / 2

private noncomputable def color (x : ℕ+) : Fin 2 :=
  ⟨(⌊phase x⌋ % 2).toNat, by omega⟩

/-- Equal floor parities force the fractional part to absorb the positive part of the step. -/
private lemma fract_step {a b : ℕ+} {d : ℕ} (hd : d ∈ evenFibonacciSet)
    (hgap : (b : ℕ) - ((a : ℕ) : ℤ) = d) (hc : color a = color b) :
    Int.fract (phase a) + 1 / 3 ≤ Int.fract (phase b) := by
  obtain ⟨m, hlo, hhi⟩ := scaled_gap hd
  have hr : ((b : ℕ) : ℝ) - (a : ℕ) = d := by exact_mod_cast hgap
  have he : phase b - phase a = -Real.goldenConj * d / 2 := by
    rw [← hr]; unfold phase; ring
  have h₀ : ⌊phase a⌋ + 2 * m ≤ ⌊phase b⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le (phase a)]
  have h₁ : ⌊phase b⌋ < ⌊phase a⌋ + 2 * m + 2 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith [Int.lt_floor_add_one (phase a)]
  have hmod := congrArg Fin.val hc
  change (⌊phase a⌋ % 2).toNat = (⌊phase b⌋ % 2).toNat at hmod
  have hfloor : ⌊phase b⌋ = ⌊phase a⌋ + 2 * m := by omega
  simp only [Int.fract, hfloor, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  linarith

end evenFibonacciSet_degreeOfAccessibility_eq_one

open evenFibonacciSet_degreeOfAccessibility_eq_one in
/-- **The even Fibonacci set is not 2-accessible.** Let $F_m$ denote the $m$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$. The even Fibonacci set
$\{F_{3n+3} : n \ge 0\} = \{2, 8, 34, \dots\}$ is not $2$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2 (consequence). -/
public theorem even_fibonacci_not_two_accessible :
    ¬ IsRAccessible 2 evenFibonacciSet := by
  intro h
  obtain ⟨x, hmono, hdiff⟩ := h.2.2 color 4 (by decide)
  have step (i : ℕ) (hi : i + 1 < 4) :
      Int.fract (phase (x ⟨i, by omega⟩)) + 1 / 3 ≤ Int.fract (phase (x ⟨i + 1, hi⟩)) := by
    obtain ⟨d, hd, hgap⟩ := hdiff i hi
    exact fract_step hd hgap (hmono ..)
  have bound (i : ℕ) (hi : i < 4) : (i : ℝ) / 3 ≤ Int.fract (phase (x ⟨i, hi⟩)) := by
    induction i with
    | zero => simp
    | succ i ih =>
      push_cast
      linarith [ih (by omega), step i hi]
  exact (not_le_of_gt (Int.fract_lt_one (phase (x 3)))) (by simpa using bound 3 (by decide))

/-- **The even Fibonacci numbers have degree of accessibility $1$.** The even Fibonacci set
$\{2, 8, 34, \dots\}$ is $1$-accessible, and it is not $r$-accessible for any natural number
$r \ge 2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Corollary 2 (`integers-2025-A29-cor-2`). -/
public theorem evenFibonacciSet_degreeOfAccessibility_eq_one :
    IsRAccessible 1 evenFibonacciSet ∧ ∀ r, 2 ≤ r → ¬ IsRAccessible r evenFibonacciSet := by
  constructor
  · refine ⟨?_, le_rfl, fun c k _ => ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact Nat.fib_pos.mpr (by omega)
    · refine ⟨fun i => ⟨2 * (i : ℕ) + 1, by omega⟩, fun _ _ => Subsingleton.elim .., ?_⟩
      intro i hi
      exact ⟨2, ⟨0, by decide⟩, by simp; ring⟩
  · exact fun r hr h => even_fibonacci_not_two_accessible (IsRAccessible.mono _ h (by decide) hr)

end MetaMathlibExt
