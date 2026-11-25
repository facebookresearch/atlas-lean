/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Fin.Basic

/-!
# Monochromatic descending waves

An explicit two-colouring of the first 157 positive integers avoids descending waves of
length 13. This refutes the proposed quadratic formula for the wave number.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted

/-- **Descending wave.** A $k$-term descending wave is a sequence $x_0, x_1, \dots, x_{k-1}$ of
natural numbers with $x_0 < x_1 < \dots < x_{k-1}$ and $x_{j-1} + x_{j+1} \le 2 x_j$ for every
$j$ with $0 < j < k - 1$. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧ ∀ i j l : Fin k, (i : ℕ) + 1 = (j : ℕ) → (j : ℕ) + 1 = (l : ℕ) →
    x i + x l ≤ 2 * x j

/-- **Forcing a monochromatic descending wave.** For natural numbers $k$ and $n$, the statement
that for every colouring of the natural numbers with two colours there is a monochromatic $k$-term
descending wave all of whose terms lie in $\{1, \dots, n\}$. Equivalently, every colouring of
$\{1, \dots, n\}$ with two colours has a monochromatic $k$-term descending wave, so the statement
says $f(k) \le n$, where $f(k)$ is the least $n$ with this property. -/
def ForcesMonochromaticWave (k n : ℕ) : Prop :=
  ∀ c : ℕ → Fin 2, ∃ x : Fin k → ℕ, IsDescendingWave x ∧ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
    ∃ γ : Fin 2, ∀ i, c (x i) = γ

/-- **Erdős Problem 781, the exact-value question.** For natural numbers $k$ and $n$, say that $n$
forces a $k$-term wave if every colouring of $\{1, \dots, n\}$ with two colours has a monochromatic
$k$-term descending wave. The statement that for every natural number $k \ge 1$ the number
$k^2 - k + 1$ forces a $k$-term wave and the number $k^2 - k$ does not; that is,
$f(k) = k^2 - k + 1$ for every $k \ge 1$, where $f(k)$ is the least $n$ that forces a $k$-term
wave. -/
def waveNumberQuadratic : Prop :=
  ∀ k : ℕ, 1 ≤ k → ForcesMonochromaticWave k (k ^ 2 - k + 1) ∧
    ¬ ForcesMonochromaticWave k (k ^ 2 - k)

/-- **Erdős Problem 781, cubic order of the wave number.** For natural numbers $k$ and $n$, say
that $n$ forces a $k$-term wave if every colouring of $\{1, \dots, n\}$ with two colours has a
monochromatic $k$-term descending wave. The statement that there are real numbers $c > 0$ and $C$
such that for all sufficiently large $k$, every natural number $n$ that forces a $k$-term wave
satisfies $n \ge c k^3$, and the natural number $\lfloor \max(C k^3, 0) \rfloor$ forces a $k$-term
wave. Writing $f(k)$ for the least $n$ that forces a $k$-term wave, this says $f(k) \asymp k^3$. -/
def waveNumberCubicOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in Filter.atTop,
    (∀ n : ℕ, ForcesMonochromaticWave k n → c * (k : ℝ) ^ 3 ≤ n) ∧
      ForcesMonochromaticWave k ⌊C * (k : ℝ) ^ 3⌋₊

-- Each pair gives the lengths of two consecutive runs, first red and then blue.
-- Bit 0 of the resulting mask represents the first point of the first run.
private def redRuns : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (r, b) :: rs => (2 ^ r - 1) ||| (redRuns rs <<< (r + b))

private def red : ℕ :=
  redRuns [(12, 2), (2, 11), (10, 10), (10, 10), (9, 9), (8, 8), (7, 7),
    (6, 6), (5, 5), (4, 4), (3, 3), (2, 2), (1, 1)] <<< 1

private def coloring (p : ℕ) : Fin 2 := if red.testBit p then 0 else 1

private def colorMask (γ : Fin 2) : ℕ := if γ = 0 then red else (2 ^ 158 - 2) ^^^ red

private lemma color_mem : ∀ p : Fin 158, 0 < p.val → (colorMask (coloring p)).testBit p := by
  decide +kernel

-- In the input row, entry i records possible endpoints before a step of size
-- start + i. Shift these endpoints by the step and intersect with the chosen colour.
-- Taking the union with the tail also admits all larger steps.
private def advance (mask : ℕ) (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | s :: ss =>
    let tail := advance mask (start + 1) ss
    ((s <<< start &&& mask) ||| tail.getD 0 0) :: tail

private lemma advance_entry (mask : ℕ) (ss : List ℕ) (start i : ℕ) :
    (advance mask start ss).getD i 0 =
      (ss.getD i 0 <<< (start + i) &&& mask) ||| (advance mask start ss).getD (i + 1) 0 := by
  induction ss generalizing start i with
  | nil => simp [advance]
  | cons s ss ih =>
    cases i with
    | zero => simp [advance]
    | succ i =>
      simpa only [advance, List.getD_cons_succ, Nat.succ_add, Nat.add_succ, Nat.add_one] using
        ih (start + 1) i

-- Entry d of row n records endpoints of waves with n gaps, the last at least d + 1.
private def ends (mask : ℕ) : ℕ → List ℕ
  | 0 => List.replicate 157 mask
  | n + 1 => advance mask 1 (ends mask n)

private lemma advance_mem (mask : ℕ) (ss : List ℕ) {i j y : ℕ} (hle : i ≤ j)
    (h : (ss.getD j 0 <<< (1 + j) &&& mask).testBit y) :
    ((advance mask 1 ss).getD i 0).testBit y := by
  refine Nat.decreasingInduction (motive := fun k _ =>
    ((advance mask 1 ss).getD k 0).testBit y = true) ?_ ?_ hle
  · intro k _ ih
    rw [advance_entry, Nat.testBit_or, ih, Bool.or_true]
  · rw [advance_entry, Nat.testBit_or, h, Bool.true_or]

private lemma next_mem (mask : ℕ) (n x y d : ℕ) (hxy : x < y) (hd : d < y - x)
    (hx : ((ends mask n).getD (y - x - 1) 0).testBit x) (hy : mask.testBit y) :
    ((ends mask (n + 1)).getD d 0).testBit y := by
  apply advance_mem mask (ends mask n) (j := y - x - 1) (by omega)
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, show 1 + (y - x - 1) = y - x by omega,
    show y - (y - x) = x by omega, hx, hy, decide_eq_true (Nat.sub_le y x)]
  rfl

private lemma wave_mem {mask : ℕ} {x : Fin 13 → ℕ} (hw : IsDescendingWave x)
    (hb : ∀ t, x t ≤ 157) (hm : ∀ t, mask.testBit (x t))
    (n : ℕ) (hn : n + 1 < 13) (d : ℕ) (hd : d < x ⟨n + 1, hn⟩ - x ⟨n, by omega⟩) :
    ((ends mask (n + 1)).getD d 0).testBit (x ⟨n + 1, hn⟩) := by
  apply next_mem mask n _ _ d (hw.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))) hd _ (hm _)
  cases n with
  | zero =>
    have hsmall : x 1 - x 0 - 1 < 157 := by have := hb 1; omega
    change ((List.replicate 157 mask).getD (x 1 - x 0 - 1) 0).testBit (x 0) = true
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hsmall, Option.getD_some]
    exact hm 0
  | succ n =>
    apply wave_mem hw hb hm n (by omega)
    let a : Fin 13 := ⟨n, by omega⟩
    let b : Fin 13 := ⟨n + 1, by omega⟩
    let c : Fin 13 := ⟨n + 2, hn⟩
    change x c - x b - 1 < x b - x a
    have hdesc := hw.2 a b c rfl rfl
    have hab : x a < x b := hw.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))
    omega

private lemma no_endpoints : ∀ γ : Fin 2, (ends (colorMask γ) 12).getD 0 0 = 0 := by
  decide +kernel

/--
**Erdős Problem 781 is false.** For natural numbers $k$ and $n$, say that $n$ forces a $k$-term
wave if every colouring of $\{1, \dots, n\}$ with two colours has a monochromatic $k$-term
descending wave. It is not the case that for every natural number $k \ge 1$ the number
$k^2 - k + 1$ forces a $k$-term wave and the number $k^2 - k$ does not. Writing $f(k)$ for the
least $n$ that forces a $k$-term wave, this says that $f(k) \ne k^2 - k + 1$ for some $k \ge 1$.

Alon and Spencer proved $f(k) \ge c k^3$ for some $c > 0$, so $f(k) > k^2 - k + 1$ for all large
$k$.

Source: T. F. Bloom, Erdős
Problems, Problem #781, https://www.erdosproblems.com/781 (status DISPROVED); resolution: N. Alon
and J. Spencer, Ascending waves, J. Combin. Theory Ser. A 52 (1989), 275-287; T. C. Brown, P. Erdős
and A. R. Freedman, Quasi-progressions and descending waves, J. Combin. Theory Ser. A 53 (1990),
81-95, Alon-Spencer Theorem 1.1: c_1 k³ ≤ f(k) ≤ c_2 k³ for all k ≥ 1, the upper bound being Brown,
Erdős and Freedman's f(k) ≤ k³/3 - 4k/3 + 3; Brown, Erdős and Freedman also proved k² - k + 1 ≤ f(k)
and asked whether it is the exact value, and Alon and Spencer: 'Here we show that this is false',
https://web.math.princeton.edu/~nalon/PDFS/Publications1/Ascending%20waves.pdf.
-/
public theorem waveNumberQuadratic_refuted : ¬ waveNumberQuadratic := by
  intro h
  obtain ⟨x, hw, hb, γ, hc⟩ := (h 13 (by decide)).1 coloring
  have hm (t : Fin 13) : (colorMask γ).testBit (x t) := by
    rw [← hc t]
    exact color_mem ⟨x t, Nat.lt_succ_of_le (hb t).2⟩ (hb t).1
  have hlt : x 11 < x 12 := hw.1 (by decide)
  have hend := wave_mem hw (fun t => (hb t).2) hm 11 (by decide) 0 (Nat.sub_pos_of_lt hlt)
  rw [no_endpoints] at hend
  simp at hend

end MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted
