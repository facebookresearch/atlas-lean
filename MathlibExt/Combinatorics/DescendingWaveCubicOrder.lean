/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monochromatic descending waves: cubic order (Erdős Problem 781)

Erdős Problem 781 (Brown, Erdős and Freedman): let `f(k)` be the minimal `n` such that any
`2`-coloring of `{1, …, n}` contains a monochromatic `k`-term descending wave, a sequence `x_1 < ⋯ <
x_k` with `x_j ≥ (x_{j+1} + x_{j-1}) / 2` for `1 < j < k`. Estimate `f(k)`. In particular, is `f(k)
= k² - k + 1` for all `k`?

This module proves `waveNumberCubicOrder_holds`: `f(k)` has cubic order, as Alon and Spencer
showed. Every number that forces a `k`-term wave is at least `k³ / 32768` once `k ≥ 2048`, and
`k³` forces a `k`-term wave for every `k ≥ 1`.

Source: T. F. Bloom, Erdős Problems, Problem #781, https://www.erdosproblems.com/781 (status
DISPROVED). UnsolvedMath record UM-30007031 (`EP-781`), dataset ulamai/UnsolvedMath v1.8.0.

`ForcesMonochromaticWave k n` says `f(k) ≤ n`; it is monotone in `n`, so `f(k) = k² - k + 1` is
'forced at `k² - k + 1` and not at `k² - k`', and `f(k) ≍ k³` is stated through the same predicate
without `sInf`. Alon and Spencer work with ascending waves
(`x_{i+1} - x_i ≤ x_{i+2} - x_{i+1}`); the reflection `x ↦ n + 1 - x` exchanges ascending and
descending waves in `{1, …, n}`, so both define the same `f`, and Alon and Spencer quote Brown,
Erdős and Freedman's bounds for it. Their asymptotic lower bound refutes the quadratic formula.

## Proof outline

* Upper bound. A monochromatic `k`-term descending wave in `{1, …, k³}` is built greedily from
  the right end, as in the proof of `AW(k; r) ≤ k^(2r-1)` in Section 1 of T. LeSaulnier and
  A. Robertson, *On monochromatic ascending waves*, arXiv:math/0506351. If `z` is the current
  leftmost point and `g` the current gap, either one of the `k` integers `z - g - k + 1, …, z - g`
  has the colour of `z`, or these `k` consecutive integers form a wave of the other colour. Each
  gap exceeds the previous one by less than `k`, so every point stays in `{1, …, k³}`.
* Lower bound. Fix `k ≥ 2048` and `q = ⌊k / 512⌋`, cut the integers into blocks of `b = 64 q`
  consecutive integers and pair the blocks `2p` and `2p + 1`. A vector of pair bits colours block
  `2p` by its bit and block `2p + 1` by the other colour. This is a random block colouring in the
  style of Alon and Spencer, whose argument Section 2 of LeSaulnier and Robertson generalizes.
  - Three consecutive blocks never all have one colour, so a monochromatic run with gaps at most
    `b` spans fewer than `2b` integers: in a monochromatic `k`-term wave all gaps but the last `2b`
    exceed `b`.
  - The block indices `y_i = ⌊x_i / b⌋` of a descending wave satisfy
    `y_{j+L} - y_j ≤ y_{i+L} - y_i + 1` for `i ≤ j`. So the block differences of `64 q`
    consecutive gaps in `(b, q b]` form an admissible word with entries in `[1, q + 1]`: each
    entry is at most one more than every earlier entry, and after two consecutive entries equal
    to the running minimum `m`, an entry `m + 1` is followed by an entry at most `m`.
  - Over the one-letter extensions of an admissible word, the potential `64^m · ω(state)` sums to
    at most `7 / 4` times its value, so there are at most `82 · 64^q · (7 / 4)^n` admissible
    words of length `n`.
  - If two consecutive blocks of a strictly decreasing list of `n + 1` blocks share a pair, the
    blocks never all have one colour; otherwise they lie in distinct pairs and all have one
    colour for a `2^(-n)` fraction of the bit vectors. Double counting over the top block and
    the word gives a colouring for which no admissible word, read down from a block in range,
    visits blocks of only one colour.
  - For that colouring all `k - 192 q + 1` first gaps of a monochromatic `k`-term wave exceed
    `64 q²`, so it does not fit in `{1, …, (k - 192 q + 1)(64 q² + 1)}`, and this number is at
    least `k³ / 32768`.

## Implementation notes

`waveNumberCubicOrder_holds` keeps the full name, statement and docstring it had in the former
wanted module `WantedExt/Combinatorics/DescendingWaveColoringErdosProblem781Wanted.lean`, so its
namespace still reads `DescendingWaveColoringErdosProblem781Wanted`. All other declarations are
private.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted

namespace CubicOrder

open Finset

/-! ### The cubic upper bound -/

/-- The greedy construction, run for `m` more steps from a point `z` of colour `γ` with current gap
`g`. Either some block of `k` consecutive integers in `[1, n]` avoids the colour `γ`, or there is a
sequence `z = w 0 > w 1 > ⋯ > w m ≥ 1` of colour `γ` in `[1, n]` whose first gap is at least `g`
and whose gaps are non-decreasing. -/
private lemma exists_block_or_exists_descent (c : ℕ → Fin 2) (γ : Fin 2) (k n m : ℕ) :
    ∀ z g : ℕ, 1 ≤ g → z ≤ n → c z = γ → m * (g + m * k) < z →
      (∃ a, 1 ≤ a ∧ a + k ≤ n + 1 ∧ ∀ i < k, c (a + i) ≠ γ) ∨
      ∃ w : ℕ → ℕ, w 0 = z ∧ (∀ i < m, w (i + 1) < w i) ∧
        (∀ i ≤ m, c (w i) = γ ∧ 1 ≤ w i ∧ w i ≤ n) ∧ (0 < m → g ≤ w 0 - w 1) ∧
        ∀ i, i + 1 < m → w i - w (i + 1) ≤ w (i + 1) - w (i + 2) := by
  induction m with
  | zero =>
    intro z g _ hz hc hlt
    exact Or.inr ⟨fun _ => z, rfl, by simp, fun _ _ => ⟨hc, show 1 ≤ z by omega, hz⟩, by simp,
      by simp⟩
  | succ m ih =>
    intro z g hg hz hc hlt
    have hbig : g + k < z := by
      have h1 : k ≤ (m + 1) * k := Nat.le_mul_of_pos_left k (Nat.succ_pos m)
      have h2 : g + (m + 1) * k ≤ (m + 1) * (g + (m + 1) * k) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos m)
      omega
    by_cases hex : ∃ j < k, c (z - g - j) = γ
    · obtain ⟨j, hj, hcj⟩ := hex
      have hstep : m * (g + j + m * k) + (g + j) < z := by
        have : m * j ≤ m * k := Nat.mul_le_mul_left m hj.le
        nlinarith
      rcases ih (z - g - j) (g + j) (by omega) (by omega) hcj (by omega) with
        hblock | ⟨w, hw0, hdec, hcol, hfirst, hgap⟩
      · exact Or.inl hblock
      · refine Or.inr ⟨fun | 0 => z | i + 1 => w i, rfl, fun i hi => ?_, fun i hi => ?_,
          fun _ => ?_, fun i hi => ?_⟩
        · rcases i with _ | i
          · change w 0 < z
            omega
          · exact hdec i (by omega)
        · rcases i with _ | i
          · change c z = γ ∧ 1 ≤ z ∧ z ≤ n
            exact ⟨hc, by omega, hz⟩
          · exact hcol i (by omega)
        · change g ≤ z - w 0
          omega
        · rcases i with _ | i
          · change z - w 0 ≤ w 0 - w 1
            have := hfirst (by omega)
            omega
          · exact hgap i (by omega)
    · push Not at hex
      refine Or.inl ⟨z - g - (k - 1), by omega, by omega, fun i hi => ?_⟩
      have := hex (k - 1 - i) (by omega)
      rwa [show z - g - (k - 1 - i) = z - g - (k - 1) + i by omega] at this

/-- **Cubic upper bound for the wave number.** Every two-colouring of `{1, …, k³}` contains a
monochromatic `k`-term descending wave. -/
private theorem forcesMonochromaticWave_cube (k : ℕ) (hk : 1 ≤ k) :
    ForcesMonochromaticWave k (k ^ 3) := by
  intro c
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hbound : k * (1 + k * (k + 1)) < (k + 1) ^ 3 := by nlinarith
  rcases exists_block_or_exists_descent c (c ((k + 1) ^ 3)) (k + 1) ((k + 1) ^ 3) k
      ((k + 1) ^ 3) 1 le_rfl le_rfl rfl hbound with
    ⟨a, ha1, ha2, hac⟩ | ⟨w, -, hdec, hcol, -, hgap⟩
  · -- `k` consecutive integers avoiding the colour of `k ^ 3` form a wave of the other colour.
    refine ⟨fun i => a + (i : ℕ), ⟨Fin.val_strictMono.const_add a, fun i j l hij hjl => ?_⟩,
      fun i => ?_, c a, fun i => ?_⟩
    · change a + (i : ℕ) + (a + l) ≤ 2 * (a + j)
      omega
    · have := i.isLt
      change 1 ≤ a + (i : ℕ) ∧ a + (i : ℕ) ≤ (k + 1) ^ 3
      omega
    · have h0 := hac 0 (by omega)
      rw [add_zero] at h0
      have key : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide
      exact key _ _ _ (hac i i.isLt) h0
  · -- Otherwise the greedy points, read from left to right, form a wave of that colour.
    refine ⟨fun i => w (k - i), ⟨?_, fun i j l hij hjl => ?_⟩,
      fun i => (hcol _ (Nat.sub_le _ _)).2, c ((k + 1) ^ 3),
      fun i => (hcol _ (Nat.sub_le _ _)).1⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hi := i.isLt
      change w (k - (i : ℕ)) < w (k - ((i : ℕ) + 1))
      rw [show k - (i : ℕ) = k - ((i : ℕ) + 1) + 1 by omega]
      exact hdec _ (by omega)
    · have hl := l.isLt
      change w (k - (i : ℕ)) + w (k - (l : ℕ)) ≤ 2 * w (k - (j : ℕ))
      rw [show k - (i : ℕ) = k - l + 2 by omega, show k - (j : ℕ) = k - l + 1 by omega]
      have h1 := hgap (k - l) (by omega)
      have h2 := hdec (k - l) (by omega)
      have h3 : w (k - l + 2) < w (k - l + 1) := hdec (k - l + 1) (by omega)
      omega

/-! ### Floor division -/

private lemma add_div_le_succ {b : ℕ} (hb : 0 < b) (a c : ℕ) : (a + c) / b ≤ a / b + c / b + 1 := by
  have ha := Nat.lt_div_mul_add (a := a) hb
  have hc := Nat.lt_div_mul_add (a := c) hb
  have : (a + c) / b < a / b + c / b + 2 := by
    rw [Nat.div_lt_iff_lt_mul hb]
    nlinarith
  omega

private lemma div_sub_div_le {b u u' v v' : ℕ} (hu : u ≤ u') (hv : v ≤ v') (h : u' - u ≤ v' - v) :
    u' / b - u / b ≤ v' / b - v / b + 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h1 : u' / b ≤ (u' - u) / b + u / b + 1 := by
    have := add_div_le_succ hb (u' - u) u
    rwa [Nat.sub_add_cancel hu] at this
  have h2 : (v' - v) / b + v / b ≤ v' / b := by
    have : (v' - v) / b + v / b ≤ (v' - v + v) / b := Nat.div_add_div_le_add_div
    rwa [Nat.sub_add_cancel hv] at this
  have h3 : (u' - u) / b ≤ (v' - v) / b := Nat.div_le_div_right h
  omega

/-! ### Block colourings from pair bits -/

/-- The bit of pair `i`, and `false` outside the range. -/
private def pairBit {P : ℕ} (ε : Fin P → Bool) (i : ℕ) : Bool :=
  if h : i < P then ε ⟨i, h⟩ else false

/-- Block `y` belongs to pair `y / 2`; the two blocks of a pair get opposite colours. -/
private def blockCol {P : ℕ} (ε : Fin P → Bool) (y : ℕ) : Bool :=
  xor (pairBit ε (y / 2)) (decide (y % 2 = 1))

private lemma blockCol_succ_ne {P : ℕ} (ε : Fin P → Bool) {y : ℕ} (hy : y % 2 = 0) :
    blockCol ε (y + 1) ≠ blockCol ε y := by
  have h1 : (y + 1) / 2 = y / 2 := by omega
  have h2 : (y + 1) % 2 = 1 := by omega
  simp [blockCol, h1, h2, hy]

private lemma not_three {P : ℕ} (ε : Fin P → Bool) (y : ℕ) :
    ¬ (blockCol ε (y + 1) = blockCol ε y ∧ blockCol ε (y + 2) = blockCol ε y) := by
  rintro ⟨h1, h2⟩
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · exact blockCol_succ_ne ε hy h1
  · have h3 := blockCol_succ_ne ε (y := y + 1) (by omega)
    exact h3 (h2.trans h1.symm)

/-- A monochromatic run whose gaps are at most `b` stays inside two consecutive blocks. -/
private lemma short_run {P b : ℕ} (ε : Fin P → Bool) (hb : 0 < b) (X : ℕ → ℕ) (j L : ℕ)
    (hstep : ∀ i < L, X (j + i + 1) ≤ X (j + i) + b)
    (hcol : ∀ i ≤ L, blockCol ε (X (j + i) / b) = blockCol ε (X j / b)) :
    X (j + L) < X j + 2 * b := by
  have key : ∀ i ≤ L, X (j + i) / b ≤ X j / b + 1 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hs : X (j + (i + 1)) / b ≤ X (j + i) / b + 1 := by
        have h := hstep i (by omega)
        calc X (j + (i + 1)) / b ≤ (X (j + i) + b) / b :=
              Nat.div_le_div_right (by simpa [add_assoc] using h)
          _ = X (j + i) / b + 1 := Nat.add_div_right _ hb
      by_contra hcon
      push Not at hcon
      have e1 : X (j + i) / b = X j / b + 1 := by omega
      have e2 : X (j + (i + 1)) / b = X j / b + 2 := by omega
      apply not_three ε (X j / b)
      constructor
      · rw [← e1]; exact hcol i (by omega)
      · rw [← e2]; exact hcol (i + 1) hi
  have h := key L le_rfl
  have h1 := Nat.lt_div_mul_add (a := X (j + L)) hb
  have h2 := Nat.div_mul_le_self (X j) b
  have h3 : X (j + L) / b * b ≤ (X j / b + 1) * b := Nat.mul_le_mul_right _ h
  nlinarith

/-! ### Admissible block-difference sequences -/

/-- The update of a state by a new entry `a`. A state records the running minimum of the entries
read so far, capped at its initial value, whether two consecutive entries both equal that minimum,
and whether the latest entry equals it. -/
private def step (s : ℕ × Bool × Bool) (a : ℕ) : ℕ × Bool × Bool :=
  if a < s.1 then (a, false, true)
  else if a = s.1 then (s.1, s.2.1 || s.2.2, true)
  else (s.1, s.2.1, false)

/-- The state of a list, read from its last entry to its head. -/
private def stateOf (D : ℕ) : List ℕ → ℕ × Bool × Bool
  | [] => (D, false, false)
  | a :: l => step (stateOf D l) a

/-- The entries allowed after a given state. -/
private def ok (s : ℕ × Bool × Bool) (a : ℕ) : Bool :=
  decide (1 ≤ a ∧ a ≤ s.1 + 1 ∧ (s.2.1 = true → s.2.2 = false → a ≤ s.1))

/-- The admissible lists of length `n`. -/
private def seqs (D : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => (seqs D n).biUnion fun l =>
      ((range (D + 2)).filter fun a => ok (stateOf D l) a).image fun a => a :: l

/-- The potential used to count admissible lists. -/
private def weight (s : ℕ × Bool × Bool) : ℕ :=
  64 ^ s.1 * (if s.2.1 then (if s.2.2 then 20 else 12) else (if s.2.2 then 60 else 82))

private lemma geom64 (m : ℕ) : 63 * ∑ a ∈ range m, 64 ^ a ≤ 64 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

private lemma local_bound (D : ℕ) (s : ℕ × Bool × Bool) :
    4 * ∑ a ∈ (range (D + 2)).filter (fun a => ok s a), weight (step s a) ≤ 7 * weight s := by
  obtain ⟨m, p, r⟩ := s
  set F := (range (D + 2)).filter (fun a => ok (m, p, r) a) with hF
  rw [← sum_filter_add_sum_filter_not F (fun a => a < m)]
  have hlow : 63 * ∑ a ∈ F.filter (fun a => a < m), weight (step (m, p, r) a) ≤
      60 * 64 ^ m := by
    have hsub : F.filter (fun a => a < m) ⊆ range m := by
      intro a ha
      simp only [mem_filter] at ha
      exact mem_range.2 ha.2
    calc 63 * ∑ a ∈ F.filter (fun a => a < m), weight (step (m, p, r) a)
        = 63 * ∑ a ∈ F.filter (fun a => a < m), 60 * 64 ^ a := by
          congr 1
          apply sum_congr rfl
          intro a ha
          simp only [mem_filter] at ha
          simp [step, weight, ha.2, mul_comm]
      _ ≤ 63 * ∑ a ∈ range m, 60 * 64 ^ a := by
          gcongr
      _ = 60 * (63 * ∑ a ∈ range m, 64 ^ a) := by rw [← mul_sum]; ring
      _ ≤ 60 * 64 ^ m := by gcongr; exact geom64 m
  have hsub2 : F.filter (fun a => ¬ a < m) ⊆ {m, m + 1} := by
    intro a ha
    simp only [hF, mem_filter, ok, decide_eq_true_eq] at ha
    simp only [mem_insert, mem_singleton]
    omega
  have hm : step (m, p, r) m = (m, p || r, true) := by simp [step]
  have hm1 : step (m, p, r) (m + 1) = (m, p, false) := by simp [step]
  have hhigh : ∑ a ∈ F.filter (fun a => ¬ a < m), weight (step (m, p, r) a) ≤
      weight (m, p || r, true) + (if p = true ∧ r = false then 0 else weight (m, p, false)) := by
    by_cases hpr : p = true ∧ r = false
    · have hsub3 : F.filter (fun a => ¬ a < m) ⊆ {m} := by
        intro a ha
        simp only [hF, mem_filter, ok, decide_eq_true_eq] at ha
        simp only [mem_singleton]
        have := ha.1.2.2.2 hpr.1 hpr.2
        omega
      calc _ ≤ ∑ a ∈ ({m} : Finset ℕ), weight (step (m, p, r) a) :=
            sum_le_sum_of_subset hsub3
        _ = weight (m, p || r, true) := by simp [hm]
        _ ≤ _ := by simp [hpr]
    · calc _ ≤ ∑ a ∈ ({m, m + 1} : Finset ℕ), weight (step (m, p, r) a) :=
            sum_le_sum_of_subset hsub2
        _ = weight (m, p || r, true) + weight (m, p, false) := by
            rw [sum_pair (by omega), hm, hm1]
        _ = _ := by simp [hpr]
  have hX : 0 < 64 ^ m := by positivity
  generalize ∑ a ∈ F.filter (fun a => a < m), weight (step (m, p, r) a) = S1 at hlow ⊢
  generalize ∑ a ∈ F.filter (fun a => ¬ a < m), weight (step (m, p, r) a) = S2 at hhigh ⊢
  cases p <;> cases r <;> simp [weight] at hhigh ⊢ <;> omega

private lemma mem_seqs_succ {D n : ℕ} {l : List ℕ} :
    l ∈ seqs D (n + 1) ↔ ∃ l' ∈ seqs D n, ∃ a, a < D + 2 ∧ ok (stateOf D l') a ∧ l = a :: l' := by
  simp only [seqs, mem_biUnion, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨l', hl', a, ⟨ha, hok⟩, rfl⟩
    exact ⟨l', hl', a, ha, hok, rfl⟩
  · rintro ⟨l', hl', a, ha, hok, rfl⟩
    exact ⟨l', hl', a, ⟨ha, hok⟩, rfl⟩

private lemma weight_sum_succ (D n : ℕ) :
    4 * ∑ l ∈ seqs D (n + 1), weight (stateOf D l) ≤ 7 * ∑ l ∈ seqs D n, weight (stateOf D l) := by
  have hdisj : (seqs D n : Set (List ℕ)).PairwiseDisjoint fun l =>
      ((range (D + 2)).filter fun a => ok (stateOf D l) a).image fun a => a :: l := by
    intro l₁ _ l₂ _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx₁ hx₂
    simp only [mem_image] at hx₁ hx₂
    obtain ⟨a₁, _, rfl⟩ := hx₁
    obtain ⟨a₂, _, h⟩ := hx₂
    exact hne (List.cons.inj h).2.symm
  rw [seqs, sum_biUnion hdisj, mul_sum, mul_sum]
  apply sum_le_sum
  intro l _
  rw [sum_image (fun a _ b _ h => (List.cons.inj h).1)]
  exact local_bound D (stateOf D l)

private lemma card_seqs (D n : ℕ) : 4 ^ n * (seqs D n).card ≤ 7 ^ n * (82 * 64 ^ D) := by
  have hW : ∀ n, 4 ^ n * ∑ l ∈ seqs D n, weight (stateOf D l) ≤ 7 ^ n * (82 * 64 ^ D) := by
    intro n
    induction n with
    | zero => simp [seqs, stateOf, weight, mul_comm]
    | succ n ih =>
      calc 4 ^ (n + 1) * ∑ l ∈ seqs D (n + 1), weight (stateOf D l)
          = 4 ^ n * (4 * ∑ l ∈ seqs D (n + 1), weight (stateOf D l)) := by ring
        _ ≤ 4 ^ n * (7 * ∑ l ∈ seqs D n, weight (stateOf D l)) :=
            Nat.mul_le_mul_left _ (weight_sum_succ D n)
        _ = 7 * (4 ^ n * ∑ l ∈ seqs D n, weight (stateOf D l)) := by ring
        _ ≤ 7 * (7 ^ n * (82 * 64 ^ D)) := by gcongr
        _ = 7 ^ (n + 1) * (82 * 64 ^ D) := by ring
  have hcard : (seqs D n).card ≤ ∑ l ∈ seqs D n, weight (stateOf D l) := by
    rw [card_eq_sum_ones]
    apply sum_le_sum
    intro l _
    simp only [weight]
    have : 0 < 64 ^ (stateOf D l).1 := by positivity
    split_ifs <;> nlinarith
  calc 4 ^ n * (seqs D n).card ≤ 4 ^ n * ∑ l ∈ seqs D n, weight (stateOf D l) := by gcongr
    _ ≤ _ := hW n

private lemma seqs_props {D : ℕ} : ∀ {n : ℕ} {l : List ℕ}, l ∈ seqs D n →
    l.length = n ∧ ∀ a ∈ l, 1 ≤ a ∧ a ≤ D + 1
  | 0, l, hl => by
    rw [seqs, mem_singleton] at hl
    subst hl
    simp
  | n + 1, l, hl => by
    obtain ⟨l', hl', a, ha, hok, rfl⟩ := mem_seqs_succ.1 hl
    obtain ⟨hlen, hall⟩ := seqs_props hl'
    simp only [ok, decide_eq_true_eq] at hok
    refine ⟨by simp [hlen], ?_⟩
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨hok.1, by omega⟩
    · exact hall b hb

/-! ### Counting colourings -/

private lemma pairBit_update_ne {P : ℕ} (ε : Fin P → Bool) (p : Fin P) (v : Bool) {i : ℕ}
    (hi : i ≠ p.val) : pairBit (Function.update ε p v) i = pairBit ε i := by
  unfold pairBit
  split_ifs with h
  · rw [Function.update_of_ne]
    intro heq
    exact hi (by rw [← heq])
  · rfl

private lemma pairBit_update_self {P : ℕ} (ε : Fin P → Bool) (p : Fin P) (v : Bool) :
    pairBit (Function.update ε p v) p.val = v := by
  simp [pairBit, p.isLt]

/-- Flipping the bit of pair `p`. -/
private def flipAt {P : ℕ} (p : Fin P) (ε : Fin P → Bool) : Fin P → Bool :=
  Function.update ε p (!ε p)

private lemma flipAt_flipAt {P : ℕ} (p : Fin P) (ε : Fin P → Bool) : flipAt p (flipAt p ε) = ε := by
  funext i
  by_cases h : i = p
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

private lemma blockCol_flipAt_ne {P : ℕ} (p : Fin P) (ε : Fin P → Bool) {w : ℕ}
    (hw : w / 2 ≠ p.val) :
    blockCol (flipAt p ε) w = blockCol ε w := by
  simp only [blockCol, flipAt, pairBit_update_ne _ _ _ hw]

private lemma blockCol_flipAt_self {P : ℕ} (p : Fin P) (ε : Fin P → Bool) {z : ℕ}
    (hz : z / 2 = p.val) :
    blockCol (flipAt p ε) z = !blockCol ε z := by
  have h1 : pairBit ε (z / 2) = ε p := by
    rw [hz]; simp [pairBit, p.isLt]
  simp only [blockCol, flipAt]
  rw [hz, pairBit_update_self, ← hz, h1]
  cases ε p <;> simp

private lemma card_mono {P : ℕ} (γ : Bool) : ∀ zs : List ℕ, zs.Pairwise (· > ·) →
    (∀ z ∈ zs, z / 2 < P) →
    2 ^ zs.length * (univ.filter fun ε : Fin P → Bool => ∀ z ∈ zs, blockCol ε z = γ).card ≤
      2 ^ P
  | [], _, _ => by simp
  | z :: zs, hpw, hP => by
    rw [List.pairwise_cons] at hpw
    have ih := card_mono γ zs hpw.2 (fun w hw => hP w (List.mem_cons_of_mem _ hw))
    set A := univ.filter fun ε : Fin P → Bool => ∀ w ∈ zs, blockCol ε w = γ with hA
    have hB : (univ.filter fun ε : Fin P → Bool => ∀ w ∈ z :: zs, blockCol ε w = γ) =
        A.filter fun ε => blockCol ε z = γ := by
      ext ε
      simp [A, and_comm]
    rw [hB, List.length_cons, pow_succ]
    suffices h2 : 2 * (A.filter fun ε => blockCol ε z = γ).card ≤ A.card by
      calc 2 ^ zs.length * 2 * (A.filter fun ε => blockCol ε z = γ).card
          = 2 ^ zs.length * (2 * (A.filter fun ε => blockCol ε z = γ).card) := by ring
        _ ≤ 2 ^ zs.length * A.card := Nat.mul_le_mul_left _ h2
        _ ≤ 2 ^ P := ih
    by_cases hsame : ∃ w ∈ zs, w / 2 = z / 2
    · obtain ⟨w, hw, hwz⟩ := hsame
      have hlt : w < z := hpw.1 w hw
      have hz : z = w + 1 := by omega
      have hw2 : w % 2 = 0 := by omega
      have h0 : (A.filter fun ε => blockCol ε z = γ) = ∅ := by
        apply filter_eq_empty_iff.2
        intro ε hε hz'
        have hwγ : blockCol ε w = γ := (mem_filter.1 hε).2 w hw
        exact blockCol_succ_ne ε hw2 (by rw [← hz, hz', hwγ])
      rw [h0]
      simp
    · push Not at hsame
      set p : Fin P := ⟨z / 2, hP z List.mem_cons_self⟩ with hp
      have hzp : z / 2 = p.val := rfl
      have hfix : ∀ ε, flipAt p ε ∈ A ↔ ε ∈ A := by
        intro ε
        simp only [hA, mem_filter, mem_univ, true_and]
        constructor
        · intro h w hw
          rw [← blockCol_flipAt_ne p ε (hsame w hw)]
          exact h w hw
        · intro h w hw
          rw [blockCol_flipAt_ne p ε (hsame w hw)]
          exact h w hw
      have hcard : (A.filter fun ε => blockCol ε z = γ).card =
          (A.filter fun ε => ¬ blockCol ε z = γ).card := by
        apply card_nbij' (flipAt p) (flipAt p)
        · intro ε hε
          simp only [coe_filter, Set.mem_ofPred_eq] at hε ⊢
          refine ⟨(hfix ε).2 hε.1, ?_⟩
          rw [blockCol_flipAt_self p ε hzp, hε.2]
          cases γ <;> simp
        · intro ε hε
          simp only [coe_filter, Set.mem_ofPred_eq] at hε ⊢
          refine ⟨(hfix ε).2 hε.1, ?_⟩
          rw [blockCol_flipAt_self p ε hzp]
          have h2 := hε.2
          revert h2
          cases blockCol ε z <;> cases γ <;> simp
        · intro ε _; exact flipAt_flipAt p ε
        · intro ε _; exact flipAt_flipAt p ε
      have := card_filter_add_card_filter_not (s := A) (fun ε => blockCol ε z = γ)
      omega

/-- The blocks visited by a list of block differences, read down from the top block `Y`. -/
private def blocks : ℕ → List ℕ → List ℕ
  | Y, [] => [Y]
  | Y, a :: l => Y :: blocks (Y - a) l

private lemma blocks_le : ∀ (l : List ℕ) (Y : ℕ), ∀ z ∈ blocks Y l, z ≤ Y
  | [], Y, z, hz => by simp [blocks] at hz; omega
  | a :: l, Y, z, hz => by
    simp only [blocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact le_rfl
    · exact (blocks_le l (Y - a) z hz).trans (Nat.sub_le _ _)

private lemma blocks_length : ∀ (l : List ℕ) (Y : ℕ), (blocks Y l).length = l.length + 1
  | [], _ => rfl
  | a :: l, Y => by simp [blocks, blocks_length l]

private lemma blocks_pairwise : ∀ (l : List ℕ) (Y : ℕ), (∀ a ∈ l, 1 ≤ a) → l.sum ≤ Y →
    (blocks Y l).Pairwise (· > ·)
  | [], _, _, _ => by simp [blocks]
  | a :: l, Y, hl, hs => by
    simp only [blocks, List.pairwise_cons]
    have ha : 1 ≤ a := hl a List.mem_cons_self
    simp only [List.sum_cons] at hs
    refine ⟨fun w hw => ?_, blocks_pairwise l (Y - a)
      (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (by omega)⟩
    have := blocks_le l (Y - a) w hw
    omega

/-- The event that the blocks of a list, read down from `Y`, all have one colour. -/
private def bad {P : ℕ} (ε : Fin P → Bool) (Y : ℕ) (l : List ℕ) : Bool :=
  decide (l.sum ≤ Y ∧ ∃ γ : Bool, ∀ z ∈ blocks Y l, blockCol ε z = γ)

private lemma card_bad {P : ℕ} (Y : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) (hY : Y / 2 < P) :
    2 ^ l.length * (univ.filter fun ε : Fin P → Bool => bad ε Y l = true).card ≤ 2 ^ P := by
  by_cases hs : l.sum ≤ Y
  · have hpw := blocks_pairwise l Y hl hs
    have hP : ∀ z ∈ blocks Y l, z / 2 < P := fun z hz =>
      lt_of_le_of_lt (Nat.div_le_div_right (blocks_le l Y z hz)) hY
    have h1 := card_mono true (blocks Y l) hpw hP
    have h2 := card_mono false (blocks Y l) hpw hP
    rw [blocks_length, pow_succ] at h1 h2
    have hsub : (univ.filter fun ε : Fin P → Bool => bad ε Y l = true) ⊆
        (univ.filter fun ε : Fin P → Bool => ∀ z ∈ blocks Y l, blockCol ε z = true) ∪
        (univ.filter fun ε : Fin P → Bool => ∀ z ∈ blocks Y l, blockCol ε z = false) := by
      intro ε hε
      simp only [mem_filter, mem_univ, true_and, bad, decide_eq_true_eq] at hε
      obtain ⟨_, γ, hγ⟩ := hε
      cases γ
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hγ⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hγ⟩)
    have h3 := card_le_card hsub
    have h4 := card_union_le
      (univ.filter fun ε : Fin P → Bool => ∀ z ∈ blocks Y l, blockCol ε z = true)
      (univ.filter fun ε : Fin P → Bool => ∀ z ∈ blocks Y l, blockCol ε z = false)
    set c1 := (univ.filter fun ε : Fin P → Bool => ∀ z ∈ blocks Y l, blockCol ε z = true).card
    set c2 := (univ.filter fun ε : Fin P → Bool => ∀ z ∈ blocks Y l, blockCol ε z = false).card
    calc 2 ^ l.length * (univ.filter fun ε : Fin P → Bool => bad ε Y l = true).card
        ≤ 2 ^ l.length * (c1 + c2) := Nat.mul_le_mul_left _ (h3.trans h4)
      _ ≤ 2 ^ P := by nlinarith
  · have h0 : (univ.filter fun ε : Fin P → Bool => bad ε Y l = true) = ∅ := by
      apply filter_eq_empty_iff.2
      intro ε _ h
      simp only [bad, decide_eq_true_eq] at h
      exact hs h.1
    rw [h0]
    simp

private lemma exists_good (P M D n : ℕ) (hM : ∀ Y < M, Y / 2 < P)
    (hcount : M * (seqs D n).card < 2 ^ n) :
    ∃ ε : Fin P → Bool, ∀ Y < M, ∀ l ∈ seqs D n, bad ε Y l = false := by
  set S := (range M) ×ˢ (seqs D n) with hS
  have hsum : 2 ^ n * ∑ ε : Fin P → Bool, (S.filter fun q => bad ε q.1 q.2 = true).card <
      2 ^ n * 2 ^ P := by
    calc 2 ^ n * ∑ ε : Fin P → Bool, (S.filter fun q => bad ε q.1 q.2 = true).card
        = ∑ q ∈ S, 2 ^ n *
            (univ.filter fun ε : Fin P → Bool => bad ε q.1 q.2 = true).card := by
          rw [mul_sum]
          simp only [card_filter, mul_sum]
          exact sum_comm
      _ ≤ ∑ q ∈ S, 2 ^ P := by
          apply sum_le_sum
          intro q hq
          obtain ⟨hY, hl⟩ := mem_product.1 hq
          obtain ⟨hlen, hall⟩ := seqs_props hl
          rw [← hlen]
          exact card_bad q.1 q.2 (fun a ha => (hall a ha).1) (hM q.1 (mem_range.1 hY))
      _ = S.card * 2 ^ P := by rw [sum_const, smul_eq_mul]
      _ < 2 ^ n * 2 ^ P := by
          rw [hS, card_product, card_range]
          exact Nat.mul_lt_mul_of_pos_right hcount (by positivity)
  have hlt : ∑ ε : Fin P → Bool, (S.filter fun q => bad ε q.1 q.2 = true).card <
      ∑ _ε : Fin P → Bool, 1 := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul, mul_one]
    exact lt_of_mul_lt_mul_left hsum (by positivity)
  obtain ⟨ε, _, hε⟩ := exists_lt_of_sum_lt hlt
  refine ⟨ε, fun Y hY l hl => ?_⟩
  have h0 : (S.filter fun q => bad ε q.1 q.2 = true) = ∅ := card_eq_zero.1 (by omega)
  by_contra hb
  have hmem : (Y, l) ∈ S.filter fun q => bad ε q.1 q.2 = true :=
    mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 hY, hl⟩, by simpa using hb⟩
  rw [h0] at hmem
  simp at hmem

/-! ### Waves -/

section Wave

variable {k : ℕ} {X : ℕ → ℕ}

private lemma mono_le (hmono : ∀ i, i + 1 < k → X i < X (i + 1)) :
    ∀ i j, i ≤ j → j < k → X i + (j - i) ≤ X j := by
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h1 := hmono j (by omega)
    have h2 := ih (by omega)
    omega

private lemma gap_anti (hdesc : ∀ i, i + 2 < k → X (i + 2) - X (i + 1) ≤ X (i + 1) - X i) :
    ∀ i j, i ≤ j → j + 1 < k → X (j + 1) - X j ≤ X (i + 1) - X i := by
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 : X (j + 1 + 1) - X (j + 1) ≤ X (j + 1) - X j := hdesc j (by omega)
    have h2 := ih (by omega)
    omega

private lemma window_anti (hmono : ∀ i, i + 1 < k → X i < X (i + 1))
    (hdesc : ∀ i, i + 2 < k → X (i + 2) - X (i + 1) ≤ X (i + 1) - X i) :
    ∀ L i j, i ≤ j → j + L < k → X (j + L) - X j ≤ X (i + L) - X i := by
  intro L
  induction L with
  | zero => intro i j _ _; simp
  | succ L ih =>
    intro i j hij hj
    have h1 := ih i j hij (by omega)
    have h2 := gap_anti hdesc (i + L) (j + L) (by omega) (by omega)
    have h3 := mono_le hmono j (j + L) (by omega) (by omega)
    have h4 := mono_le hmono i (i + L) (by omega) (by omega)
    have h5 := hmono (j + L) (by omega)
    have h6 := hmono (i + L) (by omega)
    rw [show j + (L + 1) = j + L + 1 by omega, show i + (L + 1) = i + L + 1 by omega]
    omega

private lemma block_window (hmono : ∀ i, i + 1 < k → X i < X (i + 1))
    (hdesc : ∀ i, i + 2 < k → X (i + 2) - X (i + 1) ≤ X (i + 1) - X i) (b : ℕ) :
    ∀ L i j, i ≤ j → j + L < k → X (j + L) / b - X j / b ≤ X (i + L) / b - X i / b + 1 := by
  intro L i j hij hj
  have h1 := mono_le hmono j (j + L) (by omega) hj
  have h2 := mono_le hmono i (i + L) (by omega) (by omega)
  exact div_sub_div_le (by omega) (by omega) (window_anti hmono hdesc L i j hij hj)

private lemma tail_gap {P b : ℕ} (ε : Fin P → Bool) (hb : 0 < b)
    (hmono : ∀ i, i + 1 < k → X i < X (i + 1))
    (hdesc : ∀ i, i + 2 < k → X (i + 2) - X (i + 1) ≤ X (i + 1) - X i)
    (hcol : ∀ i < k, blockCol ε (X i / b) = blockCol ε (X 0 / b)) :
    ∀ j, j + 2 * b + 1 ≤ k → b < X (j + 1) - X j := by
  intro j hj
  by_contra hcon
  push Not at hcon
  have hrun := short_run ε hb X j (2 * b) (fun i hi => by
      have h1 := gap_anti hdesc j (j + i) (by omega) (by omega)
      have h2 := hmono (j + i) (by omega)
      have h3 := hmono j (by omega)
      omega)
    (fun i hi => by rw [hcol (j + i) (by omega), hcol j (by omega)])
  have := mono_le hmono j (j + 2 * b) (by omega) (by omega)
  omega

private lemma sum_gaps (hmono : ∀ i, i + 1 < k → X i < X (i + 1)) (g : ℕ) :
    ∀ s, s + 1 < k → (∀ j ≤ s, g ≤ X (j + 1) - X j) → X 0 + (s + 1) * g ≤ X (s + 1) := by
  intro s
  induction s with
  | zero =>
    intro hs h
    have h1 := h 0 le_rfl
    have h2 := hmono 0 (by omega)
    omega
  | succ s ih =>
    intro hs h
    have h1 := ih (by omega) (fun j hj => h j (by omega))
    have h2 := h (s + 1) le_rfl
    have h3 := hmono (s + 1) (by omega)
    rw [add_mul, one_mul]
    omega

end Wave

/-! ### Block-difference lists of waves -/

/-- The list `[e (j - 1), …, e 0]`. -/
private def revList (e : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 => e j :: revList e j

/-- Invariant for the state of `revList e j`. -/
private def StateInvariant (D : ℕ) (e : ℕ → ℕ) (j : ℕ) (s : ℕ × Bool × Bool) : Prop :=
  s.1 ≤ D ∧ (∀ i < j, s.1 ≤ e i) ∧ (s.1 = D ∨ ∃ i < j, s.1 = e i) ∧
    (s.2.2 = true ↔ (0 < j ∧ e (j - 1) = s.1)) ∧
    (s.2.1 = true → ∃ i, i + 2 ≤ j ∧ e i = s.1 ∧ e (i + 1) = s.1)

private lemma revList_mem (D : ℕ) (e : ℕ → ℕ) (n : ℕ)
    (hpos : ∀ i < n, 1 ≤ e i) (hD : ∀ i < n, e i ≤ D + 1)
    (hW1 : ∀ i j, i < j → j < n → e j ≤ e i + 1)
    (hW2 : ∀ i j, i < j → j + 1 < n → e j + e (j + 1) ≤ e i + e (i + 1) + 1) :
    ∀ j ≤ n, revList e j ∈ seqs D j ∧ StateInvariant D e j (stateOf D (revList e j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by simp [revList, seqs], ?_⟩
    simp [StateInvariant, revList, stateOf]
  | succ j ih =>
    intro hj
    obtain ⟨hmem, hinv⟩ := ih (by omega)
    have hst : stateOf D (revList e (j + 1)) = step (stateOf D (revList e j)) (e j) := rfl
    rcases hS : stateOf D (revList e j) with ⟨m, ph, lo⟩
    rw [hS] at hinv hst
    obtain ⟨hmD, hmle, hmeq, hlo, hph⟩ := hinv
    simp only at hmD hmle hmeq hlo hph
    have hok : ok (m, ph, lo) (e j) = true := by
      simp only [ok, decide_eq_true_eq]
      refine ⟨hpos j (by omega), ?_, ?_⟩
      · rcases hmeq with h | ⟨i, hi, h⟩
        · have := hD j (by omega); omega
        · have := hW1 i j hi (by omega); omega
      · intro hph' hlo'
        obtain ⟨i, hi, hei, hei1⟩ := hph hph'
        have hj0 : 0 < j := by omega
        have hne : e (j - 1) ≠ m := by
          intro h
          have := hlo.2 ⟨hj0, h⟩
          simp [hlo'] at this
        have hge := hmle (j - 1) (by omega)
        have hw := hW2 i (j - 1) (by omega) (by omega)
        rw [show j - 1 + 1 = j by omega] at hw
        omega
    refine ⟨mem_seqs_succ.2 ⟨revList e j, hmem, e j, by have := hD j (by omega); omega,
      by rw [hS]; exact hok, rfl⟩, ?_⟩
    rw [hst]
    simp only [ok, decide_eq_true_eq] at hok
    by_cases h1 : e j < m
    · have hstep : step (m, ph, lo) (e j) = (e j, false, true) := by simp [step, h1]
      rw [hstep]
      simp only [StateInvariant]
      refine ⟨by omega, fun i hi => ?_, Or.inr ⟨j, by omega, rfl⟩, by simp, by simp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have := hmle i hi; omega
      · exact le_rfl
    · by_cases h2 : e j = m
      · have hstep : step (m, ph, lo) (e j) = (m, ph || lo, true) := by simp [step, h2]
        rw [hstep]
        simp only [StateInvariant]
        refine ⟨hmD, fun i hi => ?_, ?_, by simp [h2], ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact hmle i hi
          · omega
        · rcases hmeq with h | ⟨i, hi, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨i, by omega, h⟩
        · intro hor
          rcases Bool.or_eq_true_iff.1 hor with hp | hl
          · obtain ⟨i, hi, hei, hei1⟩ := hph hp
            exact ⟨i, by omega, hei, hei1⟩
          · obtain ⟨hj0, hej⟩ := hlo.1 hl
            exact ⟨j - 1, by omega, hej, by rw [show j - 1 + 1 = j by omega, h2]⟩
      · have hstep : step (m, ph, lo) (e j) = (m, ph, false) := by simp [step, h1, h2]
        rw [hstep]
        simp only [StateInvariant]
        have h3 : e j = m + 1 := by omega
        refine ⟨hmD, fun i hi => ?_, ?_, by simp [h3], ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact hmle i hi
          · omega
        · rcases hmeq with h | ⟨i, hi, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨i, by omega, h⟩
        · intro hp
          obtain ⟨i, hi, hei, hei1⟩ := hph hp
          exact ⟨i, by omega, hei, hei1⟩

private lemma revList_blocks (y : ℕ → ℕ) (n : ℕ) (hy : ∀ i < n, y i ≤ y (i + 1)) :
    ∀ j ≤ n, (revList (fun i => y (i + 1) - y i) j).sum = y j - y 0 ∧
      ∀ z ∈ blocks (y j) (revList (fun i => y (i + 1) - y i) j), ∃ i ≤ j, z = y i := by
  have hmon : ∀ i j, i ≤ j → j ≤ n → y i ≤ y j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact (ih (by omega)).trans (hy j (by omega))
  intro j
  induction j with
  | zero => intro _; simp [revList, blocks]
  | succ j ih =>
    intro hj
    obtain ⟨hsum, hbl⟩ := ih (by omega)
    have h1 := hy j (by omega)
    have h2 := hmon 0 j (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · simp only [revList, List.sum_cons, hsum]
      omega
    · intro z hz
      simp only [revList, blocks, List.mem_cons] at hz
      rw [show y (j + 1) - (y (j + 1) - y j) = y j by omega] at hz
      rcases hz with rfl | hz
      · exact ⟨j + 1, le_rfl, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := hbl z hz
        exact ⟨i, by omega, rfl⟩

private lemma sq_le_four_pow (q : ℕ) : (q + 1) ^ 2 ≤ 4 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e1 : (q + 1 + 1) ^ 2 = q ^ 2 + 4 * q + 4 := by ring
    have e2 : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    rw [pow_succ 4]
    omega

/-- For `512 q ≤ k < 512 (q + 1)` with `q ≥ 4`, there is a colouring of
`{1, …, (k - 192 q + 1) (64 q² + 1)}` with no monochromatic `k`-term descending wave. -/
private theorem lower_bound (q : ℕ) (hq : 4 ≤ q) (k : ℕ) (hk1 : 512 * q ≤ k)
    (hk2 : k < 512 * (q + 1)) :
    ¬ ForcesMonochromaticWave k ((k - 192 * q + 1) * (64 * q * q + 1)) := by
  obtain ⟨b, hb_def⟩ : ∃ b, b = 64 * q := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (k - 192 * q + 1) * (64 * q * q + 1) := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨M, hM⟩ : ∃ M, M = N / b + 1 := ⟨_, rfl⟩
  have hb : 0 < b := by omega
  -- counting the bad patterns
  have hMle : M ≤ 513 * 4 ^ q := by
    have h1 : N ≤ b * ((k + 1) * (q + 1)) := by
      rw [hN, hb_def]
      have : k - 192 * q + 1 ≤ k + 1 := by omega
      calc (k - 192 * q + 1) * (64 * q * q + 1) ≤ (k + 1) * (64 * q * (q + 1)) := by
            gcongr; nlinarith
        _ = 64 * q * ((k + 1) * (q + 1)) := by ring
    have h2 : N / b ≤ (k + 1) * (q + 1) := Nat.div_le_of_le_mul h1
    have h3 : (k + 1) * (q + 1) ≤ 512 * (q + 1) ^ 2 := by nlinarith
    have h4 := sq_le_four_pow q
    have h5 : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hkey : M * (7 ^ (64 * q) * (82 * 64 ^ q)) < 8 ^ (64 * q) := by
    have hbase : 20 * (256 * 7 ^ 64) ≤ 8 ^ 64 := by norm_num
    have h20 : 20 ^ 4 ≤ 20 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    have hpos : 0 < (256 * 7 ^ 64) ^ q := by positivity
    calc M * (7 ^ (64 * q) * (82 * 64 ^ q))
        ≤ 513 * 4 ^ q * (7 ^ (64 * q) * (82 * 64 ^ q)) := by gcongr
      _ = 42066 * (256 * 7 ^ 64) ^ q := by
          rw [mul_pow, pow_mul, show (256 : ℕ) = 4 * 64 by norm_num, mul_pow]; ring
      _ < 20 ^ 4 * (256 * 7 ^ 64) ^ q := by
          apply Nat.mul_lt_mul_of_pos_right _ hpos; norm_num
      _ ≤ 20 ^ q * (256 * 7 ^ 64) ^ q := Nat.mul_le_mul_right _ h20
      _ = (20 * (256 * 7 ^ 64)) ^ q := (mul_pow _ _ _).symm
      _ ≤ (8 ^ 64) ^ q := Nat.pow_le_pow_left hbase q
      _ = 8 ^ (64 * q) := by rw [← pow_mul]
  have hcount : M * (seqs q (64 * q)).card < 2 ^ (64 * q) := by
    have hc := card_seqs q (64 * q)
    have h8 : 8 ^ (64 * q) = 4 ^ (64 * q) * 2 ^ (64 * q) := by
      rw [← mul_pow]; norm_num
    have : 4 ^ (64 * q) * (M * (seqs q (64 * q)).card) < 4 ^ (64 * q) * 2 ^ (64 * q) := by
      calc 4 ^ (64 * q) * (M * (seqs q (64 * q)).card)
          = M * (4 ^ (64 * q) * (seqs q (64 * q)).card) := by ring
        _ ≤ M * (7 ^ (64 * q) * (82 * 64 ^ q)) := Nat.mul_le_mul_left _ hc
        _ < 8 ^ (64 * q) := hkey
        _ = _ := h8
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨ε, hε⟩ := exists_good M M q (64 * q) (fun Y hY => by omega) hcount
  -- a monochromatic wave gives a bad pattern
  intro hF
  obtain ⟨x, ⟨hsm, hwave⟩, hrange, γ, hcol⟩ :=
    hF (fun z => if blockCol ε (z / b) then 0 else 1)
  have hk0 : 0 < k := by omega
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℕ, X = fun i => if h : i < k then x ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have hXk : ∀ i (h : i < k), X i = x ⟨i, h⟩ := fun i h => by simp [hX, h]
  have hmono : ∀ i, i + 1 < k → X i < X (i + 1) := by
    intro i hi
    rw [hXk i (by omega), hXk (i + 1) hi]
    exact hsm (Fin.mk_lt_mk.2 (by omega))
  have hdesc : ∀ i, i + 2 < k → X (i + 2) - X (i + 1) ≤ X (i + 1) - X i := by
    intro i hi
    have h := hwave ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, hi⟩ rfl rfl
    have h1 : x ⟨i, by omega⟩ < x ⟨i + 1, by omega⟩ := hsm (Fin.mk_lt_mk.2 (by omega))
    have h2 : x ⟨i + 1, by omega⟩ < x ⟨i + 2, hi⟩ := hsm (Fin.mk_lt_mk.2 (by omega))
    rw [hXk i (by omega), hXk (i + 1) (by omega), hXk (i + 2) hi]
    omega
  have hfin : ∀ (g : Fin 2) (u v : Bool), ((if u then (0 : Fin 2) else 1) = g) →
      ((if v then (0 : Fin 2) else 1) = g) → u = v := by decide
  have hcolX : ∀ i < k, blockCol ε (X i / b) = blockCol ε (X 0 / b) := by
    intro i hi
    have h1 := hcol ⟨i, hi⟩
    have h2 := hcol ⟨0, hk0⟩
    rw [← hXk i hi] at h1
    rw [← hXk 0 hk0] at h2
    exact hfin γ _ _ h1 h2
  have hrangeX : ∀ i < k, 1 ≤ X i ∧ X i ≤ N := by
    intro i hi
    rw [hXk i hi]
    exact hrange ⟨i, hi⟩
  have htail := tail_gap ε hb hmono hdesc hcolX
  obtain ⟨s, hs⟩ : ∃ s, s = k - 192 * q := ⟨_, rfl⟩
  have hbig : q * b < X (s + 1) - X s := by
    by_contra hle
    push Not at hle
    obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, e = fun i => X (s + i + 1) / b - X (s + i) / b :=
      ⟨_, rfl⟩
    have hgap : ∀ i < 64 * q, b < X (s + i + 1) - X (s + i) ∧
        X (s + i + 1) - X (s + i) ≤ q * b := by
      intro i hi
      refine ⟨htail (s + i) (by omega), ?_⟩
      have := gap_anti hdesc s (s + i) (by omega) (by omega)
      omega
    have hpos : ∀ i < 64 * q, 1 ≤ e i := by
      intro i hi
      obtain ⟨h1, -⟩ := hgap i hi
      have : (X (s + i) + b) / b ≤ X (s + i + 1) / b := Nat.div_le_div_right (by omega)
      rw [Nat.add_div_right _ hb] at this
      rw [he]
      dsimp only
      omega
    have hD : ∀ i < 64 * q, e i ≤ q + 1 := by
      intro i hi
      obtain ⟨-, h2⟩ := hgap i hi
      have : X (s + i + 1) / b ≤ (X (s + i) + q * b) / b := Nat.div_le_div_right (by omega)
      rw [Nat.add_mul_div_right _ _ hb] at this
      rw [he]
      dsimp only
      omega
    have hbw := block_window hmono hdesc b
    have hymono : ∀ i, i + 1 < k → X i / b ≤ X (i + 1) / b := fun i hi =>
      Nat.div_le_div_right (hmono i hi).le
    have hW1 : ∀ i j, i < j → j < 64 * q → e j ≤ e i + 1 := by
      intro i j hij hj
      have := hbw 1 (s + i) (s + j) (by omega) (by omega)
      rw [he]
      dsimp only
      omega
    have hW2 : ∀ i j, i < j → j + 1 < 64 * q → e j + e (j + 1) ≤ e i + e (i + 1) + 1 := by
      intro i j hij hj
      have h := hbw 2 (s + i) (s + j) (by omega) (by omega)
      have a1 := hymono (s + i) (by omega)
      have a2 : X (s + i + 1) / b ≤ X (s + i + 2) / b := hymono (s + i + 1) (by omega)
      have a3 := hymono (s + j) (by omega)
      have a4 : X (s + j + 1) / b ≤ X (s + j + 2) / b := hymono (s + j + 1) (by omega)
      rw [he]
      simp only
      rw [show s + (i + 1) = s + i + 1 by omega, show s + (j + 1) = s + j + 1 by omega,
        show s + i + 1 + 1 = s + i + 2 by omega, show s + j + 1 + 1 = s + j + 2 by omega]
      omega
    have hmem := (revList_mem q e (64 * q) hpos hD hW1 hW2 (64 * q) le_rfl).1
    have hyb := revList_blocks (fun i => X (s + i) / b) (64 * q)
      (fun i hi => hymono (s + i) (by omega)) (64 * q) le_rfl
    have hee : (fun i => X (s + (i + 1)) / b - X (s + i) / b) = e := by
      rw [he]; funext i; rw [show s + (i + 1) = s + i + 1 by omega]
    rw [hee] at hyb
    obtain ⟨hsum, hbl⟩ := hyb
    have hY : X (s + 64 * q) / b < M := by
      have := (hrangeX (s + 64 * q) (by omega)).2
      have : X (s + 64 * q) / b ≤ N / b := Nat.div_le_div_right this
      omega
    have hbad := hε (X (s + 64 * q) / b) hY (revList e (64 * q)) hmem
    simp only [bad, decide_eq_false_iff_not, not_and, not_exists] at hbad
    apply hbad (by rw [hsum]; exact Nat.sub_le _ _) (blockCol ε (X 0 / b))
    intro z hz
    obtain ⟨i, hi, rfl⟩ := hbl z hz
    exact hcolX (s + i) (by omega)
  have hall : ∀ j ≤ s, q * b + 1 ≤ X (j + 1) - X j := by
    intro j hj
    have := gap_anti hdesc j s hj (by omega)
    omega
  have hsum := sum_gaps hmono (q * b + 1) s (by omega) hall
  have h1 := (hrangeX 0 hk0).1
  have h2 := (hrangeX (s + 1) (by omega)).2
  have hqb : q * b = 64 * q * q := by rw [hb_def]; ring
  rw [hqb] at hsum
  have hNs : N = (s + 1) * (64 * q * q + 1) := by rw [hN, hs]
  rw [hNs] at h2
  omega

end CubicOrder

/--
**Alon–Spencer: the descending-wave number has cubic order.** For natural numbers $k$ and $n$, say
that $n$ forces a $k$-term wave if every colouring of $\{1, \dots, n\}$ with two colours has a
monochromatic $k$-term descending wave. There are real numbers $c > 0$ and $C$ such that for all
sufficiently large $k$, every natural number $n$ that forces a $k$-term wave satisfies
$n \ge c k^3$, and the natural number $\lfloor \max(C k^3, 0) \rfloor$ forces a $k$-term wave.
Writing $f(k)$ for the least $n$ that forces a $k$-term wave, this says $f(k) \asymp k^3$.

Source: T. F. Bloom,
Erdős Problems, Problem #781, https://www.erdosproblems.com/781 (status DISPROVED); resolution: N.
Alon and J. Spencer, Ascending waves, J. Combin. Theory Ser. A 52 (1989), 275-287; T. C. Brown, P.
Erdős and A. R. Freedman, Quasi-progressions and descending waves, J. Combin. Theory Ser. A 53
(1990), 81-95, Alon-Spencer Theorem 1.1: c_1 k³ ≤ f(k) ≤ c_2 k³ for all k ≥ 1, the upper bound being
Brown, Erdős and Freedman's f(k) ≤ k³/3 - 4k/3 + 3; Brown, Erdős and Freedman also proved k² - k + 1
≤ f(k) and asked whether it is the exact value, and Alon and Spencer: 'Here we show that this is
false', https://web.math.princeton.edu/~nalon/PDFS/Publications1/Ascending%20waves.pdf.
-/
theorem waveNumberCubicOrder_holds : waveNumberCubicOrder := by
  refine ⟨1 / 32768, 1, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2048] with k hk
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q, q = k / 512 := ⟨_, rfl⟩
    have hq4 : 4 ≤ q := by omega
    have hk1 : 512 * q ≤ k := by omega
    have hk2 : k < 512 * (q + 1) := by omega
    have hnN : (k - 192 * q + 1) * (64 * q * q + 1) < n := by
      by_contra hle
      push Not at hle
      apply CubicOrder.lower_bound q hq4 k hk1 hk2
      intro c
      obtain ⟨x, hx, hr, γ, hγ⟩ := hn c
      exact ⟨x, hx, fun i => ⟨(hr i).1, (hr i).2.trans hle⟩, γ, hγ⟩
    have hcube : k ^ 3 ≤ 32768 * n := by
      have h1 : k ≤ 2 * (k - 192 * q + 1) := by omega
      have h2 : k ≤ 1024 * q := by omega
      calc k ^ 3 = k * k * k := by ring
        _ ≤ (1024 * q) * (1024 * q) * (2 * (k - 192 * q + 1)) := by gcongr
        _ ≤ 32768 * ((k - 192 * q + 1) * (64 * q * q + 1)) := by nlinarith
        _ ≤ 32768 * n := by omega
    have hcube' : (k : ℝ) ^ 3 ≤ 32768 * (n : ℝ) := by exact_mod_cast hcube
    linarith
  · have hfl : ⌊(1 : ℝ) * (k : ℝ) ^ 3⌋₊ = k ^ 3 := by
      rw [one_mul]
      exact_mod_cast Nat.floor_natCast (k ^ 3)
    rw [hfl]
    exact CubicOrder.forcesMonochromaticWave_cube k (by omega)

end MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted
