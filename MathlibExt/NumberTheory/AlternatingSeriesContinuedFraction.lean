/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Analysis.PSeries

/-!
# Continued fractions of alternating series

The alternating series formed from successive three-step pattern denominators has the
prescribed continued fraction. The two-step and three-step denominator sequences are
defined by their continuant recurrences.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Convergent denominators of the two-step pattern.** For a natural number $\beta$ and a
sequence $(\omega_n)_{n \ge 0}$ of natural numbers, define natural numbers $q_n$ by $q_0 = 1$,
$q_1 = \omega_0$, and for every $n \ge 0$, $q_{2n+2} = q_{2n+1} + q_{2n}$ and
$q_{2n+3} = \omega_{n+1} q_{2n+1}^\beta q_{2n+2} + q_{2n+1}$.

When the $\omega_n$ are positive, these are the convergent denominators of the continued fraction
$[0; \omega_0, 1, \omega_1 q_1^\beta, 1, \omega_2 q_3^\beta, 1, \dots]$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.1, displays (e2) and (e22). -/
public def twoStepPatternDen (β : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => ω 0
  | n + 2 => if n % 2 = 0 then twoStepPatternDen β ω (n + 1) + twoStepPatternDen β ω n
      else ω (n / 2 + 1) * twoStepPatternDen β ω n ^ β * twoStepPatternDen β ω (n + 1) +
        twoStepPatternDen β ω n

/-- **Small values of the two-step pattern denominators.** For $\beta = 1$ and $\omega_n = 1$ for
all $n$, the convergent denominators $q_0, \dots, q_7$ of the two-step pattern are
$1, 1, 2, 3, 5, 18, 23, 432$ (the paper's first example).

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.1, first example. -/
public theorem twoStepPatternDen_one_one :
    (List.range 8).map (twoStepPatternDen 1 fun _ => 1) = [1, 1, 2, 3, 5, 18, 23, 432] := by
  decide

/-- **Convergent denominators of the three-step pattern.** For a natural number $\beta$ and a
sequence $(\omega_n)_{n \ge 0}$ of natural numbers, define natural numbers $q_n$ by $q_0 = 1$,
$q_1 = \omega_0$, and for every $n \ge 0$, $q_{3n+2} = q_{3n+1} + q_{3n}$,
$q_{3n+3} = q_{3n+2} + q_{3n+1}$ and $q_{3n+4} = \omega_{n+1} q_{3n+3} q_{3n+2}^\beta + q_{3n+2}$.

When the $\omega_n$ are positive, these are the convergent denominators of the continued fraction
$[0; \omega_0, 1, 1, \omega_1 q_2^\beta, 1, 1, \omega_2 q_5^\beta, \dots]$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.2, displays (e3) and (e33). -/
public def threeStepPatternDen (β : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => ω 0
  | n + 2 => if n % 3 = 2 then
        ω (n / 3 + 1) * threeStepPatternDen β ω (n + 1) * threeStepPatternDen β ω n ^ β +
          threeStepPatternDen β ω n
      else threeStepPatternDen β ω (n + 1) + threeStepPatternDen β ω n

/-- **Small values of the three-step pattern denominators.** For $\beta = 1$ and $\omega_n = 1$
for all $n$, the convergent denominators $q_0, \dots, q_7$ of the three-step pattern are
$1, 1, 2, 3, 8, 11, 19, 220$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.2, display (e33). -/
public theorem threeStepPatternDen_one_one :
    (List.range 8).map (threeStepPatternDen 1 fun _ => 1) = [1, 1, 2, 3, 8, 11, 19, 220] := by
  decide

namespace threeStepPattern_alternatingSeries_contFract

open GenContFract

/-- Read the digits from fractional parts satisfying the continued fraction algorithm. -/
private theorem digits_of_fracts (a : ℕ → ℕ) (f : ℕ → ℝ)
    (hpos : ∀ n, 0 < f n) (hlt : ∀ n, f n < 1)
    (hstep : ∀ n, (f n)⁻¹ = a n + f (n + 1)) :
    (GenContFract.of (f 0)).h = 0 ∧
      ∀ n, (GenContFract.of (f 0)).partDens.get? n = some (a n : ℝ) := by
  have hfloor : ⌊f 0⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨(hpos 0).le, hlt 0⟩
  refine ⟨by rw [of_h_eq_floor, hfloor, Int.cast_zero], ?_⟩
  have step (n : ℕ) : IntFractPair.of (f n)⁻¹ = ⟨a n, f (n + 1)⟩ := by
    have hf : ⌊(f n)⁻¹⌋ = (a n : ℤ) := by
      rw [hstep, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hpos (n + 1), hlt (n + 1)]
    simp only [IntFractPair.of, Int.fract, hf, Int.cast_natCast]
    rw [hstep, add_sub_cancel_left]
  have stream (n : ℕ) : IntFractPair.stream (f 0) (n + 1) = some ⟨a n, f (n + 1)⟩ := by
    induction n with
    | zero =>
      have hzero : IntFractPair.stream (f 0) 0 = some ⟨0, f 0⟩ := by
        simp [IntFractPair.stream, IntFractPair.of, Int.fract, hfloor]
      rw [IntFractPair.stream_succ_of_some hzero (hpos 0).ne', step]
    | succ n ih => rw [IntFractPair.stream_succ_of_some ih (hpos _).ne', step]
  intro n
  change ((GenContFract.of (f 0)).s.get? n).map Pair.b = _
  simp [get?_of_eq_some_of_succ_get?_intFractPair_stream (stream n)]

/-- Positive decreasing term magnitudes give strictly positive alternating tails. -/
private theorem alternating_tails (u : ℕ → ℝ) (hu : StrictAnti u) (hs : Summable u) :
    let t := fun n : ℕ => ∑' i : ℕ, (-1 : ℝ) ^ i * u (i + n)
    (∀ n, 0 < t n) ∧ ∀ n, t n + t (n + 1) = u n := by
  intro t
  have shifted (n : ℕ) : Summable (fun i => u (i + n)) := (summable_nat_add_iff n).2 hs
  constructor
  · intro n
    have lower := Antitone.alternating_series_le_tendsto
      (shifted n).tendsto_alternating_series_tsum
      (fun _ _ h => hu.antitone (Nat.add_le_add_right h n)) 1
    have hlt := hu (Nat.lt_succ_self n)
    apply lt_of_lt_of_le _ lower
    simpa [Finset.sum_range_succ, Nat.add_comm 1 n, sub_eq_add_neg] using sub_pos.mpr hlt
  · intro n
    have h := (shifted n).alternating.tsum_eq_zero_add
    apply eq_sub_iff_add_eq.mp
    simpa [t, pow_succ, Nat.add_right_comm, Nat.add_assoc, tsum_neg, sub_eq_add_neg] using h

/-- The continuant recurrence gives linear denominator growth and decreasing term magnitudes. -/
private theorem reciprocal_products (q a : ℕ → ℕ) (h₀ : q 0 = 1) (ha : ∀ n, 0 < a n)
    (h₁ : q 1 = a 0) (hrec : ∀ n, q (n + 2) = a (n + 1) * q (n + 1) + q n) :
    let u := fun n => 1 / ((q n : ℝ) * q (n + 1))
    (∀ n, 0 < q n) ∧ StrictAnti u ∧ Summable u := by
  intro u
  have hq (n : ℕ) : 0 < q n := by
    induction n using Nat.twoStepInduction with
    | zero => simp [h₀]
    | one => simpa [h₁] using ha 0
    | more n ih _ => rw [hrec]; omega
  have inc (n : ℕ) : q (n + 1) < q (n + 2) := by
    rw [hrec]
    exact (Nat.le_mul_of_pos_left _ (ha _)).trans_lt (Nat.lt_add_of_pos_right (hq n))
  have mono : Monotone q := monotone_nat_of_le_succ fun n => by
    cases n with
    | zero => rw [h₀, h₁]; exact ha 0
    | succ n => exact (inc n).le
  have grow (n : ℕ) : n + 1 ≤ q (n + 1) := by
    induction n with
    | zero => exact hq 1
    | succ n ih => exact lt_of_le_of_lt ih (inc n)
  refine ⟨hq, strictAnti_nat_of_succ_lt (fun n => ?_), ?_⟩
  · dsimp [u]
    have pos (k : ℕ) : (0 : ℝ) < q k := by exact_mod_cast hq k
    apply one_div_lt_one_div_of_lt (mul_pos (pos _) (pos _))
    rw [mul_comm (q n : ℝ)]
    apply mul_lt_mul_of_pos_left _ (pos _)
    exact_mod_cast (mono (Nat.le_succ n)).trans_lt (inc n)
  · apply (summable_nat_add_iff 1).mp
    have square := Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
    have bound := (summable_nat_add_iff 1).mpr square
    apply Summable.of_nonneg_of_le (f := fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      (fun n => by dsimp [u]; positivity) _ bound
    intro n
    dsimp [u]
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    gcongr
    · exact grow n
    · exact (grow n).trans (inc n).le

/-- Scale each tail by its initial denominator. The resulting positive remainders satisfy
the Euclidean algorithm, so successive remainder ratios are precisely the fractional parts. -/
private theorem digits_of_denominators (q a : ℕ → ℕ) (h₀ : q 0 = 1) (ha : ∀ n, 0 < a n)
    (h₁ : q 1 = a 0) (hrec : ∀ n, q (n + 2) = a (n + 1) * q (n + 1) + q n) :
    let s := fun n : ℕ => (-1 : ℝ) ^ n / ((q n : ℝ) * q (n + 1))
    Summable s ∧ (GenContFract.of (∑' n, s n)).h = 0 ∧
      ∀ n, (GenContFract.of (∑' n, s n)).partDens.get? n = some (a n : ℝ) := by
  intro s
  let u (n : ℕ) : ℝ := 1 / ((q n : ℝ) * q (n + 1))
  let t (n : ℕ) := ∑' i : ℕ, (-1 : ℝ) ^ i * u (i + n)
  obtain ⟨hq, hu, hsum⟩ := reciprocal_products q a h₀ ha h₁ hrec
  obtain ⟨ht, htail⟩ := alternating_tails u hu hsum
  have pos (n : ℕ) : (0 : ℝ) < q n := by exact_mod_cast hq n
  let r : ℕ → ℝ
    | 0 => 1
    | n + 1 => q n * t n
  have hr (n : ℕ) : 0 < r n := by
    cases n with
    | zero => exact zero_lt_one
    | succ n => exact mul_pos (pos n) (ht n)
  have det (n : ℕ) : q (n + 1) * r (n + 1) + q n * r (n + 2) = (1 : ℝ) := by
    change q (n + 1) * (q n * t n) + q n * (q (n + 1) * t (n + 1)) = (1 : ℝ)
    calc
      _ = (q n : ℝ) * q (n + 1) * (t n + t (n + 1)) := by ring
      _ = 1 := by
        rw [htail n]
        exact mul_one_div_cancel (mul_pos (pos _) (pos _)).ne'
  have rem (n : ℕ) : r n = a n * r (n + 1) + r (n + 2) := by
    cases n with
    | zero => simpa [h₀, h₁] using (det 0).symm
    | succ n =>
      have step : (q (n + 2) : ℝ) = a (n + 1) * (q (n + 1) : ℝ) + q n := by
        exact_mod_cast hrec n
      have next := det (n + 1)
      rw [show n + 1 + 1 = n + 2 by rfl, step] at next
      apply mul_left_cancel₀ (pos (n + 1)).ne'
      linear_combination det n - next
  let f (n : ℕ) := r (n + 1) / r n
  have hf (n : ℕ) : 0 < f n := div_pos (hr (n + 1)) (hr n)
  have hlt (n : ℕ) : f n < 1 := by
    apply (div_lt_one (hr n)).2
    calc
      r (n + 1) ≤ (a n : ℝ) * r (n + 1) := le_mul_of_one_le_left (hr (n + 1)).le
        (by exact_mod_cast (ha n : 1 ≤ a n))
      _ < r n := by linarith only [rem n, hr (n + 2)]
  have hstep (n : ℕ) : (f n)⁻¹ = a n + f (n + 1) := by
    change (r (n + 1) / r n)⁻¹ = a n + r (n + 2) / r (n + 1)
    rw [inv_div, rem n, add_div, mul_div_cancel_right₀ _ (hr (n + 1)).ne']
  have hstart : f 0 = ∑' n, s n := by
    simp [f, r, h₀, t, u, s, div_eq_mul_inv]
  have digits := digits_of_fracts a f hf hlt hstep
  rw [hstart] at digits
  refine ⟨?_, digits⟩
  simpa [s, div_eq_mul_inv] using hsum.alternating

end threeStepPattern_alternatingSeries_contFract

/-- **Three-step pattern as an alternating series.** Let $\beta$ be a natural number, let
$(\omega_n)_{n \ge 0}$ be positive integers, and let $(q_n)_{n \ge 0}$ be the convergent
denominators of the three-step pattern for $\beta$ and $(\omega_n)$. Then the series
$\sum_{i \ge 0} (-1)^i / (q_i q_{i+1})$ converges absolutely, and its sum $x$ has continued
fraction expansion $[a_0; a_1, a_2, \dots]$ with $a_0 = 0$, $a_1 = \omega_0$, and
$a_{3n+2} = a_{3n+3} = 1$ and $a_{3n+4} = \omega_{n+1} q_{3n+2}^\beta$ for every $n \ge 0$; that is,
$x = [0; \omega_0, 1, 1, \omega_1 q_2^\beta, 1, 1, \omega_2 q_5^\beta, \dots]$.

The paper assumes $\beta \ge 1$; the statement here also allows $\beta = 0$.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Proposition 8, under the hypotheses (e3) of Section 2.2. -/
public theorem threeStepPattern_alternatingSeries_contFract (β : ℕ) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := threeStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    Summable (fun i : ℕ => (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))) ∧
      (GenContFract.of x).h = 0 ∧ (GenContFract.of x).partDens.get? 0 = some (ω 0 : ℝ) ∧
      ∀ n : ℕ, (GenContFract.of x).partDens.get? (3 * n + 1) = some 1 ∧
        (GenContFract.of x).partDens.get? (3 * n + 2) = some 1 ∧
        (GenContFract.of x).partDens.get? (3 * n + 3) =
          some ((ω (n + 1) : ℝ) * q (3 * n + 2) ^ β) := by
  intro q x
  let a : ℕ → ℕ
    | 0 => ω 0
    | n + 1 => if n % 3 = 2 then ω (n / 3 + 1) * q n ^ β else 1
  have qpos (n : ℕ) : 0 < q n := by
    induction n using Nat.twoStepInduction with
    | zero => exact Nat.zero_lt_one
    | one => exact hω 0
    | more n ih _ =>
      change 0 < threeStepPatternDen β ω (n + 2)
      rw [threeStepPatternDen]
      split <;> exact Nat.add_pos_right _ ih
  have apos (n : ℕ) : 0 < a n := by
    cases n with
    | zero => exact hω 0
    | succ n =>
      dsimp [a]
      split
      · exact Nat.mul_pos (hω _) (pow_pos (qpos n) β)
      · decide
  have hrec (n : ℕ) : q (n + 2) = a (n + 1) * q (n + 1) + q n := by
    dsimp only [q, a]
    rw [threeStepPatternDen]
    split <;> simp_all only [one_mul, mul_right_comm]
  obtain ⟨hs, hhead, hdigit⟩ :=
    threeStepPattern_alternatingSeries_contFract.digits_of_denominators q a rfl apos rfl hrec
  refine ⟨hs, hhead, hdigit 0, fun n => ⟨?_, ?_, ?_⟩⟩
  · simpa [a] using hdigit (3 * n + 1)
  · simpa [a, Nat.add_mod] using hdigit (3 * n + 2)
  · have hdiv : (3 * n + 2) / 3 = n := by omega
    simpa [a, Nat.add_mod, hdiv] using hdigit (3 * n + 3)

end

end MetaMathlibExt
