/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction

/-!
# The golden ratio, factorials, and the Lambert `W` function

Wanted statements from Petojević, Gorjanac Ranitović, Rastovac and Mandić on the golden
sequence `α n` (OEIS A214048), the counting sequence `d m` (OEIS A181716), and bounds for
the left factorial `!n = ∑_{k<n} k!` (OEIS A003422) by Kurepa's partial integral.

The paper's real sequence `a n = -(n - 1) W₋₁(-(1/(n-1)) (4/7)^(1/(n-1)))` uses the
lower real branch `W₋₁` of the Lambert `W` function. That branch is not defined in the
library, so each statement quantifies over `a` with `n - 1 ≤ a` and
`lambertMap (-a / (n - 1)) = -(1/(n-1)) (4/7)^(1/(n-1))`: writing `y = -a / (n - 1)`,
these say `y ≤ -1` and `y * exp y` equals the argument, which characterizes
`y = W₋₁(argument)` uniquely (`existsUnique_lambertMap_lower_preimage` in
`MathlibExt.Analysis.SpecialFunctions.LambertWFunction`). The same encoding is used for the two-parameter sequence
`A n m` with `4/7` replaced by `4/(7m)`. `exists_lambertSequence` proves that such `a`
(and `A`) exist for `n ≥ 4`, so the statements are not vacuous.
-/

namespace MetaMathlibExt

open Real

@[expose] public section

/-- The golden sequence `α n` (OEIS A214048): the least positive integer `m` with
`n! ≤ φ ^ m`, where `φ` is the golden ratio. This is the paper's definition (4),
`α n = m ⇔ φ ^ (m - 1) ≤ n! ≤ φ ^ m` with `m` positive; `n!` is never a power of `φ`
for `n ≥ 2`, and `α 1 = 1`.

Source: Aleksandar Petojević, Marjana Gorjanac Ranitović, Dragan Rastovac and Milinko
Mandić, *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer
Sequences 27 (2024), Article 24.5.7, Section 2.2, definition (4). -/
public noncomputable def goldenFactorialExponent (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ (n.factorial : ℝ) ≤ goldenRatio ^ m}

/-- The set defining `α n` is nonempty: some positive power of `φ` is at least `n!`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2, definition (4). -/
public theorem exists_goldenRatio_pow_ge_factorial (n : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ (n.factorial : ℝ) ≤ goldenRatio ^ m := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (n.factorial : ℝ) one_lt_goldenRatio
  refine ⟨max m 1, le_max_right _ _, hm.le.trans ?_⟩
  exact pow_le_pow_right₀ one_lt_goldenRatio.le (le_max_left _ _)

/-- `α n` is positive and `n! ≤ φ ^ (α n)`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2, definition (4). -/
public theorem goldenFactorialExponent_mem (n : ℕ) :
    1 ≤ goldenFactorialExponent n ∧
      (n.factorial : ℝ) ≤ goldenRatio ^ goldenFactorialExponent n :=
  Nat.sInf_mem (exists_goldenRatio_pow_ge_factorial n)

/-- Minimality of `α n`: every positive `m` with `n! ≤ φ ^ m` satisfies `α n ≤ m`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2, definition (4). -/
public theorem goldenFactorialExponent_le {n m : ℕ} (hm : 1 ≤ m)
    (h : (n.factorial : ℝ) ≤ goldenRatio ^ m) : goldenFactorialExponent n ≤ m :=
  Nat.sInf_le ⟨hm, h⟩

/-- `α 1 = 1`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Table 3. -/
public theorem goldenFactorialExponent_one : goldenFactorialExponent 1 = 1 :=
  le_antisymm (goldenFactorialExponent_le le_rfl (by simpa using one_lt_goldenRatio.le))
    (goldenFactorialExponent_mem 1).1

/-- `α 2 = 2`, since `φ < 2 ≤ φ ^ 2 = φ + 1`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Table 3. -/
public theorem goldenFactorialExponent_two : goldenFactorialExponent 2 = 2 := by
  have h2 : ((Nat.factorial 2 : ℕ) : ℝ) ≤ goldenRatio ^ 2 := by
    rw [goldenRatio_sq]
    norm_num [Nat.factorial]
    linarith [one_lt_goldenRatio]
  refine le_antisymm (goldenFactorialExponent_le (by norm_num) h2) ?_
  obtain ⟨h1, h⟩ := goldenFactorialExponent_mem 2
  by_contra hlt
  have hm1 : goldenFactorialExponent 2 = 1 := by omega
  rw [hm1] at h
  norm_num [Nat.factorial] at h
  linarith [goldenRatio_lt_two]

/-- The sequence `d` (OEIS A181716) with `d 0 = 0`, `d 1 = 1` and
`d m = d (m - 1) + d (m - 2) + (-1) ^ m`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2 (definition before Lemma 3). -/
public def alternatingSignFibonacci : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => alternatingSignFibonacci (m + 1) + alternatingSignFibonacci m + (-1) ^ (m + 2)

/-- The recurrence `d (m + 2) = d (m + 1) + d m + (-1) ^ (m + 2)`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2. -/
public theorem alternatingSignFibonacci_add_two (m : ℕ) :
    alternatingSignFibonacci (m + 2) =
      alternatingSignFibonacci (m + 1) + alternatingSignFibonacci m + (-1) ^ (m + 2) :=
  rfl

/-- The first values `d 0, …, d 4 = 0, 1, 2, 2, 5`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Example 5. -/
public theorem alternatingSignFibonacci_small_values :
    alternatingSignFibonacci 0 = 0 ∧ alternatingSignFibonacci 1 = 1 ∧
      alternatingSignFibonacci 2 = 2 ∧ alternatingSignFibonacci 3 = 2 ∧
      alternatingSignFibonacci 4 = 5 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> norm_num [alternatingSignFibonacci]

/-- Kurepa's partial integral `!n(x) = ∫₀ˣ e^{-t} (t^n - 1)/(t - 1) dt`, written with the
geometric sum `∑_{k<n} t^k` in place of `(t^n - 1)/(t - 1)` (they agree for `t ≠ 1`, and the
singularity at `t = 1` is removable). The paper's `b n`, `β n` and `B n m` are its values
at `a n`, `α n` and `A n m`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 1 (the function `!z(x)`) and Sections 3.1-3.3. -/
public noncomputable def kurepaPartialIntegral (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (-t) * ∑ k ∈ Finset.range n, t ^ k

/-- The partial integral vanishes at `x = 0`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 1. -/
public theorem kurepaPartialIntegral_zero (n : ℕ) : kurepaPartialIntegral n 0 = 0 := by
  simp [kurepaPartialIntegral]

/-- Lemma 2: `α (n-1) + ⌊ln n / ln φ⌋ ≤ α n ≤ α (n-1) + ⌊ln n / ln φ⌋ + 1` for `n > 1`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 2 (`jis-2024-24.5.7-lem-2`). -/
public theorem_wanted goldenFactorialExponent_succ_bounds (n : ℕ) (hn : 1 < n) :
    goldenFactorialExponent (n - 1) + ⌊Real.logb goldenRatio n⌋₊ ≤
        goldenFactorialExponent n ∧
      goldenFactorialExponent n ≤
        goldenFactorialExponent (n - 1) + ⌊Real.logb goldenRatio n⌋₊ + 1

/-- Lemma 3: for a positive integer `m`, `d m` is the number of positive integers `n` with
`⌊ln n / ln φ⌋ = m`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 3 (`jis-2024-24.5.7-lem-3`). -/
public theorem_wanted ncard_floor_logb_goldenRatio_eq_alternatingSignFibonacci (m : ℕ)
    (hm : 1 ≤ m) :
    (({n : ℕ | 1 ≤ n ∧ ⌊Real.logb goldenRatio n⌋₊ = m}.ncard : ℕ) : ℤ) =
      alternatingSignFibonacci m

/-- Existence of the paper's Lambert sequences: for `n ≥ 4` and `0 < c ≤ 1` there is `a ≥ n - 1`
with `lambertMap (-a / (n - 1)) = -(1/(n-1)) c^(1/(n-1))`, i.e.
`a = -(n - 1) W₋₁(-(1/(n-1)) c^(1/(n-1)))`. With `c = 4/7` this is `a n`, with `c = 4/(7m)`
(`m ≥ 1`) it is `A n m`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 3.1 (the lower branch `W₋₁` defining `a n` and `A n m`). -/
public theorem exists_lambertSequence {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) :
    ∃ a : ℝ, (n : ℝ) - 1 ≤ a ∧
      lambertMap (-a / ((n : ℝ) - 1)) = -(1 / ((n : ℝ) - 1)) * c ^ (1 / ((n : ℝ) - 1)) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hcp : 0 < c ^ (1 / ((n : ℝ) - 1)) := Real.rpow_pos_of_pos hc0 _
  have hcle : c ^ (1 / ((n : ℝ) - 1)) ≤ 1 := Real.rpow_le_one hc0.le hc1 (by positivity)
  have he : (1 / 3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hq : 1 / ((n : ℝ) - 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  obtain ⟨⟨y, hy⟩, hyx⟩ := (existsUnique_lambertMap_lower_preimage
    (x := -(1 / ((n : ℝ) - 1)) * c ^ (1 / ((n : ℝ) - 1)))
    (by nlinarith [one_div_pos.2 hpos]) (by nlinarith [one_div_pos.2 hpos])).exists
  refine ⟨-((n : ℝ) - 1) * y, by nlinarith, ?_⟩
  rw [show -(-((n : ℝ) - 1) * y) / ((n : ℝ) - 1) = y by field_simp]
  exact hyx

/-- Theorem 6 (main result): `α n > a n` for `n > 4`, where
`a n = -(n - 1) W₋₁(-(1/(n-1)) (4/7)^(1/(n-1)))` is encoded by `n - 1 ≤ a` and
`lambertMap (-a / (n - 1)) = -(1/(n-1)) (4/7)^(1/(n-1))` (see the module docstring).

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 6 (`jis-2024-24.5.7-thm-6`). -/
public theorem_wanted lambertSequence_lt_goldenFactorialExponent (n : ℕ) (hn : 4 < n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    a < goldenFactorialExponent n

/-- Lemma 8: `2n - 4 < (3/4) a n` for `n ≥ 4`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 8 (`jis-2024-24.5.7-lem-8`). -/
public theorem_wanted two_mul_sub_four_lt_lambertSequence (n : ℕ) (hn : 4 ≤ n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    2 * (n : ℝ) - 4 < 3 / 4 * a

/-- Lemma 9: `∑_{t=0}^{k} a_n^t / t! < a_n^{k+1} / (k+1)!` for `n ≥ 5` and `0 ≤ k < n - 2`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 9 (`jis-2024-24.5.7-lem-9`). -/
public theorem_wanted sum_pow_div_factorial_lt_lambertSequence (n k : ℕ) (hn : 5 ≤ n)
    (hk : k < n - 2) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    ∑ t ∈ Finset.range (k + 1), a ^ t / (t.factorial : ℝ) <
      a ^ (k + 1) / ((k + 1).factorial : ℝ)

/-- Theorem 10: `b n < !n < b n + 1` for `n ≥ 5`, where `b n = !n(a n)` is Kurepa's partial
integral at `a n` and `!n = ∑_{k<n} k!`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 10 (`jis-2024-24.5.7-thm-10`). -/
public theorem_wanted kurepaPartialIntegral_lambertSequence_bounds (n : ℕ) (hn : 5 ≤ n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    kurepaPartialIntegral n a < ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) < kurepaPartialIntegral n a + 1

/-- Theorem 12: `β n < !n < β n + 1` for every positive integer `n`, where `β n = !n(α n)`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 12 (`jis-2024-24.5.7-thm-12`). -/
public theorem_wanted kurepaPartialIntegral_goldenFactorialExponent_bounds (n : ℕ)
    (hn : 1 ≤ n) :
    kurepaPartialIntegral n (goldenFactorialExponent n) <
        ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) <
        kurepaPartialIntegral n (goldenFactorialExponent n) + 1

/-- Theorem 14: `B n m < !n < B n m + 1/m` for `n ≥ 5` and positive `m`, where
`B n m = !n(A n m)` and `A n m = -(n - 1) W₋₁(-(1/(n-1)) (4/(7m))^(1/(n-1)))` is encoded by
`n - 1 ≤ A` and `lambertMap (-A / (n - 1)) = -(1/(n-1)) (4/(7m))^(1/(n-1))`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 14 (`jis-2024-24.5.7-thm-14`). -/
public theorem_wanted kurepaPartialIntegral_lambertSequence_two_bounds (n m : ℕ)
    (hn : 5 ≤ n) (hm : 1 ≤ m) (A : ℝ) (hA : (n : ℝ) - 1 ≤ A)
    (hW : lambertMap (-A / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / (7 * m) : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    kurepaPartialIntegral n A < ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) < kurepaPartialIntegral n A + 1 / m

/-- Corollary 15: `!n = ⌊β n⌋ + 1` for every positive integer `n`, and for `n > 4`,
`!n = ⌊b n⌋ + 1 = ⌊B n m + 1/m⌋` for every positive `m`.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Corollary 15 (`jis-2024-24.5.7-cor-15`). -/
public theorem_wanted leftFactorial_eq_floor_kurepaPartialIntegral :
    (∀ n : ℕ, 1 ≤ n →
      ⌊kurepaPartialIntegral n (goldenFactorialExponent n)⌋ + 1 =
        ∑ k ∈ Finset.range n, (k.factorial : ℤ)) ∧
    (∀ n : ℕ, 4 < n → ∀ a : ℝ, (n : ℝ) - 1 ≤ a →
      lambertMap (-a / ((n : ℝ) - 1)) =
        -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) →
      ⌊kurepaPartialIntegral n a⌋ + 1 = ∑ k ∈ Finset.range n, (k.factorial : ℤ)) ∧
    (∀ n m : ℕ, 4 < n → 1 ≤ m → ∀ A : ℝ, (n : ℝ) - 1 ≤ A →
      lambertMap (-A / ((n : ℝ) - 1)) =
        -(1 / ((n : ℝ) - 1)) * (4 / (7 * m) : ℝ) ^ (1 / ((n : ℝ) - 1)) →
      ⌊kurepaPartialIntegral n A + 1 / m⌋ = ∑ k ∈ Finset.range n, (k.factorial : ℤ))

end

end MetaMathlibExt
