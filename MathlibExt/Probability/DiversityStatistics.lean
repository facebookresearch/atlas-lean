/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Partition.ExponentialUpperBound

/-!
# Counts and bounds for diversity statistics

For type counts with total `N`, the sum of their squares is `N + 2 * k`, where `k` counts
pairs of observations of the same type. There are at most `N.choose 2` such pairs.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

/-- **Number of values of the Gini–Simpson index.** For a natural number $N$, $\gamma(N)$ is the
number of distinct values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$
of natural numbers with $a_1 + \dots + a_k = N$.

For $N \ge 1$, the Gini–Simpson index of a sample of size $N$ with type counts $a_1, \dots, a_k$ is
$1 - \sum_i (a_i / N)^2$, so $\gamma(N)$ is the number of possible values of the Gini–Simpson index
across all samples of size $N$. -/
noncomputable def giniSimpsonCount (N : ℕ) : ℕ :=
  Set.ncard {s : ℕ | ∃ l : List ℕ, l.sum = N ∧
    (l.map (fun a => a ^ 2)).sum = s}

private lemma sq_eq_add_twice_choose (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith only [ih]

-- The index counts unordered pairs belonging to the same type.
private lemma sum_sq_mem_image (l : List ℕ) :
    (l.map (fun a => a ^ 2)).sum ∈ (fun k => l.sum + 2 * k) '' Set.Iic (l.sum.choose 2) := by
  induction l with
  | nil => exact ⟨0, Nat.zero_le _, rfl⟩
  | cons a l ih =>
    obtain ⟨k, hk, heq⟩ := ih
    change k ≤ l.sum.choose 2 at hk
    simp only [List.map_cons, List.sum_cons]
    refine ⟨a.choose 2 + k, ?_, ?_⟩
    · change a.choose 2 + k ≤ (a + l.sum).choose 2
      nlinarith only [hk, sq_eq_add_twice_choose a, sq_eq_add_twice_choose l.sum,
        sq_eq_add_twice_choose (a + l.sum), Nat.zero_le (a * l.sum)]
    · change a + l.sum + 2 * (a.choose 2 + k) = a ^ 2 + _
      rw [← heq, sq_eq_add_twice_choose a]
      ring

/-- **Upper bound on the number of Gini–Simpson values.** Let $\gamma(N)$ be the number of distinct
values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$ of natural numbers
with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the Gini–Simpson index
across samples of size $N$). Then for every natural number $N$,
$$\gamma(N) \le \tfrac{1}{2} N^2 - \tfrac{1}{2} N + 1.$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 4. -/
theorem giniSimpsonCount_le (N : ℕ) :
    (giniSimpsonCount N : ℚ) ≤ (1 / 2) * N ^ 2 - (1 / 2) * N + 1 := by
  have hcount : giniSimpsonCount N ≤ N.choose 2 + 1 := by
    calc
      giniSimpsonCount N ≤ ((fun k => N + 2 * k) '' Set.Iic (N.choose 2)).ncard := by
        apply Set.ncard_le_ncard _ ((Set.finite_Iic _).image _)
        rintro s ⟨l, rfl, rfl⟩
        exact sum_sq_mem_image l
      _ ≤ (Set.Iic (N.choose 2)).ncard := Set.ncard_image_le
      _ = _ := Set.ncard_Iic_nat _
  calc
    (giniSimpsonCount N : ℚ) ≤ (N.choose 2 : ℚ) + 1 := by exact_mod_cast hcount
    _ = _ := by rw [Nat.cast_choose_two]; ring

/-- **Number of values of the Shannon index.** For a natural number $N$, $\sigma(N)$ is the number
of distinct real numbers $-\sum_{i=1}^{k} (a_i / N) \log (a_i / N)$ over all finite sequences $(a_1,
\dots, a_k)$ of natural numbers with $a_1 + \dots + a_k = N$, where a term with $a_i = 0$ counts as
$0$ (the convention $0 \log 0 = 0$).

For $N \ge 1$, this is the number of possible values of the Shannon index across all samples of size
$N$. -/
noncomputable def shannonCount (N : ℕ) : ℕ :=
  Set.ncard {v : ℝ | ∃ l : List ℕ, l.sum = N ∧
    v = -(l.map (fun a => ((a : ℝ) / N) * Real.log ((a : ℝ) / N))).sum}

/-- **Upper bound on the number of Shannon values.** Let $\sigma(N)$ be the number of distinct real
numbers $-\sum_{i=1}^{k} (a_i / N) \log (a_i / N)$ over all finite sequences $(a_1, \dots, a_k)$ of
natural numbers with $a_1 + \dots + a_k = N$, where a term with $a_i = 0$ counts as $0$ (for $N \ge
1$, the number of possible values of the Shannon index across samples of size $N$). Then for every
natural number $N \ge 1$,
$$\sigma(N) \le \exp\left(\pi \sqrt{2/3} \sqrt{N}\right).$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 8. -/
theorem shannonCount_le (N : ℕ) (hN : 1 ≤ N) :
    (shannonCount N : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt (2 / 3) * Real.sqrt N) := by
  -- The partition bound also covers zero; retain the source's positive-size hypothesis.
  have _ := hN
  let term (a : ℕ) : ℝ := ((a : ℝ) / N) * Real.log ((a : ℝ) / N)
  let value (p : Nat.Partition N) : ℝ := -(p.parts.map term).sum
  have hcount : shannonCount N ≤ Fintype.card (Nat.Partition N) := by
    calc
      shannonCount N ≤ (Set.range value).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_range value)
        rintro _ ⟨l, hl, rfl⟩
        -- `ofSums` forgets the order and discards zeros, which contribute nothing.
        refine ⟨Nat.Partition.ofSums N l (by simpa only [Multiset.sum_coe] using hl), ?_⟩
        change -(((l : Multiset ℕ).filter (· ≠ 0)).map term).sum =
          -((l.flatMap (fun a : ℕ => [(a : ℝ)])).map (fun a => (a / N) * Real.log (a / N))).sum
        rw [← List.map_eq_flatMap, List.map_map]
        simp only [Multiset.filter_coe, Multiset.map_coe, Multiset.sum_coe, neg_inj]
        change ((l.filter (· ≠ 0)).map term).sum = (l.map term).sum
        simp only [ne_eq, decide_not]
        clear hl
        have hterm0 : term 0 = 0 := by simp [term]
        induction l with
        | nil => rfl
        | cons a l ih =>
          by_cases ha : a = 0
          · subst a
            simp [ih, hterm0]
          · simp [ha, ih]
      _ ≤ (Set.univ : Set (Nat.Partition N)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le
      _ = _ := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  exact (Nat.cast_le.mpr hcount).trans (Nat.Partition.card_le_exp N)

/-- `M_min(J) = (1 + √((⌈J⁻¹⌉ J - 1) / (⌈J⁻¹⌉ - 1))) / ⌈J⁻¹⌉`,
the lower bound for the maximal cell probability given
`J = ∑ p_i^2`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (1) (`M_min`). -/
noncomputable def diversityMmin (J : ℝ) : ℝ :=
  (1 + Real.sqrt (((⌈J⁻¹⌉ : ℝ) * J - 1) / ((⌈J⁻¹⌉ : ℝ) - 1))) / (⌈J⁻¹⌉ : ℝ)

/-- `M_max(J) = (1 + √((I J - 1)(I - 1))) / I`, the upper
bound for the maximal cell probability given `J = ∑ p_i^2`
over `I` cells.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (2) (`M_max`). -/
noncomputable def diversityMmax (I : ℕ) (J : ℝ) : ℝ :=
  (1 + Real.sqrt (((I : ℝ) * J - 1) * ((I : ℝ) - 1))) / I

/-- `S_min(M) = ⌊M⁻¹⌋ M log(1/M) + (1 - ⌊M⁻¹⌋ M) log(1 / (1 - ⌊M⁻¹⌋ M))`,
the lower bound for the Shannon index given the maximal
cell probability `M`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (3) (`S_min`), with the argument of the second
logarithm `1 / (1 - ⌊M⁻¹⌋ M)` as in Proposition 2 (Eq. (3)
misplaces a floor bracket). -/
noncomputable def diversitySmin (M : ℝ) : ℝ :=
  (⌊M⁻¹⌋ : ℝ) * M * Real.log (1 / M) +
    (1 - (⌊M⁻¹⌋ : ℝ) * M) * Real.log (1 / (1 - (⌊M⁻¹⌋ : ℝ) * M))

/-- `S_max(M) = M log(1/M) + (1 - M) log((I - 1) / (1 - M))`,
the upper bound for the Shannon index given the maximal
cell probability `M` over `I` cells.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (4) (`S_max`). -/
noncomputable def diversitySmax (I : ℕ) (M : ℝ) : ℝ :=
  M * Real.log (1 / M) + (1 - M) * Real.log (((I : ℝ) - 1) / (1 - M))

/-- Characteristic value: `M_min(1) = 1`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (1). -/
theorem diversityMmin_one : diversityMmin 1 = 1 := by
  simp [diversityMmin]

/-- Characteristic value: `M_max(1) = 1` for `I ≥ 1` cells.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (2). -/
theorem diversityMmax_one {I : ℕ} (hI : 1 ≤ I) : diversityMmax I 1 = 1 := by
  have hI' : (1 : ℝ) ≤ I := by exact_mod_cast hI
  have h : Real.sqrt (((I : ℝ) * 1 - 1) * ((I : ℝ) - 1)) = (I : ℝ) - 1 := by
    rw [mul_one]
    exact Real.sqrt_mul_self (by linarith)
  rw [diversityMmax, h]
  field_simp
  ring

/-- Characteristic value: `S_min(1) = 0`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (3). -/
theorem diversitySmin_one : diversitySmin 1 = 0 := by
  simp [diversitySmin]

/-- Characteristic value: `S_max(1) = 0`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Eq. (4). -/
theorem diversitySmax_one (I : ℕ) : diversitySmax I 1 = 0 := by
  simp [diversitySmax]

end MathlibExt.Probability.DiversityStatisticsWanted
