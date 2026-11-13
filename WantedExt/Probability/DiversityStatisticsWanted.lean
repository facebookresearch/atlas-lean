/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integer sequences for diversity statistics

Statements from Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", *Journal
of Integer Sequences* 29 (2026), Article 26.1.5
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Rosenberg/rosen5.html>).

A sample of size `N` is recorded by its list of type
counts. The Gini-Simpson index is `1 - ∑ (a / N)^2`, so
its number of distinct values `γ(N)` equals the number
of distinct values of `∑ a^2`; the Shannon index is
`-∑ (a / N) log (a / N)` and `σ(N)` counts its distinct
values. The bounds on `γ` were verified by partition
enumeration for `N ≤ 30`.

Propositions 1 and 2 (bounds quoted from Rosenberg and
from Aw and Rosenberg) and Theorem 3 use the paper's
bounding functions `M_min`, `M_max`, `S_min`, `S_max`
(Eqs. (1)-(4) of Section 2), here `diversityMmin`,
`diversityMmax`, `diversitySmin`, `diversitySmax`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

/-- The number of possible values of the Gini-Simpson
index across all samples of size `N`, counted as the
number of distinct sums of squared cell counts. -/
noncomputable def giniSimpsonCount (N : ℕ) : ℕ :=
  Set.ncard {s : ℕ | ∃ l : List ℕ, l.sum = N ∧
    (l.map (fun a => a ^ 2)).sum = s}

/-- The number of possible values of the Shannon
index `-∑ (a / N) log (a / N)` across all samples of
size `N` (with the convention `0 log 0 = 0`, which
matches `Real.log 0 = 0`). -/
noncomputable def shannonCount (N : ℕ) : ℕ :=
  Set.ncard {v : ℝ | ∃ l : List ℕ, l.sum = N ∧
    v = -(l.map (fun a => ((a : ℝ) / N) * Real.log ((a : ℝ) / N))).sum}

/-- **Proposition 4**: `γ(N) ≤ (1 / 2) N^2 - (1 / 2) N + 1`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 4. -/
theorem_wanted giniSimpsonCount_le (N : ℕ) :
    (giniSimpsonCount N : ℚ) ≤ (1 / 2) * N ^ 2 - (1 / 2) * N + 1

/-- **Proposition 5**: `γ(N)` is bounded below by
`(1 / 3) m (m^2 + 3r - 1) + 1`, where `N = C(m + 1, 2) + r`
with `0 ≤ r ≤ m`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 5. -/
theorem_wanted giniSimpsonCount_ge_triangular (N m r : ℕ)
    (hN : N = (m + 1) * m / 2 + r) (hr : r ≤ m) :
    (1 / 3) * (m : ℚ) * ((m : ℚ) ^ 2 + 3 * r - 1) + 1 ≤
      (giniSimpsonCount N : ℚ)

/-- **Proposition 6**: `γ(N)` is bounded below by
`(⌊N^2 / 5⌋ - N) / 2`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 6. -/
theorem_wanted giniSimpsonCount_ge (N : ℕ) :
    (((N ^ 2 / 5 : ℕ) : ℚ) - N) / 2 ≤ (giniSimpsonCount N : ℚ)

/-- **Proposition 7**: `γ(N) ~ (1 / 2) N^2`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 7. -/
theorem_wanted giniSimpsonCount_asymp :
    Filter.Tendsto
      (fun N : ℕ => (giniSimpsonCount N : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2))

/-- **Proposition 8**: for all `N ≥ 1`,
`σ(N) ≤ exp (π √(2 / 3) √N)`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 8. -/
theorem_wanted shannonCount_le (N : ℕ) (hN : 1 ≤ N) :
    (shannonCount N : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt (2 / 3) * Real.sqrt N)

/-- **Theorem 9**: `σ(N)` grows faster than every
polynomial: for every (nonzero) polynomial `q`,
`lim_{N → ∞} σ(N) / |q(N)| = ∞`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Theorem 9. -/
theorem_wanted shannonCount_superpolynomial
    (q : Polynomial ℝ) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => (shannonCount N : ℝ) / |q.eval (N : ℝ)|)
      Filter.atTop Filter.atTop

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

/-- **Proposition 1** (quoted from Rosenberg, Thm. 2.7): for a
probability vector `p` on `I ≥ 2` cells with at least two
nonzero entries, `J = ∑ p_i^2` and `M = max p_i`,
`M_min(J) ≤ M ≤ M_max(J)`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Proposition 1 (`jis-2026-26.1.5-prop-1`). `M` is any
greatest value of `p`. -/
theorem_wanted diversityMmin_le_max_le_diversityMmax {I : ℕ} (hI : 2 ≤ I) (p : Fin I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hp2 : ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0)
    (M : ℝ) (hM : IsGreatest (Set.range p) M) :
    diversityMmin (∑ i, p i ^ 2) ≤ M ∧ M ≤ diversityMmax I (∑ i, p i ^ 2)

/-- **Proposition 2** (quoted from Aw and Rosenberg,
Cor. 3.16): for a probability vector `p` on `I ≥ 2` cells
with at least two nonzero entries, `M = max p_i` and Shannon
index `S = -∑ p_i log p_i`, `S_min(M) ≤ S ≤ S_max(M)`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Proposition 2 (`jis-2026-26.1.5-prop-2`). `0 log 0 = 0`
matches `Real.log 0 = 0`. -/
theorem_wanted diversitySmin_le_shannon_le_diversitySmax {I : ℕ} (hI : 2 ≤ I) (p : Fin I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hp2 : ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0)
    (M : ℝ) (hM : IsGreatest (Set.range p) M) :
    diversitySmin M ≤ -∑ i, p i * Real.log (p i) ∧
      -∑ i, p i * Real.log (p i) ≤ diversitySmax I M

/-- **Theorem 3**: for a probability vector `p` on `I ≥ 2`
cells with at least two nonzero entries and Gini-Simpson index
`H = 1 - ∑ p_i^2`, the Shannon index satisfies
`S_min(M_max(1 - H)) ≤ S ≤ S_max(M_min(1 - H))`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", Journal of
Integer Sequences 29 (2026), Article 26.1.5, Theorem 3 (`jis-2026-26.1.5-thm-3`). The paper's
hypothesis `0 < H ≤ 1 - 1/I` holds for every such `p` and is
not repeated; `1 - H` is written as `∑ p_i^2`. -/
theorem_wanted diversitySmin_diversityMmax_le_shannon_le {I : ℕ} (hI : 2 ≤ I) (p : Fin I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hp2 : ∃ i j, i ≠ j ∧ p i ≠ 0 ∧ p j ≠ 0) :
    diversitySmin (diversityMmax I (∑ i, p i ^ 2)) ≤ -∑ i, p i * Real.log (p i) ∧
      -∑ i, p i * Real.log (p i) ≤ diversitySmax I (diversityMmin (∑ i, p i ^ 2))

end MathlibExt.Probability.DiversityStatisticsWanted
