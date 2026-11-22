/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.UniformSpace.UniformConvergence

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- The `q`-weighted binary digit sum `s_q(k) = ∑_{i ≥ 0} ω_i q^{i+1}`, where
`k = ∑_i ω_i 2^i` is the binary expansion of `k` (`ω_i` is the `i`-th entry of
`Nat.digits 2 k`, least significant first).

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1 (definition of `s_q`). -/
def qWeightedDigitSum {R : Type*} [CommRing R] (q : R) (k : ℕ) : R :=
  ∑ i ∈ range (Nat.digits 2 k).length, ((Nat.digits 2 k).getD i 0 : R) * q ^ (i + 1)

/-- The partial sums `S_q(n) = ∑_{k=0}^{n-1} s_q(k)` of the `q`-weighted binary digit sum.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1 (definition of `S_q`). -/
def qWeightedDigitPartialSum {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  ∑ k ∈ range n, qWeightedDigitSum q k

/-- The Takagi-Landsberg function `𝒯_a(x) = ∑_{n ≥ 0} a^n τ(2^n x)`, where
`τ(x) = |x - round x|` is the distance from `x` to the nearest integer. The parameter `a`
ranges over `ℝ` or `ℂ`; the series converges for `‖a‖ < 1`, and at dyadic rationals it is a
finite sum.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1.1, equation (TakagiLandsberg). -/
noncomputable def takagiLandsberg {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) (x : ℝ) : 𝕜 :=
  ∑' n : ℕ, a ^ n * ((|2 ^ n * x - round (2 ^ n * x)| : ℝ) : 𝕜)

/-- `s_q(0) = 0`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1. -/
theorem qWeightedDigitSum_zero {R : Type*} [CommRing R] (q : R) : qWeightedDigitSum q 0 = 0 := by
  simp [qWeightedDigitSum]

/-- The binary recursion `s_q(k) = q (k mod 2) + q s_q(⌊k/2⌋)` for `k > 0`, which gives the
paper's relations `s_q(2j) = q s_q(j)` and `s_q(2j+1) = q s_q(j) + q`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, proof of Theorem 1, equations (s(2j)) and (s(2j+1)). -/
theorem qWeightedDigitSum_of_pos {R : Type*} [CommRing R] (q : R) {k : ℕ} (hk : 0 < k) :
    qWeightedDigitSum q k = q * ((k % 2 : ℕ) : R) + q * qWeightedDigitSum q (k / 2) := by
  unfold qWeightedDigitSum
  rw [Nat.digits_def' (by norm_num) hk, List.length_cons, sum_range_succ', mul_sum]
  simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add, pow_one]
  rw [add_comm]
  congr 1
  · ring
  · refine sum_congr rfl fun i _ => ?_
    ring

/-- `𝒯_a(0) = 0`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1.1. -/
theorem takagiLandsberg_zero {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) : takagiLandsberg a 0 = 0 := by
  simp [takagiLandsberg]

/-- For `0 < N`, every dyadic grid point `t_j = j / 2^{N-1}` (`j ≤ 2^{N-1}`) of `[0, 1]`
satisfies `(S_q(t_j l) - t_j S_q(l)) / R = -q 𝒯_a(t_j)` with `l = 2^N`, `R = (2q)^{N-1}` and
`a = 1/(2q)`, for complex `q` with `|q| > 1/2`. Here `t_j l = 2j`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Proposition 1 (`integers-2026-A61-prop-1`). -/
public theorem_wanted qWeightedDigitPartialSum_dyadic_fluctuation (q : ℂ) (hq : 1 / 2 < ‖q‖)
    (N : ℕ) (hN : 0 < N) (j : ℕ) (hj : j ≤ 2 ^ (N - 1)) :
    (qWeightedDigitPartialSum q (2 * j) -
        ((j : ℂ) / 2 ^ (N - 1)) * qWeightedDigitPartialSum q (2 ^ N)) / (2 * q) ^ (N - 1) =
      -q * takagiLandsberg (1 / (2 * q)) ((j : ℝ) / 2 ^ (N - 1))

/-- The `q`-weighted Trollope-Delange formula: for real `q` with `|q| > 1/2`, `q ≠ 1`,
`a = 1/(2q)` and every positive integer `n`, with `k = ⌊log₂ n⌋ = Nat.log 2 n`,
`S_q(n) / n = (q/2) ((1 - q^{k+1})/(1 - q) - q^k F̂_q(log₂ n))`, where
`F̂_q(u) = 2^{1-u} 𝒯_a(2^{-(1-u)})` on `[0, 1)` extended with period `1` (evaluated at the
fractional part `{log₂ n}`).

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Theorem 1 (`integers-2026-A61-thm-1`). -/
public theorem_wanted qWeighted_trollopeDelange (q : ℝ) (hq : 1 / 2 < |q|) (hq1 : q ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    qWeightedDigitPartialSum q n / n =
      q / 2 * ((1 - q ^ (Nat.log 2 n + 1)) / (1 - q) -
        q ^ Nat.log 2 n *
          ((2 : ℝ) ^ (1 - Int.fract (Real.logb 2 n)) *
            takagiLandsberg (1 / (2 * q)) ((2 : ℝ) ^ (-(1 - Int.fract (Real.logb 2 n))))))

/-- Girgensohn's lemma: for `G : ℕ → ℝ`, the assignment `F((n - p_n)/p_n) := G(n)` on positive
integers `n`, with `p_n = 2^{⌊log₂ n⌋}`, is a well-defined function of the dyadic rational
`(n - p_n)/p_n ∈ [0, 1)` if and only if `G(2n) = G(n)` for all positive `n`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Lemma 1 (`integers-2026-A61-lem-1`), quoting Girgensohn,
*Digital Sums and Functional Equations*, Lemma 1. -/
public theorem_wanted dyadicMantissa_wellDefined_iff_doubling_invariant (G : ℕ → ℝ) :
    (∀ m n : ℕ, 0 < m → 0 < n →
        ((m : ℚ) - 2 ^ Nat.log 2 m) / 2 ^ Nat.log 2 m =
          ((n : ℚ) - 2 ^ Nat.log 2 n) / 2 ^ Nat.log 2 n → G m = G n) ↔
      ∀ n : ℕ, 0 < n → G (2 * n) = G n

/-- The carry into digit `i` when the natural number `j` is added to the dyadic integer
`ω = (ω₀, ω₁, …) ∈ ℤ₂ = ∏ {0, 1}` (binary addition, least significant digit first).

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5 (dyadic integers and the odometer). -/
def dyadicAddNatCarry (ω : ℕ → Fin 2) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => ((ω i : ℕ) + (j.testBit i).toNat + dyadicAddNatCarry ω j i) / 2

/-- The dyadic integer `ω + j` for `ω ∈ ℤ₂` and `j ∈ ℕ`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5 (dyadic integers and the odometer). -/
def dyadicAddNat (ω : ℕ → Fin 2) (j : ℕ) : ℕ → Fin 2 := fun i =>
  ⟨((ω i : ℕ) + (j.testBit i).toNat + dyadicAddNatCarry ω j i) % 2, Nat.mod_lt _ two_pos⟩

/-- The dyadic odometer `T ω = ω + 1`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
def dyadicOdometer (ω : ℕ → Fin 2) : ℕ → Fin 2 := dyadicAddNat ω 1

/-- `T(0) = (1, 0, 0, …)`: its first three digits.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
theorem dyadicOdometer_zero_apply :
    dyadicOdometer (fun _ => 0) 0 = 1 ∧ dyadicOdometer (fun _ => 0) 1 = 0 ∧
      dyadicOdometer (fun _ => 0) 2 = 0 := by
  decide

/-- The Haar (uniform product) measure on `ℤ₂ = ∏_{i ≥ 0} {0, 1}`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
noncomputable def dyadicHaar : MeasureTheory.Measure (ℕ → Fin 2) :=
  MeasureTheory.Measure.infinitePi fun _ => (PMF.uniformFintype (Fin 2)).toMeasure

/-- The Haar measure on `ℤ₂` is a probability measure.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
instance : MeasureTheory.IsProbabilityMeasure dyadicHaar := by
  unfold dyadicHaar
  infer_instance

/-- The odometer partial sums `S_{q,ω}(n) = ∑_{j<n} s_q(T^j ω)`, with
`s_q(ω) = ∑_{i ≥ 0} ω_i q^{i+1}`, extended to real `x ≥ 0` by linear interpolation:
`S_{q,ω}(x) = S_{q,ω}(⌊x⌋) + {x} s_q(T^{⌊x⌋} ω)`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Sections 4 and 5. -/
noncomputable def odometerDigitPartialSum (q : ℂ) (ω : ℕ → Fin 2) (x : ℝ) : ℂ :=
  (∑ j ∈ range ⌊x⌋₊, ∑' i : ℕ, ((dyadicOdometer^[j] ω i : ℕ) : ℂ) * q ^ (i + 1)) +
    ((Int.fract x : ℝ) : ℂ) * ∑' i : ℕ, ((dyadicOdometer^[⌊x⌋₊] ω i : ℕ) : ℂ) * q ^ (i + 1)

/-- `S_{q,ω}(0) = 0`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 5. -/
theorem odometerDigitPartialSum_zero (q : ℂ) (ω : ℕ → Fin 2) :
    odometerDigitPartialSum q ω 0 = 0 := by
  simp [odometerDigitPartialSum]

/-- The maximal absolute fluctuation of `t ↦ S_{q,ω}(t l) - t S_{q,ω}(l)` on `[0, 1]`.
This is the scale of the *canonical* normalizing coefficient of the sources: "the
normalizing coefficient `R_n` is canonically defined to be equal to the maximum in
`t ∈ [0, 1]` of `|𝒮(t·l_n(x)) - t·𝒮(l_n)|`".

Source: Aleksei Minabutdinov, *Limiting curves for the dyadic odometer and the generalized
Trollope-Delange formula*, Section 2.2 (definition of `φ_n` and `R_n`), and *A q-Weighted
Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Section 3
(definition of the normalization factor `R_n`). -/
noncomputable def odometerMaxFluctuation (q : ℂ) (ω : ℕ → Fin 2) (l : ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) 1,
    ‖odometerDigitPartialSum q ω ((t : ℝ) * (l : ℝ)) -
      (t : ℝ) * odometerDigitPartialSum q ω (l : ℝ)‖

/-- A **stabilizing sequence** for `(q, ω)` with **normalizing sequence** `R` and limiting
curve `φ`: a sequence `l_n` of positive integers tending to infinity and a sequence `R_n`
of nonzero scalars, unbounded in absolute value and eventually of the same order as the
canonical coefficient `odometerMaxFluctuation q ω (l n)`, such that the normalized
fluctuations `(S_{q,ω}(t l_n) - t S_{q,ω}(l_n)) / R_n` converge uniformly on `[0, 1]` to
the continuous function `φ`.

`R` is a *chosen* sequence of the canonical order, not forced to equal the maximal
fluctuation: with that equality every normalized fluctuation would have sup-norm `≤ 1`,
so the limit in Theorem 2 below could not be `-𝒯_a` (for example `𝒯_{3/4}(1/3) = 4/3`).
This matches the sources' usage, where `φ^{l_n,R_n}` is parametrized by the chosen `R_n`
(e.g. `R_n = (2q)^{n-1}` along `l_n = 2^n` in Article A61, Section 3); unbounded growth
of `R_n` is the necessary condition for a limiting curve recorded in the odometer paper.

Source: Aleksei Minabutdinov, *Limiting curves for the dyadic odometer and the generalized
Trollope-Delange formula*, Definition 1 and Section 3.1, restated in *A q-Weighted
Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Section 3. -/
def IsStabilizingSeq (q : ℂ) (ω : ℕ → Fin 2) (l : ℕ → ℕ) (R : ℕ → ℂ) (φ : ℝ → ℂ) : Prop :=
  (∀ n, 0 < l n) ∧ Filter.Tendsto l Filter.atTop Filter.atTop ∧
    (∀ n, R n ≠ 0) ∧
    Filter.Tendsto (fun n => ‖R n‖) Filter.atTop Filter.atTop ∧
    (∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
      c * odometerMaxFluctuation q ω (l n) ≤ ‖R n‖ ∧
        ‖R n‖ ≤ C * odometerMaxFluctuation q ω (l n)) ∧
    ContinuousOn φ (Set.Icc 0 1) ∧
    TendstoUniformlyOn
      (fun n (t : ℝ) => (odometerDigitPartialSum q ω (t * l n) -
        t * odometerDigitPartialSum q ω (l n)) / R n)
      φ Filter.atTop (Set.Icc 0 1)

/-- **Theorem 2** (quoted from the author's earlier work): for `1/2 < |q| < 1` and Haar-almost
every `ω ∈ ℤ₂` there are a stabilizing sequence `l_n` of positive integers and a normalizing
sequence `R_n` (in the sense of `IsStabilizingSeq`: nonzero, unbounded, and of the order
of the maximal fluctuation) such that
`φ^{l_n,R_n}_{q,ω}(t) = (S_{q,ω}(t l_n) - t S_{q,ω}(l_n))/R_n` converges uniformly on
`[0, 1]` to `-𝒯_a` with `a = 1/(2q)`.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Theorem 2 (`integers-2026-A61-thm-2`). -/
public theorem_wanted odometer_limitingCurve_eq_neg_takagi (q : ℂ) (hq : 1 / 2 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    ∀ᵐ ω ∂dyadicHaar, ∃ (l : ℕ → ℕ) (R : ℕ → ℂ),
      IsStabilizingSeq q ω l R (fun t => -takagiLandsberg (1 / (2 * q)) t)

end

end MetaMathlibExt
