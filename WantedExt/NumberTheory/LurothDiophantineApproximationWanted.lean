/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import WantedExt.NumberTheory.LurothConsecutiveDigitsWanted

namespace MetaMathlibExt

open Filter MeasureTheory
open scoped ENNReal

@[expose] public section

/-! ### Classical well approximable numbers -/

/-- The set `W(ψ)` of `ψ`-well approximable numbers in `[0, 1)`: the `x` such that
`|x - p/q| < ψ(q)/q` for some `p : ℤ` for infinitely many `q`. The fractions `p/q`
need not be reduced, so this differs from Mathlib's `addWellApproximable` (which uses
points of exact additive order `q`, i.e. reduced fractions). The value `ψ 0` is
irrelevant.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (1). -/
public def wellApproximableSet (ψ : ℕ → ℝ) : Set ℝ :=
  {x | x ∈ Set.Ico 0 1 ∧ ∃ᶠ q : ℕ in atTop, ∃ p : ℤ, |x - p / q| < ψ q / q}

/-- Every point of `wellApproximableSet ψ` lies in `[0, 1)`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (1). -/
public theorem wellApproximableSet_subset_Ico (ψ : ℕ → ℝ) :
    wellApproximableSet ψ ⊆ Set.Ico 0 1 :=
  fun _ hx => hx.1

/-- The lower order at infinity `liminf_{q → ∞} -log ψ(q) / log q` of `1/ψ`, valued in
`ℝ≥0∞` (for `ψ` with values in `(0, 1]` the ratio is nonnegative once `q ≥ 2`, and the
order may be infinite).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public noncomputable def lowerOrderAtInfinity (ψ : ℕ → ℝ) : ℝ≥0∞ :=
  liminf (fun q : ℕ => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)) atTop

/-- The upper order at infinity `limsup_{q → ∞} -log ψ(q) / log q` of `1/ψ`, valued in
`ℝ≥0∞`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public noncomputable def upperOrderAtInfinity (ψ : ℕ → ℝ) : ℝ≥0∞ :=
  limsup (fun q : ℕ => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)) atTop

/-- For `q ≥ 2` and `τ` real, `-log (q^τ)⁻¹ / log q = τ`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public theorem orderRatio_rpow_inv (τ : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      ENNReal.ofReal (-Real.log (((q : ℝ) ^ τ)⁻¹) / Real.log q) = ENNReal.ofReal τ := by
  filter_upwards [eventually_ge_atTop 2] with q hq
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq').ne'
  rw [Real.log_inv, Real.log_rpow (by linarith), neg_neg, mul_div_assoc, div_self hlog,
    mul_one]

/-- The lower order at infinity of `q ↦ q^{-τ}` is `τ`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, remark after Theorem 7. -/
public theorem lowerOrderAtInfinity_rpow_inv (τ : ℝ) :
    lowerOrderAtInfinity (fun q => ((q : ℝ) ^ τ)⁻¹) = ENNReal.ofReal τ := by
  rw [lowerOrderAtInfinity, liminf_congr (orderRatio_rpow_inv τ), liminf_const]

/-- The upper order at infinity of `q ↦ q^{-τ}` is `τ`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, remark after Theorem 7. -/
public theorem upperOrderAtInfinity_rpow_inv (τ : ℝ) :
    upperOrderAtInfinity (fun q => ((q : ℝ) ^ τ)⁻¹) = ENNReal.ofReal τ := by
  rw [upperOrderAtInfinity, limsup_congr (orderRatio_rpow_inv τ), limsup_const]

/-- Khintchine's theorem: for non-increasing `ψ` with values in `[0, 1/2]`, the Lebesgue
measure of `W(ψ)` is `0` if `∑ ψ(q)` converges and `1` if it diverges. Here `ψ` is
defined on all of `ℕ` and also assumed non-increasing at `0` (extend by `ψ 0 = ψ 1`).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 1 (Khintchine). -/
public theorem_wanted volume_wellApproximableSet_khintchine (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 ≤ ψ q) (hψ1 : ∀ q, ψ q ≤ 1 / 2) (hψ : Antitone ψ) :
    (Summable ψ → volume (wellApproximableSet ψ) = 0) ∧
      (¬ Summable ψ → volume (wellApproximableSet ψ) = 1)

/-- The Jarník–Besicovitch theorem: for `τ ≥ 1`, the set `W(τ)` of `x ∈ [0, 1)` with
`|x - p/q| < q^{-(1+τ)}` for infinitely many `q` has Hausdorff dimension `2/(1+τ)`.
Here `W(τ) = W(ψ)` with `ψ(q) = q^{-τ}`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 2 (Jarník;
Besicovitch). -/
public theorem_wanted dimH_wellApproximableSet_rpow (τ : ℝ) (hτ : 1 ≤ τ) :
    dimH (wellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) = ENNReal.ofReal (2 / (1 + τ))

/-- Dodson's theorem: for non-increasing `ψ` with values in `(0, 1/2]` whose lower order
at infinity `τ_ψ` is at least `1`, `dim W(ψ) = 2/(1+τ_ψ)` (read as `0` when
`τ_ψ = ∞`). The paper allows `ψ(q) = 0`; positivity is assumed here because Lean's
`Real.log 0 = 0` would misread `τ_ψ`. The paper's "`τ_ψ ≥ 1`" is taken as a hypothesis:
without it the formula fails (constant `ψ = 1/4` gives `τ_ψ = 0` and `dim W(ψ) = 1`).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 3 (Dodson). -/
public theorem_wanted dimH_wellApproximableSet_dodson (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1 / 2) (hψ : Antitone ψ)
    (hτ : 1 ≤ lowerOrderAtInfinity ψ) :
    dimH (wellApproximableSet ψ) = 2 * (1 + lowerOrderAtInfinity ψ)⁻¹

/-! ### Lüroth expansions -/

/-! The Lüroth map `T(x) = ⌊1/x⌋ ((⌊1/x⌋ + 1) x - 1)` and the digits
`d_{n+1}(x) = ⌊1/T^n(x)⌋ + 1` of the paper are the existing `lurothMap` and `lurothDigitSeq`
of `WantedExt/NumberTheory/LurothConsecutiveDigitsWanted.lean` (digits indexed from `0`):
there `lurothMap x = d₁(x) (d₁(x) - 1) x - (d₁(x) - 1)` with `d₁(x) = ⌊1/x⌋ + 1`, which is the
same map on `(0, 1]`. -/

/-- The Lüroth denominator of a digit sequence, indexed from `0`:
`lurothDenominator d n = d n * ∏_{j < n} d j (d j - 1)`, i.e. the paper's `Q_{n+1}`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public def lurothDenominator (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  d n * ∏ j ∈ Finset.range n, d j * (d j - 1)

/-- The Lüroth convergent of a digit sequence, indexed from `0`:
`lurothConvergent d n = ∑_{k ≤ n} 1 / lurothDenominator d k`, i.e. the paper's
`x_{n+1} = P_{n+1}/Q_{n+1}`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public def lurothConvergent (d : ℕ → ℕ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), 1 / (lurothDenominator d k : ℚ)

/-- Every Lüroth digit of `1` is `2`, i.e. `1 = [2, 2, 2, ...]`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothDigitSeq_one (n : ℕ) : lurothDigitSeq 1 n = 2 := by
  rw [lurothDigitSeq, Function.iterate_fixed lurothMap_one, lurothDigit_one]

/-- `T(T(27/71)) = 27/71` and the first two digits of `27/71` are `3, 4`, so
`27/71 = [3, 4, 3, 4, ...]`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2 (example). -/
public theorem lurothMap_lurothMap_27_71 :
    lurothMap (27 / 71) = 20 / 71 ∧ lurothMap (20 / 71) = 27 / 71 := by
  have h1 : lurothDigit ((27 : ℝ) / 71) = 3 := by
    have : ⌊(1 : ℝ) / (27 / 71)⌋₊ = 2 := by
      rw [Nat.floor_eq_iff (by norm_num)]; norm_num
    rw [lurothDigit, this]
  have h2 : lurothDigit ((20 : ℝ) / 71) = 4 := by
    have : ⌊(1 : ℝ) / (20 / 71)⌋₊ = 3 := by
      rw [Nat.floor_eq_iff (by norm_num)]; norm_num
    rw [lurothDigit, this]
  constructor
  · rw [lurothMap, h1]; norm_num
  · rw [lurothMap, h2]; norm_num

/-- Recurrence `Q_{n+2} = Q_{n+1} (d_{n+1} - 1) d_{n+2}` (paper indexing).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public theorem lurothDenominator_succ (d : ℕ → ℕ) (n : ℕ) :
    lurothDenominator d (n + 1) = lurothDenominator d n * (d n - 1) * d (n + 1) := by
  simp only [lurothDenominator, Finset.prod_range_succ]
  ring

/-- For the constant digit sequence `2`, `Q_{n+1} = 2^{n+1}`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public theorem lurothDenominator_two (n : ℕ) :
    lurothDenominator (fun _ => 2) n = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lurothDenominator_succ, ih]; ring

/-- Recurrence `x_{n+2} = x_{n+1} + 1/Q_{n+2}` (paper indexing).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothConvergent_succ (d : ℕ → ℕ) (n : ℕ) :
    lurothConvergent d (n + 1) =
      lurothConvergent d n + 1 / (lurothDenominator d (n + 1) : ℚ) := by
  rw [lurothConvergent, Finset.sum_range_succ, ← lurothConvergent]

/-- The set `L(ψ)` of Lüroth `ψ`-well approximable numbers: the `x ∈ (0, 1]` with
`|x - P_n(x)/Q_n(x)| < ψ(Q_n(x))/Q_n(x)` for infinitely many `n`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public def lurothWellApproximableSet (ψ : ℕ → ℝ) : Set ℝ :=
  {x | x ∈ Set.Ioc 0 1 ∧ ∃ᶠ n in atTop,
    |x - lurothConvergent (lurothDigitSeq x) n| <
      ψ (lurothDenominator (lurothDigitSeq x) n) / lurothDenominator (lurothDigitSeq x) n}

/-- Every point of `lurothWellApproximableSet ψ` lies in `(0, 1]`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothWellApproximableSet_subset_Ioc (ψ : ℕ → ℝ) :
    lurothWellApproximableSet ψ ⊆ Set.Ioc 0 1 :=
  fun _ hx => hx.1

/-- The set `S` of all triples (numerator, denominator, last digit) of Lüroth
convergents of points of `(0, 1]`, stored as `(P/Q, Q, d)`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (16). -/
public def lurothTripleSet : Set (ℚ × ℕ × ℕ) :=
  {t | ∃ y ∈ Set.Ioc (0 : ℝ) 1, ∃ n,
    t = (lurothConvergent (lurothDigitSeq y) n, lurothDenominator (lurothDigitSeq y) n,
      lurothDigitSeq y n)}

/-- `(1/2, 2, 2) ∈ S`, from the first convergent of `1 = [2, 2, ...]`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (16). -/
public theorem half_two_two_mem_lurothTripleSet : ((1 / 2 : ℚ), 2, 2) ∈ lurothTripleSet := by
  refine ⟨1, ⟨one_pos, le_rfl⟩, 0, ?_⟩
  simp [lurothConvergent, lurothDenominator, lurothDigitSeq_one]

/-- Lüroth convergents approximate from the left: for `x ∈ (0, 1]` and every `n`,
`0 < x - P_n/Q_n ≤ 1/((d_n - 1) Q_n)` (0-indexed here).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 1. -/
public theorem_wanted lurothConvergent_lt_le (x : ℝ) (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    0 < x - lurothConvergent (lurothDigitSeq x) n ∧
      x - lurothConvergent (lurothDigitSeq x) n ≤
        1 / (((lurothDigitSeq x n : ℝ) - 1) * lurothDenominator (lurothDigitSeq x) n)

/-- Applied mass transference principle: let `I_n = [c_n - r_n, c_n + r_n] ⊆ [0, 1]`
with `r_n → 0`, and `0 < s < 1`. If `[0, 1] ∩ limsup I_n^s` has Lebesgue measure `1`,
where `I_n^s` has the same centre and radius `r_n^s`, then
`H^s(limsup I_n) = ∞`, hence `dim limsup I_n ≥ s`. The endpoints `s = 0` and `s = 1`
admitted by the printed statement are excluded: for `s = 0`, `I_n = [1/2 - 1/(n+2),
1/2 + 1/(n+2)]` satisfies the hypothesis but `limsup I_n = {1/2}` has `H^0 = 1`; for
`s = 1`, `H^1` of a subset of `[0, 1]` is at most `1`. The paper's proof treats
`0 < s < 1`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 3. -/
public theorem_wanted hausdorffMeasure_limsup_closedBall_of_volume (c r : ℕ → ℝ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hr0 : ∀ n, 0 ≤ r n)
    (hI : ∀ n, Metric.closedBall (c n) (r n) ⊆ Set.Icc 0 1)
    (hr : Tendsto r atTop (nhds 0))
    (hfull : volume (Set.Icc 0 1 ∩
      limsup (fun n => Metric.closedBall (c n) (r n ^ s)) atTop) = 1) :
    μH[s] (limsup (fun n => Metric.closedBall (c n) (r n)) atTop) = ∞ ∧
      ENNReal.ofReal s ≤ dimH (limsup (fun n => Metric.closedBall (c n) (r n)) atTop)

/-- If `x ∈ (0, 1]` and `(P/Q, Q, d) ∈ S` satisfy `0 < x - P/Q ≤ 1/((d - 1) Q)`, then
`P/Q` is a Lüroth convergent of `x`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 4. -/
public theorem_wanted exists_lurothConvergent_eq_of_mem_lurothTripleSet (x : ℝ)
    (hx : x ∈ Set.Ioc 0 1) (t : ℚ × ℕ × ℕ) (ht : t ∈ lurothTripleSet)
    (hpos : 0 < x - t.1) (hle : x - t.1 ≤ 1 / (((t.2.2 : ℝ) - 1) * t.2.1)) :
    ∃ n, lurothConvergent (lurothDigitSeq x) n = t.1

/-- For `τ ≥ 0`, `L(τ) = limsup_k B_{τ,k}` where, for a triple `(P/Q, Q, d) ∈ S`,
`B = (P/Q, P/Q + Q^{-(1+τ)}) ∩ (P/Q, P/Q + 1/((d - 1) Q)]`. The limsup over the paper's
re-enumeration of `S` is stated as membership in `B_t` for infinitely many `t ∈ S`,
which does not depend on the enumeration.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 5. -/
public theorem_wanted lurothWellApproximableSet_rpow_eq_limsup (τ : ℝ) (hτ : 0 ≤ τ) :
    lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹) =
      {x | {t ∈ lurothTripleSet |
        x ∈ Set.Ioo (t.1 : ℝ) (t.1 + ((t.2.1 : ℝ) ^ (1 + τ))⁻¹) ∩
          Set.Ioc (t.1 : ℝ) (t.1 + (((t.2.2 : ℝ) - 1) * t.2.1)⁻¹)}.Infinite}

/-- For `ψ : ℕ → (0, 1]` with lower order at infinity `τ_ψ > 1`,
`L(ψ) = limsup_k (P_k/Q_k, P_k/Q_k + ψ(Q_k)/Q_k)` over the triples of `S`, stated as
membership for infinitely many triples (independent of the enumeration).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 7. -/
public theorem_wanted lurothWellApproximableSet_eq_limsup (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) (hτ : 1 < lowerOrderAtInfinity ψ) :
    lurothWellApproximableSet ψ =
      {x | {t ∈ lurothTripleSet |
        x ∈ Set.Ioo (t.1 : ℝ) (t.1 + ψ t.2.1 / t.2.1)}.Infinite}

/-- Tan–Zhou, a Lüroth analogue of Khintchine's theorem: for non-increasing
`ψ : ℕ → (0, 1]`, `L(L(ψ))` is `0` if `∑ -ψ(q) log ψ(q) / q` converges and `1` if it
diverges. The `q = 0` term is `0` in Lean; `ψ` is also assumed non-increasing at `0`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 4 (Tan and
Zhou). -/
public theorem_wanted volume_lurothWellApproximableSet (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) (hψ : Antitone ψ) :
    (Summable (fun q : ℕ => -ψ q * Real.log (ψ q) / q) →
        volume (lurothWellApproximableSet ψ) = 0) ∧
      (¬ Summable (fun q : ℕ => -ψ q * Real.log (ψ q) / q) →
        volume (lurothWellApproximableSet ψ) = 1)

/-- Cao–Wu–Zhang: for `τ ≥ 1`, `dim L(τ) = 1/(1+τ)`, where `L(τ) = L(ψ)` with
`ψ(q) = q^{-τ}`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 5 (Cao, Wu, and
Zhang). -/
public theorem_wanted dimH_lurothWellApproximableSet_rpow_of_one_le (τ : ℝ) (hτ : 1 ≤ τ) :
    dimH (lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) =
      ENNReal.ofReal (1 / (1 + τ))

/-- For `τ ≥ 0`, `dim L(τ) = 1/(1+τ)`, and for `τ > 0`, `H^{1/(1+τ)}(L(τ)) = ∞`.
The printed statement also claims the measure part at `τ = 0`; it fails there:
`L(0) ⊆ (0, 1]` (`lurothWellApproximableSet_subset_Ioc`), so `H^1(L(0)) ≤ 1`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 6. -/
public theorem_wanted dimH_hausdorffMeasure_lurothWellApproximableSet_rpow (τ : ℝ)
    (hτ : 0 ≤ τ) :
    dimH (lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) =
        ENNReal.ofReal (1 / (1 + τ)) ∧
      (0 < τ → μH[1 / (1 + τ)] (lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) = ∞)

/-- For `ψ : ℕ → (0, 1]`, `1/(1 + τ̄_ψ) ≤ dim L(ψ) ≤ 1/(1 + τ_ψ)` (in `ℝ≥0∞`, with
`1/∞ = 0`).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 7. -/
public theorem_wanted dimH_lurothWellApproximableSet_bounds (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) :
    (1 + upperOrderAtInfinity ψ)⁻¹ ≤ dimH (lurothWellApproximableSet ψ) ∧
      dimH (lurothWellApproximableSet ψ) ≤ (1 + lowerOrderAtInfinity ψ)⁻¹

/-- For `ψ : ℕ → (0, 1]`, with `S_k` the set of all `k`-th Lüroth denominators and
`λ_ψ = liminf_k liminf_{q ∈ S_k} -log ψ(q)/log q`,
`λ̄_ψ = liminf_k limsup_{q ∈ S_k} -log ψ(q)/log q`: `λ_ψ ≥ τ_ψ`, `λ̄_ψ ≤ τ̄_ψ`, and
`1/(1 + λ̄_ψ) ≤ dim L(ψ) ≤ 1/(1 + λ_ψ)`. Here `S_k` is indexed from `0` (the paper's
`S_{k+1}`), which does not change the outer `liminf`, and `q ∈ S_k`, `q → ∞` is the
filter `atTop ⊓ 𝓟 S_k`.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 8. -/
public theorem_wanted dimH_lurothWellApproximableSet_bounds_denominators (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) :
    let S : ℕ → Set ℕ := fun k =>
      {q | ∃ d : ℕ → ℕ, (∀ n, 2 ≤ d n) ∧ lurothDenominator d k = q}
    let f : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)
    let lowerLam : ℝ≥0∞ := liminf (fun k => liminf f (atTop ⊓ Filter.principal (S k))) atTop
    let upperLam : ℝ≥0∞ := liminf (fun k => limsup f (atTop ⊓ Filter.principal (S k))) atTop
    lowerOrderAtInfinity ψ ≤ lowerLam ∧ upperLam ≤ upperOrderAtInfinity ψ ∧
      (1 + upperLam)⁻¹ ≤ dimH (lurothWellApproximableSet ψ) ∧
      dimH (lurothWellApproximableSet ψ) ≤ (1 + lowerLam)⁻¹

/-- For every `τ ≥ 0` there is `ψ : ℕ → (0, 1]` that is not eventually non-increasing,
has lower order at infinity `τ`, and has `dim L(ψ) = 0` (`< 1/(1+τ)`), so the
Tan–Zhou conjecture fails without monotonicity.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 9. -/
public theorem_wanted exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero (τ : ℝ)
    (hτ : 0 ≤ τ) :
    ∃ ψ : ℕ → ℝ, (∀ q, 0 < ψ q ∧ ψ q ≤ 1) ∧ (¬ ∃ N, AntitoneOn ψ (Set.Ici N)) ∧
      lowerOrderAtInfinity ψ = ENNReal.ofReal τ ∧ dimH (lurothWellApproximableSet ψ) = 0

/-- For `ψ : ℕ → (0, 1]` with lower order at infinity `τ_ψ > 1`, put `t = 1/(1 + τ_ψ)` and
`θ_t(q) = min {1, 2^{-t} q^{1-t} ψ(q)^t}`. If `θ_t` is non-increasing and
`∑_{q ≥ 1} -(ψ(q)/q)^t ((1 - t) log q + t log(ψ(q)/2)) = ∞`, then
`dim L(ψ) = 1/(1 + τ_ψ)`.

`θ_t` is required to be non-increasing on `q ≥ 1` (the paper's `ℕ`; at `q = 0` the formula
gives `0`); the series is indexed from `q = 1` and "`= ∞`" is read as its partial sums tending
to `+∞` (the terms need not be nonnegative); `t` is `(1 + τ_ψ)⁻¹` converted to a real number
(`0` if `τ_ψ = ∞`).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 10
(`integers-2026-A45-thm-10`). -/
public theorem_wanted dimH_lurothWellApproximableSet_of_tendsto_sum (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) (hτ : 1 < lowerOrderAtInfinity ψ) (t : ℝ)
    (ht : t = ((1 + lowerOrderAtInfinity ψ)⁻¹).toReal)
    (hθ : AntitoneOn (fun q : ℕ => min 1 ((2 : ℝ) ^ (-t) * (q : ℝ) ^ (1 - t) * ψ q ^ t))
      (Set.Ici 1))
    (hdiv : Tendsto (fun N : ℕ => ∑ q ∈ Finset.Icc 1 N,
        -((ψ q / q) ^ t * ((1 - t) * Real.log q + t * Real.log (ψ q / 2)))) atTop atTop) :
    dimH (lurothWellApproximableSet ψ) = (1 + lowerOrderAtInfinity ψ)⁻¹

end

end MetaMathlibExt
