/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the definition and statement are adapted from
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level2/ma_proofbench_l2_91.lean` (MA-ProofBench, L. Pu et al.,
*A Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*,
arXiv:2606.13782; also distributed in the Hugging Face dataset openbmb/MA-ProofBench),
under the MIT license above. The ATLAS import placed the declarations in the namespace
below, added the definition's docstring, moved the problem description onto the
renamed `theorem_wanted`, and used a public module import. This file preserves the
adapted definition, statement and docstrings, supplies a proof, and narrows the imports.
-/

module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import MathlibExt.Analysis.Complex.FiniteZerosInDiscOfHolomorphic

/-!
# A zero count for the entire series with coefficients `n⁻ⁿ`

The exponential series dominates the absolute values of the defining terms and
proves the series is entire. Jensen's inequality on the circle of radius twice
that of the given disc bounds the total multiplicity of the zeros inside it.
-/

open Complex Set Metric
open scoped BigOperators ENNReal

noncomputable section

namespace MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowNWanted

/-- **The entire function $1+\sum_{n\ge 1}(z/n)^n$.** This is the function
$F:\mathbb{C}\to\mathbb{C}$ given by
$$F(z)=1+\sum_{n=1}^{\infty}\left(\frac{z}{n}\right)^{n}.$$
-/
@[expose] public noncomputable def F : ℂ → ℂ :=
  fun z => 1 + ∑' n : ℕ, (z / (n + 1 : ℂ)) ^ (n + 1)

/-- The scalar series coefficient, including the constant term `0 ^ 0 = 1`. -/
private def coeff (n : ℕ) : ℂ := ((n : ℂ) ^ n)⁻¹

private theorem coeff_norm (n : ℕ) : ‖coeff n‖ = ((n : ℝ) ^ n)⁻¹ := by
  rw [coeff, norm_inv, norm_pow, Complex.norm_natCast]

private theorem coeff_bound {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ‖coeff n‖ * r ^ n ≤ r ^ n / (n.factorial : ℝ) := by
  have hle : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  rw [coeff_norm, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (pow_nonneg hr _) hfact hle

private theorem summable_coeff_norm {r : ℝ} (hr : 0 ≤ r) :
    Summable fun n => ‖coeff n‖ * r ^ n :=
  (Real.summable_pow_div_factorial r).of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n)) (coeff_bound hr)

private theorem summable_term_norm (z : ℂ) : Summable fun n => ‖coeff n * z ^ n‖ := by
  simpa only [norm_mul, norm_pow] using summable_coeff_norm (norm_nonneg z)

private theorem F_eq_tsum (z : ℂ) : F z = ∑' n : ℕ, coeff n * z ^ n := by
  have hs : Summable fun n => coeff n * z ^ n := (summable_term_norm z).of_norm
  rw [hs.tsum_eq_zero_add]
  simp only [F, coeff, Nat.cast_zero, pow_zero, inv_one, mul_one]
  congr 1
  apply tsum_congr
  intro n
  rw [Nat.cast_add, Nat.cast_one, div_pow, div_eq_mul_inv, mul_comm]

private theorem F_zero : F 0 = 1 := by simp [F]

private theorem F_analytic : AnalyticOnNhd ℂ F univ := by
  let p := FormalMultilinearSeries.ofScalars ℂ coeff
  have hp : p.radius = ∞ := by
    apply p.radius_eq_top_of_summable_norm
    intro r
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using summable_coeff_norm r.coe_nonneg
  have h := p.analyticOnNhd
  have he : p.sum = F := by
    funext z
    change FormalMultilinearSeries.ofScalarsSum coeff z = F z
    rw [FormalMultilinearSeries.ofScalars_sum_eq, F_eq_tsum]
    simp only [smul_eq_mul]
  rw [hp, he] at h
  intro z _
  exact h z (show edist z (0 : ℂ) < ∞ from edist_lt_top _ _)

private theorem F_norm_le_exp (z : ℂ) : ‖F z‖ ≤ Real.exp ‖z‖ := by
  rw [F_eq_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc
    _ ≤ ∑' n : ℕ, ‖coeff n * z ^ n‖ := norm_tsum_le_tsum_norm (summable_term_norm z)
    _ ≤ ∑' n : ℕ, ‖z‖ ^ n / (n.factorial : ℝ) := by
      apply Summable.tsum_le_tsum _ (summable_term_norm z) (Real.summable_pow_div_factorial _)
      intro n
      rw [norm_mul, norm_pow]
      exact coeff_bound (norm_nonneg z) n

open FiniteZerosInDiscOfHolomorphicWanted (finite_zeros_in_ball_of_not_identically_zero)

open MeromorphicOn in
/-- **Zeros of $1+\sum_{n\ge 1}(z/n)^n$ in a disc.** Let $F$ be the entire function
$$F(z)=1+\sum_{n=1}^{\infty}\left(\frac{z}{n}\right)^{n}.$$
For every real $R>0$, $F$ has only finitely many zeros in the open disc
$\{z\in\mathbb{C} : |z|<R\}$, and the number of these zeros counted with multiplicity is at
most $4R$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level2/ma_proofbench_l2_91.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_finset_zeros_sum_analyticOrderNatAt_le
  (R : ℝ)
  (hR : 0 < R) :
  ∃ s : Finset ℂ,
    (∀ z : ℂ, z ∈ s ↔ ‖z‖ < R ∧ F z = 0) ∧
    ((∑ z ∈ s, analyticOrderNatAt F z) : ℝ) ≤ 4 * R := by
  classical
  have hF0 : F 0 ≠ 0 := by
    rw [F_zero]
    exact one_ne_zero
  have hfinite :=
    finite_zeros_in_ball_of_not_identically_zero F 0 R hR
      ⟨univ, isOpen_univ, subset_univ _, F_analytic.differentiableOn⟩
      (fun h => hF0 (h 0 (mem_ball_self hR)))
  let s := hfinite.toFinset
  have hs (z : ℂ) : z ∈ s ↔ ‖z‖ < R ∧ F z = 0 := by
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_ofPred_eq, mem_ball_zero_iff]
  refine ⟨s, hs, ?_⟩
  -- The closed-disc divisor also counts any boundary zeros, all with nonnegative order.
  let D := divisor F (closedBall (0 : ℂ) R)
  have hFin := D.finiteSupport (isCompact_closedBall (0 : ℂ) R)
  have hAnalytic : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R) := F_analytic.mono (subset_univ _)
  have hD (z : ℂ) : 0 ≤ D z := hAnalytic.divisor_nonneg z
  have hDval (z : ℂ) (hz : z ∈ s) : (analyticOrderNatAt F z : ℤ) = D z := by
    have hzR : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr ((hs z).mp hz).1.le
    change (analyticOrderNatAt F z : ℤ) = divisor F (closedBall (0 : ℂ) R) z
    rw [hAnalytic.divisor_apply hzR]
    change ((analyticOrderAt F z).toNat : ℤ) = _
    generalize analyticOrderAt F z = e
    cases e using ENat.recTopCoe <;> rfl
  have hsub : s ⊆ hFin.toFinset ∪ s := Finset.subset_union_right
  have hmem : Function.support (fun z => D z) ⊆ ↑(hFin.toFinset ∪ s) := by
    intro z hz
    exact Finset.mem_union.mpr (Or.inl (hFin.mem_toFinset.mpr hz))
  have hInt : ((∑ z ∈ s, analyticOrderNatAt F z) : ℤ) ≤ ∑ᶠ z : ℂ, D z := by
    rw [finsum_eq_sum_of_support_subset _ hmem]
    calc
      _ = ∑ z ∈ s, D z := Finset.sum_congr rfl hDval
      _ ≤ ∑ z ∈ hFin.toFinset ∪ s, D z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hD z
  have hBig : 0 < 2 * R := by positivity
  have hRabs : |R| = R := abs_of_pos hR
  have hBigabs : |2 * R| = 2 * R := abs_of_pos hBig
  have hlt : |R| < |2 * R| := by rw [hRabs, hBigabs]; linarith
  have hOuter : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) |2 * R|) := F_analytic.mono (subset_univ _)
  have hNorm (z : ℂ) (hz : z ∈ sphere (0 : ℂ) |2 * R|) : ‖F z‖ ≤ Real.exp (2 * R) := by
    rw [mem_sphere, dist_zero_right, hBigabs] at hz
    exact (F_norm_le_exp z).trans_eq (congrArg Real.exp hz)
  -- Jensen on the circle of radius `2 * R` bounds the closed-disc count.
  have h := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := R) (R := 2 * R)
    (M := Real.exp (2 * R)) (by simpa only [hRabs] using hR) hlt (Real.one_le_exp hBig.le)
    hOuter hF0 hNorm
  have hratio : 2 * R / R = 2 := by field_simp [hR.ne']
  rw [hRabs, F_zero, norm_one, div_one, Real.log_exp, hratio] at h
  have hLog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at hh
    linarith
  calc
    _ ≤ ((∑ᶠ z : ℂ, D z : ℤ) : ℝ) := by exact_mod_cast hInt
    _ ≤ (2 * R) / Real.log 2 := h
    _ ≤ 4 * R := by
      apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
      nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hLog)]

end MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowNWanted
