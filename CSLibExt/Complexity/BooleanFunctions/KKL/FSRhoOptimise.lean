/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform
public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC
public import CSLibExt.Complexity.BooleanFunctions.KKL.DegreeTruncation
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLpBiased

/-!
# The KKL inequality at p = 1/2, and the p-biased basis at p = 1/2

At `p = 1/2` the `p`-biased characters are the Walsh characters up to the sign `(-1)^{|S|}`, so
the `p`-biased Fourier weights agree with the uniform ones. The KKL inequality for the uniform
measure with constant `2`, proved in `KKL.RhoOptimiseClose2`, is recorded here as
`fsr_pbiased_endpoint`: the `p = 1/2` case of the `p`-biased KKL inequality, which this
library does not prove for other `p`.

## Main results

* `StatMech.Probability.fsr_ptn_pchar_half`: `φ_S = (-1)^{|S|} χ_S` at `p = 1/2`.
* `StatMech.Probability.fsr_ptn_coeff_half_sq`: the `p`-biased and Walsh Fourier weights agree at
  `p = 1/2`.
* `StatMech.Probability.fsr_pbiased_endpoint`: `KKLHypercontractive (1/2) 2`.

## References

* J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988.
* D. Falik, A. Samorodnitsky, *Edge-isoperimetric inequalities and influences*, Combin. Probab.
  Comput. 16 (2007).
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At `p = 1/2` the normalized bit is `-(-1)^b`. -/
theorem fsr_ptn_psi_half (b : Bool) :
    ptn_psi (1 / 2 : ℝ) b = - khc_sign b := by
  unfold ptn_psi khc_sign
  rw [show ptn_sigma (1 / 2 : ℝ) = 1 / 2 from by
    unfold ptn_sigma; rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 from by ring,
      Real.sqrt_sq (by norm_num)]]
  cases b <;> norm_num [ptn_val]

omit [Fintype ι] [DecidableEq ι] in
/-- At `p = 1/2` the `p`-biased character is `(-1)^{|S|}` times the Walsh character. -/
theorem fsr_ptn_pchar_half (S : Finset ι) (ω : ConfigSpace ι) :
    ptn_pchar (1 / 2 : ℝ) S ω = (-1) ^ S.card * khc_walshChar S ω := by
  unfold ptn_pchar khc_walshChar
  rw [show (fun i => ptn_psi (1 / 2 : ℝ) (ω i)) = (fun i => - khc_sign (ω i)) from by
    funext i; exact fsr_ptn_psi_half (ω i)]
  rw [Finset.prod_neg]

/-- At `p = 1/2` the squared `p`-biased and Walsh Fourier coefficients agree. -/
theorem fsr_ptn_coeff_half_sq (f : ConfigSpace ι → ℝ) (S : Finset ι) :
    (ptn_coeff (1 / 2 : ℝ) f S) ^ 2 = (khc_fourierCoeff f S) ^ 2 := by
  have heq : ptn_coeff (1 / 2 : ℝ) f S = (-1) ^ S.card * khc_fourierCoeff f S := by
    unfold ptn_coeff khc_fourierCoeff
    rw [khc_expect_half]
    rw [show (fun ω => f ω * ptn_pchar (1 / 2 : ℝ) S ω)
        = (fun ω => (-1) ^ S.card * (f ω * khc_walshChar S ω)) from by
      funext ω; rw [fsr_ptn_pchar_half]; ring]
    rw [vtp_uexp_smul]
  rw [heq, mul_pow]
  rcases Nat.even_or_odd S.card with he | ho
  · rw [he.neg_one_pow]; ring
  · rw [ho.neg_one_pow]; ring

/-- Total influence at `p = 1/2` in terms of the `p`-biased Fourier coefficients. -/
theorem fsr_totalInfl_half_eq (φ : ConfigSpace ι → Bool) :
    totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      = ∑ S : Finset ι, 4 * (S.card : ℝ)
          * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  rw [khc_totalInfl_eq_fourierWeight φ]
  apply Finset.sum_congr rfl
  intro S _
  rw [fsr_ptn_coeff_half_sq]

/-- **Kahn–Kalai–Linial inequality** for the uniform measure with constant `2` (J. Kahn, G. Kalai,
  N. Linial, *The influence of variables on Boolean functions*, FOCS 1988; proof after D. Falik,
  A. Samorodnitsky, 2007): for every finite nonempty `E` and every Boolean function `φ` on `{0,
  1}^E`, `2 · Var(φ) · log (1 / maxₑ Infₑ(φ)) ≤ ∑ₑ Infₑ(φ)`, where `Infₑ(φ)` is the probability
  that `e` is pivotal. This is the `p = 1/2` case of the `p`-biased KKL inequality. -/
theorem fsr_pbiased_endpoint :
    KKLHypercontractive (1 / 2 : ℝ) 2 :=
  bph_KKL cro2_rhoOptimise

end StatMech.Probability
