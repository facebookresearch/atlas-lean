/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import MathlibExt.Probability.RandomWalkFDD

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace RandomWalkFDDTest

/-- The piecewise linear interpolation `f n s = S_{⌊ns⌋} / √n + (ns - ⌊ns⌋) R_{⌊ns⌋} / √n` of the
random walk `S_k = ∑_{i < k} R i`, as in the statement of
`tendstoInDistribution_randomWalk_increments`. -/
noncomputable def walk {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊(n : ℝ) * s⌋₊, R i ω) / √n +
    ((n : ℝ) * s - ⌊(n : ℝ) * s⌋₊) * R ⌊(n : ℝ) * s⌋₊ ω / √n

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ}

-- Times `0 < 1 < 3`: the increments `f n 1 - f n 0` and `f n 3 - f n 1` converge jointly to
-- independent `𝓝(0, 1)` and `𝓝(0, 2)` variables.
example (hR_meas : ∀ i, Measurable (R i)) (hR_mean : ∀ i, ∫ ω, R i ω ∂P = 0)
    (hR_var : ∀ i, ∫ ω, R i ω ^ 2 ∂P = 1) (hR_bdd : ∀ i ω, |R i ω| ≤ 1)
    (hindep : iIndepFun R P) (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    {Z : Fin 2 → Ω' → ℝ} (hZ0 : HasLaw (Z 0) (gaussianReal 0 1) P')
    (hZ1 : HasLaw (Z 1) (gaussianReal 0 2) P') (hZindep : iIndepFun Z P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => ![walk R n 1 ω - walk R n 0 ω, walk R n 3 ω - walk R n 1 ω])
      atTop (fun ω => ![Z 0 ω, Z 1 ω]) (fun _ => P) P' := by
  have ht : StrictMono ![(0 : ℝ), 1, 3] := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  have h := tendstoInDistribution_randomWalk_increments hR_meas hR_mean hR_var hR_bdd hindep
    hident _ ht (by norm_num) (Fin.forall_fin_two.2
      ⟨by convert hZ0 using 3; norm_num, by convert hZ1 using 3; norm_num⟩) hZindep
  convert h using 1
  · funext n ω j
    fin_cases j <;> rfl
  · funext ω j
    fin_cases j <;> rfl

-- Times `1/4 < 3/4 < 7/4`, which are not grid points: the interpolation terms are exercised,
-- and the limits are independent `𝓝(0, 1/2)` and `𝓝(0, 1)` variables.
example (hR_meas : ∀ i, Measurable (R i)) (hR_mean : ∀ i, ∫ ω, R i ω ∂P = 0)
    (hR_var : ∀ i, ∫ ω, R i ω ^ 2 ∂P = 1) (hR_bdd : ∀ i ω, |R i ω| ≤ 1)
    (hindep : iIndepFun R P) (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    {Z : Fin 2 → Ω' → ℝ} (hZ0 : HasLaw (Z 0) (gaussianReal 0 (1 / 2)) P')
    (hZ1 : HasLaw (Z 1) (gaussianReal 0 1) P') (hZindep : iIndepFun Z P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) =>
        ![walk R n (3 / 4) ω - walk R n (1 / 4) ω, walk R n (7 / 4) ω - walk R n (3 / 4) ω])
      atTop (fun ω => ![Z 0 ω, Z 1 ω]) (fun _ => P) P' := by
  have ht : StrictMono ![(1 / 4 : ℝ), 3 / 4, 7 / 4] := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  have h := tendstoInDistribution_randomWalk_increments hR_meas hR_mean hR_var hR_bdd hindep
    hident _ ht (by norm_num) (Fin.forall_fin_two.2
      ⟨by convert hZ0 using 3; rw [← NNReal.coe_inj]; norm_num,
        by convert hZ1 using 3; norm_num⟩) hZindep
  convert h using 1
  · funext n ω j
    fin_cases j <;> rfl
  · funext ω j
    fin_cases j <;> rfl

end RandomWalkFDDTest

#print axioms tendstoInDistribution_randomWalk_increments
