/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessBeta
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercolationMeanfield
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaReparam

/-!
# The mean-field inequality in the `β`-parametrization at `β̃_c`

Integration of the percolation mean-field inequality, written in the variable `β` with
`p(β) = 1 - e^{-βJ}`, from `β̃_c`.

## i. Overview

The change of variables `p = p(β)` and the integrated bound `f(p(β)) ≥ (β - β_c)/β` for a general
starting point `β_c` are `shr_integrate_beta` and its companions in `BetaReparam`. This file
specializes the starting point to `β̃_c` (`betaTildeC`), where `p(β̃_c) = p̃_c`. The result is
proved; the differential inequality for `f` (`hineq`) and `f(p̃_c) ≥ 0` are hypotheses.

## ii. Key results

- `bfp_integrate_perco_beta_named` : `f(p(β)) ≥ (β - β̃_c)/β` for `β > β̃_c`, given the
  differential inequality on `(p̃_c, 1)`

## iii. Table of contents

- A. Integration from `β̃_c`

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}

/-! ## A. Integration from `β̃_c` -/

/-- If `f` satisfies `(1/(q(1-q))) (1 - f(q)) ≤ f'(q)` on `(p̃_c, 1)` and `f(p̃_c) ≥ 0`, then
`f(p(β)) ≥ (β - β̃_c)/β` for `β > β̃_c`. -/
theorem bfp_integrate_perco_beta_named {J β : ℝ} (f : ℝ → ℝ) (hJ : 0 < J) (hd : 0 < d)
    (htc1 : (tildePc d : ℝ) < 1) (hβ : betaTildeC d J < β)
    (hdiff : ∀ q ∈ Ico (tildePc d : ℝ) 1, DifferentiableAt ℝ f q)
    (hineq : ∀ q ∈ Ioo (tildePc d : ℝ) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
    (hf0 : 0 ≤ f (tildePc d : ℝ)) :
    (β - betaTildeC d J) / β ≤ f (pBeta J β) := by
  set βc := betaTildeC d J with hβc_def
  have hβc_pos : 0 < βc := betaTildeC_pos hJ hd htc1
  have hval : pBeta J βc = (tildePc d : ℝ) := by
    rw [hβc_def]; exact pBeta_betaTildeC hJ htc1
  refine StatMech.Sharpness.shr_integrate_beta J β βc f hJ hβc_pos hβ ?_ ?_ ?_
  · rw [hval]; exact hdiff
  · rw [hval]; exact hineq
  · rw [hval]; exact hf0

end Sharpness

end StatMech
