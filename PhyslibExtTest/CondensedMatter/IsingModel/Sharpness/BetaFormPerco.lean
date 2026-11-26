/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaFormPerco

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaFormPerco`

* `bfp_integrate_perco_beta_named` on the constant function `f = 1`, which satisfies the
  differential inequality on `(p̃_c, 1)` and `f(p̃_c) ≥ 0` (the hypotheses are satisfiable);
* the general form applied under its hypotheses.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.BetaFormPerco

open _root_.StatMech _root_.StatMech.Sharpness

-- The constant function `1` satisfies the hypotheses, giving `(β - β̃_c)/β ≤ 1`.
example (d : ℕ) (J β : ℝ) (hJ : 0 < J) (hd : 0 < d)
    (hc : (Percolation.tildePc d : ℝ) < 1) (hβ : betaTildeC d J < β) :
    (β - betaTildeC d J) / β ≤ (fun _ : ℝ => (1 : ℝ)) (pBeta J β) :=
  bfp_integrate_perco_beta_named (fun _ => 1) hJ hd hc hβ (fun _ _ => differentiableAt_const _)
    (fun _ _ => by simp) zero_le_one

-- The general integrated bound.
example (d : ℕ) (J β : ℝ) (f : ℝ → ℝ) (hJ : 0 < J) (hd : 0 < d)
    (hc : (Percolation.tildePc d : ℝ) < 1) (hβ : betaTildeC d J < β)
    (hdiff : ∀ q ∈ Set.Ico (Percolation.tildePc d : ℝ) 1, DifferentiableAt ℝ f q)
    (hineq : ∀ q ∈ Set.Ioo (Percolation.tildePc d : ℝ) 1, 1 / (q * (1 - q)) * (1 - f q) ≤ deriv f q)
    (h0 : 0 ≤ f (Percolation.tildePc d)) :
    (β - betaTildeC d J) / β ≤ f (pBeta J β) :=
  bfp_integrate_perco_beta_named f hJ hd hc hβ hdiff hineq h0

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.BetaFormPerco
