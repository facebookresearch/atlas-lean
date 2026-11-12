/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Point price elasticity of demand

The point elasticity of a demand curve `q` at price `p` is `ε(p) = p q'(p) / q(p)`. On positive
prices and quantities it is the log-log derivative `d log q / d log p`: the derivative of
`s ↦ log q(exp s)` at `s = log p`.

## Main definitions

* `pointElasticity q p`: the point elasticity `p * deriv q p / q p`. It is meaningful only when
  `q` is differentiable at `p` and `q p ≠ 0`; elsewhere Lean's total `deriv` and division return
  junk values (for example `pointElasticity (fun _ => 0) p = 0`). The log-derivative theorem
  below carries both conditions (with `p > 0`, `q p > 0`) as hypotheses.

## Main results

* `pointElasticity_eq_of_hasDerivAt`: with `HasDerivAt q q' p`, the elasticity is `p q' / q p`.
* `hasDerivAt_log_comp_exp_pointElasticity`: for `p > 0`, `q p > 0` and `q` differentiable at
  `p`, `s ↦ log (q (exp s))` has derivative `pointElasticity q p` at `log p`.

The proof is the chain rule (`HasDerivAt.comp`, `HasDerivAt.log`, `Real.hasDerivAt_exp`).

Atlas roadmap target EC03.T03.

## References

* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton (2014), ch. 15.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), §2.E.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

/-- The point price elasticity of a demand curve `q` at price `p`:
`ε(p) = p q'(p) / q(p)`. It is the economic elasticity only when `q` is differentiable at `p`
and `q p ≠ 0`; otherwise `deriv` and division by zero return Mathlib's junk values. -/
noncomputable def pointElasticity (q : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * deriv q p / q p

/-- With a derivative `q'` at `p`, the point elasticity is `p q' / q(p)`. -/
theorem pointElasticity_eq_of_hasDerivAt {q : ℝ → ℝ} {q' p : ℝ} (hd : HasDerivAt q q' p) :
    pointElasticity q p = p * q' / q p := by
  unfold pointElasticity
  rw [hd.deriv]

/-- **Elasticity is the log-log derivative.** At a positive price `p` where demand is
positive and differentiable, `d log q / d log p` exists and equals the point elasticity:
the map `s ↦ log (q (exp s))` has derivative `pointElasticity q p` at `s = log p`. -/
theorem hasDerivAt_log_comp_exp_pointElasticity {q : ℝ → ℝ} {q' p : ℝ} (hp : 0 < p)
    (hq : 0 < q p) (hd : HasDerivAt q q' p) :
    HasDerivAt (fun s => Real.log (q (Real.exp s))) (pointElasticity q p) (Real.log p) := by
  have hexp : HasDerivAt Real.exp (Real.exp (Real.log p)) (Real.log p) :=
    Real.hasDerivAt_exp (Real.log p)
  have hbase : Real.exp (Real.log p) = p := Real.exp_log hp
  have hd' : HasDerivAt q q' (Real.exp (Real.log p)) := by
    rw [hbase]
    exact hd
  have hcomp : HasDerivAt (q ∘ Real.exp) (q' * Real.exp (Real.log p)) (Real.log p) :=
    hd'.comp (Real.log p) hexp
  have hlog := hcomp.log (by simpa [Function.comp_apply, hbase] using ne_of_gt hq)
  simp only [Function.comp_apply, hbase] at hlog
  have hel : pointElasticity q p = q' * p / q p := by
    rw [pointElasticity_eq_of_hasDerivAt hd]
    ring
  rw [hel]
  exact hlog

end MathlibExt.Economics.Consumer
