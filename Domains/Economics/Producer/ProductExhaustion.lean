/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Product exhaustion under constant returns

Let a production function `f` be differentiable at the input bundle `x` with derivative `L`,
and have constant returns along the ray through `x`: `f (t • x) = t * f x` for `t > 0` (no
homogeneity for negative `t` is assumed). Euler's identity `L x = f x` follows from Mathlib's
local Euler theorem `HasFDerivAt.apply_self_eq_smul_of_eventuallyEq`. Hence the marginal
products `L (Pi.single i 1)` weighted by input quantities sum to output, and competitive factor
payments `wᵢ = P · ∂f/∂xᵢ` exhaust the value of output `P * f x`.

Atlas' `MetaMathlibExt.IsHomogeneousDegreeOne.fderiv_apply_self`
(`MathlibExt/Analysis/Calculus/HomogeneousEuler.lean`) is the same identity for functions on
`Fin n → ℝ` that are homogeneous at every point, stated with `fderiv`. The results here need
homogeneity only along the ray through `x`, take an arbitrary derivative `L` over any finite index
type, and add the factor-payment form; both files call the same Mathlib kernel.

## Main results

* `MathlibExt.Economics.Producer.fderiv_apply_self_eq_of_constantReturns`
* `MathlibExt.Economics.Producer.sum_marginalProduct_mul_eq`
* `MathlibExt.Economics.Producer.dotProduct_eq_mul_of_competitive_payments`

## References

* P. H. Wicksteed, *An Essay on the Co-ordination of the Laws of Distribution* (1894).
* H. R. Varian, *Microeconomic Analysis*, 3rd ed., Norton (1992), Chapter 1.

Atlas roadmap target EC07.T03.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Economics.Producer

/-- **Euler's identity under constant returns**: the derivative applied to the input bundle
equals output. -/
theorem fderiv_apply_self_eq_of_constantReturns {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} {x : ι → ℝ} (hf : HasFDerivAt f L x)
    (hcrs : ∀ t : ℝ, 0 < t → f (t • x) = t * f x) :
    L x = f x := by
  have hmain : L x = (1:ℝ) • f x := by
    refine hf.apply_self_eq_smul_of_eventuallyEq (hasDerivAt_id (1:ℝ)) ?_
    filter_upwards [eventually_gt_nhds (zero_lt_one : (0:ℝ) < 1)] with t ht
    show f (t • x) = t • f x
    rw [hcrs t ht, smul_eq_mul]
  simpa using hmain

/-- Marginal products weighted by input quantities sum to output:
`∑ᵢ (∂f/∂xᵢ)(x) · xᵢ = f(x)`. -/
theorem sum_marginalProduct_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} {x : ι → ℝ} (hf : HasFDerivAt f L x)
    (hcrs : ∀ t : ℝ, 0 < t → f (t • x) = t * f x) :
    ∑ i, L (Pi.single i 1) * x i = f x := by
  have h1 : L x = f x := fderiv_apply_self_eq_of_constantReturns hf hcrs
  have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [← h1]
  conv_rhs => rw [hx, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- **Product exhaustion.** If each input is paid the value of its marginal product at output
price `P` (competitive factor payments `wᵢ = P · ∂f/∂xᵢ`), total factor payments equal the
value of output. -/
theorem dotProduct_eq_mul_of_competitive_payments {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} {x w : ι → ℝ} {P : ℝ} (hf : HasFDerivAt f L x)
    (hcrs : ∀ t : ℝ, 0 < t → f (t • x) = t * f x)
    (hw : ∀ i, w i = P * L (Pi.single i 1)) :
    w ⬝ᵥ x = P * f x := by
  have h2 : ∑ i, L (Pi.single i 1) * x i = f x :=
    sum_marginalProduct_mul_eq hf hcrs
  show ∑ i, w i * x i = P * f x
  rw [← h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hw i]
  ring

end MathlibExt.Economics.Producer
