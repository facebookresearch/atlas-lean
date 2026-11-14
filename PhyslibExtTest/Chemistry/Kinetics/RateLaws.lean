/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.Kinetics.RateLaws

/-!
# Rate laws tests

Signature probes, API checks, and axiom audits for rate laws.
-/

namespace Chemistry.Kinetics

/-! ## External signature probes

Each `#check` pins an external lemma the prod file depends on. If any fails,
adjust the corresponding prod call site to the reported signature.
-/

#check @exists_hasDerivAt_eq_slope
#check @HasDerivAt.exp
#check @HasDerivAt.inv
#check @HasDerivAt.div
#check @HasDerivAt.const_mul
#check @HasDerivAt.const_add
#check @HasDerivAt.congr_of_eventuallyEq
#check @hasDerivAt_const
#check @hasDerivAt_id'
#check @HasDerivAt.deriv
#check @HasDerivAt.differentiableAt
#check @DifferentiableAt.hasDerivAt
#check @HasDerivAt.continuousAt
#check @ContinuousAt.continuousWithinAt
#check @Real.exp_add
#check @Real.exp_neg
#check @Real.exp_pos
#check @Real.exp_ne_zero
#check @Real.exp_zero
#check @Real.exp_log
#check @Real.log_exp
#check @Real.log_one
#check @Real.log_div
#check @Real.exp_le_one_iff
#check @Real.add_one_le_exp
#check @div_eq_div_iff
#check @div_eq_iff
#check @eq_div_iff
#check @div_le_iff₀
#check @div_lt_one
#check @div_eq_zero_iff
#check @div_le_div_iff₀
#check @div_ne_zero
#check @zpow_neg_one
#check @zpow_one
#check @zpow_zero
#check @mul_left_cancel₀
#check @mul_inv_cancel₀
#check @Set.mem_Icc
#check @Set.mem_Ioo
#check @Filter.EventuallyEq.of_eq
#check @eq_or_lt_of_le
#check @lt_or_gt_of_ne
#check @max_eq_left
#check @max_eq_right
#check @one_div_pos
#check @add_pos_of_pos_of_nonneg
#check @pow_ne_zero
#check @HasDerivAt.add
#check @HasDerivAt.sub
#check @HasDerivAt.mul

/-! ## Prod API resolution -/

#check @extentRate
#check @concOfExtent
#check @hasDerivAt_concOfExtent
#check @deriv_concOfExtent
#check @rateLaw_zero_ode
#check @rateLaw_first_ode
#check @rateLaw_secondAA_ode
#check @rateLaw_secondAB_ode
#check @eq_of_hasDerivAt_zero
#check @zeroOrderSol
#check @hasDerivAt_zeroOrderSol
#check @zeroOrderSol_unique
#check @zeroOrderSol_zero
#check @depletionTime
#check @zeroOrderConc
#check @zeroOrderConc_before
#check @zeroOrderConc_after
#check @zeroOrderSol_halfLife
#check @zeroOrderSol_halfLife_unique
#check @firstOrderSol
#check @firstOrderSol_zero
#check @firstOrderSol_pos
#check @hasDerivAt_firstOrderSol
#check @firstOrderSol_unique
#check @firstOrderSol_halfLife
#check @firstOrderSol_halfLife_unique
#check @secondOrderGen_unique
#check @secondOrderAASol
#check @secondOrderAASol_zero
#check @secondOrderAASol_denom_pos
#check @secondOrderAASol_pos
#check @hasDerivAt_secondOrderAASol
#check @secondOrderAASol_unique
#check @secondOrderAASol_halfLife
#check @secondOrderAASol_halfLife_unique
#check @secondOrderABSolA
#check @secondOrderABSolB
#check @secondOrderABSolA_zero
#check @secondOrderABSolB_zero
#check @secondOrderAB_denom_ne
#check @hasDerivAt_secondOrderABSolA
#check @hasDerivAt_secondOrderABSolB
#check @secondOrderABSol_conserved
#check @ab_conservation
#check @secondOrderABSol_unique
#check @secondOrderABEqualSol
#check @secondOrderABEqualSol_zero
#check @secondOrderABEqualSol_denom_pos
#check @secondOrderABEqualSol_pos
#check @hasDerivAt_secondOrderABEqualSol
#check @secondOrderABEqualSol_unique
#check @secondOrderABEqualSol_halfLife
#check @halfLife
#check @halfLife_correct_zero
#check @halfLife_correct_first
#check @halfLife_correct_second
#check @halfLife_indep_iff_first_order
#check @rateGroup
#check @rateGroup_zero
#check @rateGroup_one
#check @rateGroup_two
#check @k_of_rateGroup
#check @firstOrderSol_rateGroup
#check @secondOrderAASol_rateGroup
#check @zeroOrderSol_rateGroup
#check @pfoRateConst
#check @pfoSol
#check @pfoSol_zero
#check @hasDerivAt_pfoSol
#check @pfoRatio
#check @pfo_error_bound
#check @pfo_rel_error_bound

/-! ## Concrete checks -/

example (A0 k : ℝ) : zeroOrderSol A0 k 0 = A0 := zeroOrderSol_zero A0 k
example (A0 k : ℝ) : firstOrderSol A0 k 0 = A0 := firstOrderSol_zero A0 k
example (A0 B0 k : ℝ) : pfoSol A0 B0 k 0 = A0 := pfoSol_zero A0 B0 k
example (A0 k : ℝ) : secondOrderAASol A0 k 0 = A0 := secondOrderAASol_zero A0 k
example (A0 k : ℝ) : secondOrderABEqualSol A0 k 0 = A0 :=
  secondOrderABEqualSol_zero A0 k
example (A0 B0 k : ℝ) (hΔ : B0 - A0 ≠ 0) :
    secondOrderABSolA A0 B0 k 0 = A0 := secondOrderABSolA_zero A0 B0 k hΔ
example (A0 B0 k : ℝ) (hΔ : B0 - A0 ≠ 0) :
    secondOrderABSolB A0 B0 k 0 = B0 := secondOrderABSolB_zero A0 B0 k hΔ

example : halfLife 1 5 7 = Real.log 2 / 5 := rfl
example (k A0 : ℝ) : halfLife 0 k A0 = A0 / (2 * k) := rfl
example (k A0 : ℝ) : halfLife 2 k A0 = 1 / (2 * k * A0) := rfl

example (k t A0 : ℝ) : rateGroup 0 k t A0 = k * t / A0 := rateGroup_zero k t A0
example (k t A0 : ℝ) : rateGroup 1 k t A0 = k * t := rateGroup_one k t A0
example (k t A0 : ℝ) : rateGroup 2 k t A0 = k * t * A0 := rateGroup_two k t A0

/-- Evaluated rate group: `6 * 4 / 3 = 8`, with the division reduced. -/
example : rateGroup 0 6 4 3 = 8 := by
  rw [rateGroup_zero]
  norm_num

example : pfoRatio 1 2 = 1 / 2 := rfl
example : depletionTime 4 2 = 4 / 2 := rfl

example (A0 k t : ℝ) (ht : 0 ≤ t) :
    zeroOrderSol A0 k t = zeroOrderSol A0 k t :=
  zeroOrderSol_unique A0 k (zeroOrderSol A0 k)
    (fun s _ => hasDerivAt_zeroOrderSol A0 k s)
    (zeroOrderSol_zero A0 k) t ht

example (A0 k t : ℝ) (ht : 0 ≤ t) :
    firstOrderSol A0 k t = firstOrderSol A0 k t :=
  firstOrderSol_unique A0 k (firstOrderSol A0 k)
    (fun s _ => hasDerivAt_firstOrderSol A0 k s)
    (firstOrderSol_zero A0 k) t ht

example (A0 k t : ℝ) (hk : 0 < k) (hA0 : 0 < A0) (ht : 0 ≤ t) :
    secondOrderAASol A0 k t = secondOrderAASol A0 k t :=
  secondOrderAASol_unique A0 k (secondOrderAASol A0 k) hk hA0
    (fun s hs => hasDerivAt_secondOrderAASol A0 k s
      (ne_of_gt (secondOrderAASol_denom_pos A0 k s hk hA0 hs)))
    (fun s hs => secondOrderAASol_pos A0 k s hk hA0 hs)
    (secondOrderAASol_zero A0 k) t ht

example (A0 k t : ℝ) (hk : 0 < k) (hA0 : 0 < A0) (ht : 0 ≤ t) :
    secondOrderABEqualSol A0 k t = secondOrderABEqualSol A0 k t :=
  secondOrderABEqualSol_unique A0 k (secondOrderABEqualSol A0 k)
    (secondOrderABEqualSol A0 k) hA0 hk
    (fun s hs => by
      have h := hasDerivAt_secondOrderABEqualSol A0 k s
        (ne_of_gt (secondOrderABEqualSol_denom_pos A0 k s hk hA0 hs))
      have hderiv : deriv (secondOrderABEqualSol A0 k) s
          = -k * secondOrderABEqualSol A0 k s * secondOrderABEqualSol A0 k s := by
        rw [h.deriv]
        ring
      have hfinal := h.differentiableAt.hasDerivAt
      rw [hderiv] at hfinal
      exact hfinal)
    (fun s hs => by
      have h := hasDerivAt_secondOrderABEqualSol A0 k s
        (ne_of_gt (secondOrderABEqualSol_denom_pos A0 k s hk hA0 hs))
      have hderiv : deriv (secondOrderABEqualSol A0 k) s
          = -k * secondOrderABEqualSol A0 k s * secondOrderABEqualSol A0 k s := by
        rw [h.deriv]
        ring
      have hfinal := h.differentiableAt.hasDerivAt
      rw [hderiv] at hfinal
      exact hfinal)
    (fun s hs => secondOrderABEqualSol_pos A0 k s hk hA0 hs)
    (secondOrderABEqualSol_zero A0 k) (secondOrderABEqualSol_zero A0 k) t ht

example (A0 B0 k t : ℝ) (hA0 : 0 < A0) (hB0 : 0 < B0) (hk : 0 < k)
    (hΔ : B0 - A0 ≠ 0)
    (hposA : ∀ s : ℝ, 0 ≤ s → 0 < secondOrderABSolA A0 B0 k s)
    (hposB : ∀ s : ℝ, 0 ≤ s → 0 < secondOrderABSolB A0 B0 k s)
    (ht : 0 ≤ t) :
    secondOrderABSolA A0 B0 k t = secondOrderABSolA A0 B0 k t :=
  secondOrderABSol_unique A0 B0 k (secondOrderABSolA A0 B0 k)
    (secondOrderABSolB A0 B0 k) hA0 hB0 hk hΔ
    (fun s hs => by
      have hM := secondOrderAB_denom_ne A0 B0 k s hA0 hB0 hk hΔ hs
      have hA := hasDerivAt_secondOrderABSolA A0 B0 k s hM
      simpa [secondOrderABSolB] using hA)
    (fun s hs => hasDerivAt_secondOrderABSolB A0 B0 k s
      (secondOrderAB_denom_ne A0 B0 k s hA0 hB0 hk hΔ hs))
    hposA hposB
    (secondOrderABSolA_zero A0 B0 k hΔ) (secondOrderABSolB_zero A0 B0 k hΔ) t ht

/-! ## Axiom audits -/

#print axioms eq_of_hasDerivAt_zero
#print axioms zeroOrderSol_unique
#print axioms firstOrderSol_unique
#print axioms secondOrderGen_unique
#print axioms secondOrderAASol_unique
#print axioms secondOrderABSol_unique
#print axioms secondOrderABEqualSol_unique
#print axioms halfLife_indep_iff_first_order
#print axioms pfo_error_bound
#print axioms pfo_rel_error_bound

end Chemistry.Kinetics
