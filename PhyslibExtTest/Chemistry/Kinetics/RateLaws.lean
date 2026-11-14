/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.Kinetics.RateLaws
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

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

#check @ReactorVolume
#check @extentRate
#check @volume_mul_extentRate
#check @concOfExtent
#check @concOfExtent_zero
#check @hasDerivAt_concOfExtent
#check @deriv_concOfExtent
#check @rateLaw_zero_ode
#check @rateLaw_first_ode
#check @rateLaw_secondAA_ode
#check @rateLaw_secondAB_ode
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
#check @firstOrderSol_eq_amount
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
#check @secondOrderABSolA_pos
#check @secondOrderABSolB_pos
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
#check @RateModel
#check @RateModel.order
#check @RateModel.sol
#check @halfLife
#check @halfLife_correct
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
#check @pfo_error_div_initial_bound

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

example (A0 k t : ℝ) :
    firstOrderSol A0 k t = MathlibExt.Biology.Biophysics.CompartmentKinetics.amount k 0 A0 t :=
  congrFun (firstOrderSol_eq_amount A0 k) t

example : halfLife .firstOrder 5 7 = Real.log 2 / 5 := rfl
example (k A0 : ℝ) : halfLife .zeroOrder k A0 = A0 / (2 * k) := rfl
example (k A0 : ℝ) : halfLife .secondOrderAA k A0 = 1 / (2 * k * A0) := rfl
example (k A0 : ℝ) : halfLife .secondOrderABEqual k A0 = 1 / (k * A0) := rfl

/-- Both second-order models have order `2`, but their half-lives differ: the order alone does not
determine the half-life. -/
example (k A0 : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    RateModel.secondOrderAA.order = RateModel.secondOrderABEqual.order ∧
      halfLife .secondOrderAA k A0 ≠ halfLife .secondOrderABEqual k A0 := by
  refine ⟨rfl, ?_⟩
  simp only [halfLife]
  rw [Ne, div_eq_div_iff (by positivity) (by positivity)]
  intro h
  have hkA0 := mul_pos hk hA0
  linarith

/-- The equal-amounts `A + B → P` half-life halves its concentration. -/
example (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    secondOrderABEqualSol A0 k (halfLife .secondOrderABEqual k A0) = A0 / 2 :=
  halfLife_correct .secondOrderABEqual A0 k hk hA0

/-- The equal-amounts `A + B → P` half-life depends on `[A]₀`. -/
example (k : ℝ) (hk : 0 < k) :
    ¬ ∀ A0 A0' : ℝ, 0 < A0 → 0 < A0' →
      halfLife .secondOrderABEqual k A0 = halfLife .secondOrderABEqual k A0' :=
  fun h => absurd ((halfLife_indep_iff_first_order _ k hk).mp h) (by decide)

example (k t A0 : ℝ) : rateGroup 0 k t A0 = k * t / A0 := rateGroup_zero k t A0
example (k t A0 : ℝ) : rateGroup 1 k t A0 = k * t := rateGroup_one k t A0
example (k t A0 : ℝ) : rateGroup 2 k t A0 = k * t * A0 := rateGroup_two k t A0

/-- Evaluated rate group: `6 * 4 / 3 = 8`, with the division reduced. -/
example : rateGroup 0 6 4 3 = 8 := by
  rw [rateGroup_zero]
  norm_num

example : pfoRatio 1 2 = 1 / 2 := rfl
example : depletionTime 4 2 = 4 / 2 := rfl

/-- Regression: an extent trajectory that does not start at `0` (`ξ ≡ 1`, `V = ν = 1`) still gives
initial concentration `c₀`. -/
example (c₀ : ℝ) : concOfExtent c₀ 1 ⟨1, one_pos⟩ (fun _ => 1) 0 = c₀ :=
  concOfExtent_zero c₀ 1 ⟨1, one_pos⟩ _

example (c₀ t : ℝ) : concOfExtent c₀ 1 ⟨1, one_pos⟩ (fun s => 1 + s) t = c₀ + t := by
  simp [concOfExtent]

/-- Regression: a reactor volume is positive, so the zero volume of the old interface (where
Lean's division gave a zero rate) cannot be passed. -/
example (V : ReactorVolume) : (V : ℝ) ≠ 0 := V.2.ne'

/-- `ξ(t) = 3t` in a reactor of volume `2` has extent rate `v = 3/2`, and `V v = dξ/dt = 3`. -/
example (t : ℝ) : extentRate ⟨2, two_pos⟩ (fun s => 3 * s) t = 3 / 2 := by
  have h : deriv (fun s : ℝ => 3 * s) t = 3 := by simp
  simp only [extentRate, h]
  norm_num

example (t : ℝ) : ((⟨2, two_pos⟩ : ReactorVolume) : ℝ) * extentRate ⟨2, two_pos⟩ (fun s => 3 * s) t
    = deriv (fun s : ℝ => 3 * s) t :=
  volume_mul_extentRate _ _ t

/-- Extent-based first-order kinetics feeds the integrated law: with `A s = c(s)` for
`c = concOfExtent A0 (-1) V ξ` and `v = k[A]` on `t ≥ 0`, `A` is the first-order solution. -/
example (A ξ : ℝ → ℝ) (A0 k : ℝ) (V : ReactorVolume) (t : ℝ)
    (hA : ∀ s, A s = concOfExtent A0 (-1) V ξ s)
    (hξ : ∀ s, DifferentiableAt ℝ ξ s) (hrate : ∀ s, 0 ≤ s → extentRate V ξ s = k * A s)
    (ht : 0 ≤ t) : A t = firstOrderSol A0 k t :=
  firstOrderSol_unique A0 k A (fun s hs => rateLaw_first_ode A ξ A0 k V s hA (hξ s) (hrate s hs))
    (by rw [hA, concOfExtent_zero]) t ht

/-! Non-vacuity: the explicit solutions satisfy every hypothesis of the uniqueness theorems. -/

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

/-- The explicit unequal-amount solution satisfies every hypothesis of `secondOrderABSol_unique`;
its positivity is proved (`secondOrderABSolA_pos`, `secondOrderABSolB_pos`), not assumed. -/
example (A0 B0 k t : ℝ) (hA0 : 0 < A0) (hB0 : 0 < B0) (hk : 0 < k)
    (hΔ : B0 - A0 ≠ 0) (ht : 0 ≤ t) :
    secondOrderABSolA A0 B0 k t = secondOrderABSolA A0 B0 k t :=
  secondOrderABSol_unique A0 B0 k (secondOrderABSolA A0 B0 k)
    (secondOrderABSolB A0 B0 k) hA0 hB0 hk hΔ
    (fun s hs => by
      have hM := secondOrderAB_denom_ne A0 B0 k s hA0 hB0 hk hΔ hs
      have hA := hasDerivAt_secondOrderABSolA A0 B0 k s hM
      simpa [secondOrderABSolB] using hA)
    (fun s hs => hasDerivAt_secondOrderABSolB A0 B0 k s
      (secondOrderAB_denom_ne A0 B0 k s hA0 hB0 hk hΔ hs))
    (fun s hs => secondOrderABSolA_pos A0 B0 k s hA0 hk hΔ hs)
    (fun s hs => secondOrderABSolB_pos A0 B0 k s hA0 hB0 hk hΔ hs)
    (secondOrderABSolA_zero A0 B0 k hΔ) (secondOrderABSolB_zero A0 B0 k hΔ) t ht

/-- Both denominator-sign branches: `[B]₀ > [A]₀` (`[A]₀ = 1`, `[B]₀ = 2`) and `[B]₀ < [A]₀`
(`[A]₀ = 2`, `[B]₀ = 1`), with `k = 1`. -/
example (t : ℝ) (ht : 0 ≤ t) :
    0 < secondOrderABSolA 1 2 1 t ∧ 0 < secondOrderABSolB 1 2 1 t :=
  ⟨secondOrderABSolA_pos 1 2 1 t one_pos one_pos (by norm_num) ht,
    secondOrderABSolB_pos 1 2 1 t one_pos two_pos one_pos (by norm_num) ht⟩

example (t : ℝ) (ht : 0 ≤ t) :
    0 < secondOrderABSolA 2 1 1 t ∧ 0 < secondOrderABSolB 2 1 1 t :=
  ⟨secondOrderABSolA_pos 2 1 1 t two_pos one_pos (by norm_num) ht,
    secondOrderABSolB_pos 2 1 1 t two_pos one_pos one_pos (by norm_num) ht⟩

/-- At `t = 1` in the `[B]₀ < [A]₀` branch: `[A](1) = 2e / (2e - 1)` and `[B](1) = 1 / (2e - 1)`,
both positive, and `[B](1) - [A](1) = -1 = [B]₀ - [A]₀`. -/
example : secondOrderABSolA 2 1 1 1 = 2 * Real.exp 1 / (2 * Real.exp 1 - 1) ∧
    secondOrderABSolB 2 1 1 1 = 1 / (2 * Real.exp 1 - 1) := by
  have hE : (1:ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  have hD : 2 * Real.exp 1 - 1 ≠ 0 := by linarith
  have hD' : 1 - 2 * Real.exp 1 ≠ 0 := by linarith
  constructor
  · simp only [secondOrderABSolA]
    norm_num
    field_simp
    ring
  · simp only [secondOrderABSolB, secondOrderABSolA]
    norm_num
    field_simp
    ring

/-! ## Axiom audits -/

#print axioms zeroOrderSol_unique
#print axioms firstOrderSol_unique
#print axioms secondOrderGen_unique
#print axioms secondOrderAASol_unique
#print axioms secondOrderABSol_unique
#print axioms secondOrderABSolA_pos
#print axioms secondOrderABSolB_pos
#print axioms volume_mul_extentRate
#print axioms secondOrderABEqualSol_unique
#print axioms halfLife_indep_iff_first_order
#print axioms pfo_error_bound
#print axioms pfo_error_div_initial_bound
#print axioms halfLife_correct

end Chemistry.Kinetics
