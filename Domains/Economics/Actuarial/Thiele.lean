/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Thiele's differential equation for a deterministic two-state policy

Coffie, Duedahl and Proske, *Thiele's Differential Equation Based on Markov Jump Processes
with Non-countable State Space* (2021, arXiv:2102.10047), Theorem 2.2.1, give an equation for
the conditional reserve of a regular jump insurance model. Example 2.2.2 gives its countable
discrete-state form. For a single transition from alive to dead, take interest `δ`, exit
intensity `μ`, premium income `π` (payment stream `−π dt`), transition benefit `b`, and zero
reserve after death. The alive-state equation then has the right-hand side `(δ + μ)V + π − μb`.

Here the reserve is defined by a deterministic integral with a prescribed maturity payment.
The proof derives the equation from that integral; it does not identify the integral with a
conditional expectation or assume a law for the time of death.
-/

@[expose] public section

namespace Domains.Economics.Actuarial

open MeasureTheory Set
open scoped Topology

/-- For real-valued paths `δ, μ, π, b`, maturity `T` and terminal benefit `g`, the two-state
reserve at time `t` is `V(t) = ∫ₜᵀ F(t,s)(μ(s)b(s) − π(s)) ds + F(t,T)g`, where
`F(t,s) = exp(−∫ₜˢ (δ(u) + μ(u)) du)`. Benefits are costs and premium income is subtracted.
The integrals are oriented real interval integrals. For a policy they are used on `0 ≤ t ≤ T`
with continuous paths on `[0,T]` and nonnegative interest `δ` and exit intensity `μ`. -/
noncomputable def twoStateReserve (δ μ π b : ℝ → ℝ) (T g t : ℝ) : ℝ :=
  let F := fun s => Real.exp (-(∫ u in t..s, δ u + μ u))
  (∫ s in t..T, F s * (μ s * b s - π s)) + F T * g

/-- Let `T > 0`, let `g` be any real terminal benefit and let the real paths `δ, μ, π, b`
be continuous on `[0,T]`. Put `F(t,s) = exp(−∫ₜˢ (δ(u) + μ(u)) du)` and
`V(t) = ∫ₜᵀ F(t,s)(μ(s)b(s) − π(s)) ds + F(t,T)g`, counting benefits as costs and
premiums as income. Then `V(T) = g` and at every `0 < t < T` the ordinary derivative is
`V′(t) = (δ(t) + μ(t))V(t) + π(t) − μ(t)b(t)`. The identity needs no sign restriction on
`δ` or `μ`, so includes the nonnegative rates of the insurance application. -/
theorem thiele_differentialEquation {δ μ π b : ℝ → ℝ} {T : ℝ} (g : ℝ) (hT : 0 < T)
    (hδ : ContinuousOn δ (Icc 0 T)) (hμ : ContinuousOn μ (Icc 0 T))
    (hπ : ContinuousOn π (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T)) :
    twoStateReserve δ μ π b T g T = g ∧ ∀ t ∈ Ioo 0 T,
      HasDerivAt (twoStateReserve δ μ π b T g)
        ((δ t + μ t) * twoStateReserve δ μ π b T g t + π t - μ t * b t) t := by
  refine ⟨by simp [twoStateReserve], ?_⟩
  let r := fun u => δ u + μ u
  let A := fun x => ∫ u in 0..x, r u
  let q := fun s => Real.exp (-A s) * (μ s * b s - π s)
  have hr : ContinuousOn r (Icc 0 T) := hδ.add hμ
  have hi (x : ℝ) (hx : x ∈ Icc 0 T) : IntervalIntegrable r volume 0 x :=
    (hr.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  have hA : ContinuousOn A (Icc 0 T) := by
    rw [← uIcc_of_le hT.le] at hr ⊢
    exact intervalIntegral.continuousOn_primitive_interval hr.integrableOn_Icc
  have hq : ContinuousOn q (Icc 0 T) :=
    (Real.continuous_exp.comp_continuousOn hA.neg).mul ((hμ.mul hb).sub hπ)
  -- Additivity splits the two-time weight into a factor at each endpoint.
  have hF (x s : ℝ) (hx : x ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
      Real.exp (-(∫ u in x..s, r u)) = Real.exp (A x) * Real.exp (-A s) := by
    rw [← intervalIntegral.integral_symm, ← intervalIntegral.integral_interval_sub_left
      (hi x hx) (hi s hs), sub_eq_add_neg, Real.exp_add]
  have hV : EqOn (twoStateReserve δ μ π b T g)
      (fun x => Real.exp (A x) * ((∫ s in x..T, q s) + Real.exp (-A T) * g)) (Icc 0 T) := by
    intro x hx
    dsimp only [twoStateReserve]
    rw [hF x T hx ⟨hT.le, le_rfl⟩, mul_add, ← mul_assoc, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hx.2] at hs
    dsimp only [q]
    rw [hF x s hx ⟨hx.1.trans hs.1, hs.2⟩, mul_assoc]
  intro t ht
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hN : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have dA : HasDerivAt A (r t) t := intervalIntegral.integral_hasDerivAt_right (hi t ht')
    ⟨_, hN, hr.aestronglyMeasurable measurableSet_Icc⟩ (hr.continuousAt hN)
  have dIntegral := intervalIntegral.integral_hasDerivAt_left
    ((hq.mono (Icc_subset_Icc_left ht'.1)).intervalIntegrable_of_Icc ht'.2)
    ⟨_, hN, hq.aestronglyMeasurable measurableSet_Icc⟩ (hq.continuousAt hN)
  have dV := dA.exp.mul (dIntegral.add_const (Real.exp (-A T) * g))
  refine (dV.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hN] with x hx using hV hx
  rw [hV ht']
  dsimp only [q, r]
  have hcancel : Real.exp (A t) * Real.exp (-A t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination -(μ t * b t - π t) * hcancel

end Domains.Economics.Actuarial
