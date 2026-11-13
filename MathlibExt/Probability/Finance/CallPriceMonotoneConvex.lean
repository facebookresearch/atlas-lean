/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.OptionPayoffs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Call prices are decreasing and convex in strike

Under a common positive pricing functional (nonnegative state prices `ψ`), the call
price `C(K) = ∑ ω, ψ ω * europeanCallPayoff (S ω) K` is decreasing (antitone) and
convex in the strike `K`: each summand is a nonnegative multiple of the convex payoff
`K ↦ europeanCallPayoff (S ω) K`. The payoff is the landed
`OptionPayoffs.europeanCallPayoff`.

## Main results

* `callPrice`: the state-price-weighted call price at a strike.
* `antitone_callPrice`: the call price decreases in strike.
* `convexOn_callPrice`: the call price is convex in strike.

## References

* J. C. Hull, *Options, Futures, and Other Derivatives*, Chapter 10 (properties of
  stock options: call prices decrease and are convex in the strike price).
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.CallPriceMonotoneConvex

open Finset
open MathlibExt.Probability.Finance.OptionPayoffs

/-- Call price at strike `K` under the state prices `ψ` and terminal underlying values `S`:
`C(K) = ∑ ω, ψ ω * europeanCallPayoff (S ω) K` (source clause: "call price =
state-price-weighted call payoff"). `ψ ω` is the state price of state `ω`; `S ω` is the
terminal underlying value in state `ω`. The payoff is the landed
`OptionPayoffs.europeanCallPayoff`, not a re-encoding of `max (S - K) 0`. -/
noncomputable def callPrice {Ω : Type*} [Fintype Ω] (ψ S : Ω → ℝ) (K : ℝ) : ℝ :=
  ∑ ω, ψ ω * europeanCallPayoff (S ω) K

private theorem convexOn_payoff (S : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ => europeanCallPayoff S K) := by
  have h1 : ConvexOn ℝ Set.univ (fun K : ℝ => S - K) := by
    have ha : ConvexOn ℝ Set.univ (fun _ : ℝ => S) := convexOn_const S convex_univ
    have hb : ConcaveOn ℝ Set.univ (id : ℝ → ℝ) := concaveOn_id convex_univ
    exact ha.sub hb
  have h0 : ConvexOn ℝ Set.univ (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 convex_univ
  have hsup := h1.sup h0
  have heq : (fun K : ℝ => europeanCallPayoff S K)
      = ((fun K : ℝ => S - K) ⊔ fun _ : ℝ => (0 : ℝ)) := by
    funext K
    simp only [europeanCallPayoff, Pi.sup_apply]
  exact heq ▸ hsup

private theorem convexOn_summand {Ω : Type*} {ψ S : Ω → ℝ}
    (hψ : ∀ ω, 0 ≤ ψ ω) (ω : Ω) :
    ConvexOn ℝ Set.univ (fun K : ℝ => ψ ω * europeanCallPayoff (S ω) K) := by
  have hpay := convexOn_payoff (S ω)
  have hsmul := hpay.smul (hψ ω)
  have heq : (fun K : ℝ => ψ ω * europeanCallPayoff (S ω) K)
      = (fun K : ℝ => ψ ω • europeanCallPayoff (S ω) K) := by
    funext K
    exact (smul_eq_mul _ _).symm
  exact heq ▸ hsmul

private theorem convexOn_sum_aux {Ω : Type*} {f : Ω → ℝ → ℝ}
    (hf : ∀ ω, ConvexOn ℝ Set.univ (f ω)) (s : Finset Ω) :
    ConvexOn ℝ Set.univ (fun K : ℝ => s.sum (fun ω => f ω K)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have heq : (fun K : ℝ => (∅ : Finset Ω).sum (fun ω => f ω K))
        = (fun _ : ℝ => (0 : ℝ)) := by
      funext K
      simp
    rw [heq]
    exact convexOn_const 0 convex_univ
  | insert a t hat ih =>
    have heq : (fun K : ℝ => (insert a t).sum (fun ω => f ω K))
        = (f a + fun K : ℝ => t.sum (fun ω => f ω K)) := by
      funext K
      simp [Finset.sum_insert hat, Pi.add_apply]
    rw [heq]
    exact (hf a).add ih

/-- **Call prices decrease in strike.** With nonnegative state prices, a higher strike gives
a weakly lower call price (Atlas roadmap FI11.T04, monotonicity half). -/
theorem antitone_callPrice {Ω : Type*} [Fintype Ω] {ψ S : Ω → ℝ}
    (hψ : ∀ ω, 0 ≤ ψ ω) :
    Antitone (callPrice ψ S) := by
  intro a b hab
  simp only [callPrice, europeanCallPayoff]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (hψ ω)
  apply max_le_max
  · exact sub_le_sub_left hab _
  · exact le_rfl

/-- **Call prices are convex in strike.** With nonnegative state prices, the call price is a
convex function of the strike on the whole real line (Atlas roadmap FI11.T04, convexity
half). Reuse: each summand is a nonnegative multiple of `K ↦ europeanCallPayoff (S ω) K`,
the max of an affine function and `0` (`ConvexOn.sup`, after unfolding
`europeanCallPayoff`); the sum of convex functions is convex. Do not
reprove `ConvexOn.sup`, `ConvexOn.smul`, or `ConvexOn.add`. -/
theorem convexOn_callPrice {Ω : Type*} [Fintype Ω] {ψ S : Ω → ℝ}
    (hψ : ∀ ω, 0 ≤ ψ ω) :
    ConvexOn ℝ Set.univ (callPrice ψ S) := by
  classical
  have hf : ∀ ω, ConvexOn ℝ Set.univ (fun K : ℝ => ψ ω * europeanCallPayoff (S ω) K) :=
    fun ω => convexOn_summand hψ ω
  have h := convexOn_sum_aux (f := fun ω K => ψ ω * europeanCallPayoff (S ω) K) hf Finset.univ
  have heq : callPrice ψ S
      = (fun K : ℝ => Finset.univ.sum (fun ω => ψ ω * europeanCallPayoff (S ω) K)) := by
    rfl
  rw [heq]
  exact h

end MathlibExt.Probability.Finance.CallPriceMonotoneConvex
