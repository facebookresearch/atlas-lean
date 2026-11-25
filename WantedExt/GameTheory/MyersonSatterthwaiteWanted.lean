/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-! # The Myerson–Satterthwaite theorem

A seller (trader 1) owns an object that a buyer (trader 2) may buy. Their values `v₁` and `v₂`
are independent, with continuous positive densities `f₁` on `[a₁, b₁]` and `f₂` on `[a₂, b₂]`.
A direct mechanism is a pair `(p, x)`: on the reports `(v₁, v₂)` the object is transferred with
probability `p v₁ v₂` and the buyer pays the seller `x v₁ v₂`. With quasi-linear utilities, the
interim expected gains from trade of the seller of value `v₁` reporting `w₁`, and of the buyer of
value `v₂` reporting `w₂`, are

* `∫_{a₂}^{b₂} (x w₁ v₂ - v₁ p w₁ v₂) f₂(v₂) dv₂`,
* `∫_{a₁}^{b₁} (v₂ p v₁ w₂ - x v₁ w₂) f₁(v₁) dv₁`.

The mechanism is Bayesian incentive compatible when truthful reports maximize these, individually
rational when the truthful values are nonnegative for every type, and ex post efficient when the
object is transferred exactly when the buyer values it more (Myerson and Satterthwaite 1983, §2
and §3).

**Theorem** (Myerson and Satterthwaite 1983, Corollary 1). If the interiors of the two intervals
intersect, no Bayesian incentive-compatible, individually rational trading mechanism is ex post
efficient. The proof computes, from the envelope formula of Myerson's lemma, that every
incentive-compatible ex post efficient mechanism gives
`U₁(b₁) + U₂(a₂) = -∫_{a₂}^{b₁} (1 - F₂) F₁ < 0` (their (7)).

The positive densities matter: for two-point distributions on `{1, 4}` and `{0, 3}` the
mechanism "trade at price 2 when both agree" is incentive compatible, individually rational and
ex post efficient (Myerson and Satterthwaite 1983, remark after Corollary 1).

The statement is recorded as wanted. Interim payments are written as integrals of `x` against the
other trader's density; the hypotheses `hx`, `hx₁`, `hx₂` say that they are defined (the
paper's integrals exist), and `hp` that `p` is a measurable probability.

## References

* R. B. Myerson and M. A. Satterthwaite, "Efficient mechanisms for bilateral trading",
  *J. Econom. Theory* 29 (1983), 265–281, §2, Theorem 1, §3 (equation (7)) and Corollary 1.
-/

@[expose] public section

namespace MathlibExt.GameTheory.MyersonSatterthwaiteWanted

open Set MeasureTheory

/-- **Myerson–Satterthwaite theorem.** Let the seller's value have a continuous positive
probability density `f₁` on `[a₁, b₁]` and the buyer's value a continuous positive probability
density `f₂` on `[a₂, b₂]`, with `a₂ < b₁` and `a₁ < b₂` (the interiors intersect). Then there is
no trading mechanism `(p, x)`, with `p` a measurable transfer probability and interim payments
defined, that is Bayesian incentive compatible (`hIC₁`, `hIC₂`), interim individually rational
(`hIR₁`, `hIR₂`) and ex post efficient (`heff`) (Myerson and Satterthwaite 1983,
Corollary 1). -/
theorem_wanted myerson_satterthwaite
    {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hov₁ : a₂ < b₁) (hov₂ : a₁ < b₂)
    {f₁ f₂ : ℝ → ℝ} (hf₁ : ContinuousOn f₁ (Icc a₁ b₁)) (hf₂ : ContinuousOn f₂ (Icc a₂ b₂))
    (hf₁pos : ∀ v ∈ Icc a₁ b₁, 0 < f₁ v) (hf₂pos : ∀ v ∈ Icc a₂ b₂, 0 < f₂ v)
    (hf₁one : ∫ v in a₁..b₁, f₁ v = 1) (hf₂one : ∫ v in a₂..b₂, f₂ v = 1)
    (p x : ℝ → ℝ → ℝ) (hpm : Measurable (Function.uncurry p))
    (hp : ∀ v₁ ∈ Icc a₁ b₁, ∀ v₂ ∈ Icc a₂ b₂, p v₁ v₂ ∈ Icc (0 : ℝ) 1)
    (hx : IntegrableOn (Function.uncurry x) (Icc a₁ b₁ ×ˢ Icc a₂ b₂))
    (hx₁ : ∀ v₁ ∈ Icc a₁ b₁, IntervalIntegrable (x v₁) volume a₂ b₂)
    (hx₂ : ∀ v₂ ∈ Icc a₂ b₂, IntervalIntegrable (fun v₁ => x v₁ v₂) volume a₁ b₁)
    (hIC₁ : ∀ v₁ ∈ Icc a₁ b₁, ∀ w₁ ∈ Icc a₁ b₁,
      ∫ v₂ in a₂..b₂, (x w₁ v₂ - v₁ * p w₁ v₂) * f₂ v₂ ≤
        ∫ v₂ in a₂..b₂, (x v₁ v₂ - v₁ * p v₁ v₂) * f₂ v₂)
    (hIC₂ : ∀ v₂ ∈ Icc a₂ b₂, ∀ w₂ ∈ Icc a₂ b₂,
      ∫ v₁ in a₁..b₁, (v₂ * p v₁ w₂ - x v₁ w₂) * f₁ v₁ ≤
        ∫ v₁ in a₁..b₁, (v₂ * p v₁ v₂ - x v₁ v₂) * f₁ v₁)
    (hIR₁ : ∀ v₁ ∈ Icc a₁ b₁, 0 ≤ ∫ v₂ in a₂..b₂, (x v₁ v₂ - v₁ * p v₁ v₂) * f₂ v₂)
    (hIR₂ : ∀ v₂ ∈ Icc a₂ b₂, 0 ≤ ∫ v₁ in a₁..b₁, (v₂ * p v₁ v₂ - x v₁ v₂) * f₁ v₁)
    (heff : ∀ v₁ ∈ Icc a₁ b₁, ∀ v₂ ∈ Icc a₂ b₂,
      (v₁ < v₂ → p v₁ v₂ = 1) ∧ (v₂ < v₁ → p v₁ v₂ = 0)) :
    False

end MathlibExt.GameTheory.MyersonSatterthwaiteWanted
