/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Lotka characteristic equation: one real root, its sign, and dominance

For a net maternity function `φ ≥ 0` (survival times fecundity) that vanishes outside a
bounded reproductive span, as in Jones's notes, where `φ = 0` outside `[α, β]`, the Lotka
characteristic function is `f(s) = ∫ e^{-sa} φ(a) da`. When `f(s)` is finite for every real `s`
and `φ` is not almost everywhere zero, `f` is continuous and strictly decreasing, tends to `∞`
at `-∞` and to `0` at `∞`, so the equation `f(r) = 1` has exactly one real root `r`, the
intrinsic rate of increase. Since `f(0) = R₀ = ∫ φ`, the sign of `r` is the sign of `R₀ - 1`.
Because `φ` is a density (its law is not supported on an arithmetic lattice), every other
complex root `z` of `∫ e^{-za} φ(a) da = 1` has `Re z < r`. The bounded span is the setting of
Jones's notes, which state the shape of `f` and the dominance of the real root.

`Domains.Biology.Epidemiology.EulerLotka` proves only that exponential solutions satisfy the
Euler–Lotka equation (`renewal_exp_iff`), and `Domains.Biology.Ecology.Leslie` treats the
discrete-age equation; neither proves uniqueness, the sign rule or dominance of the real root.

Sources: F. R. Sharpe and A. J. Lotka, "A problem in age-distribution", Philos. Mag. (6) 21
(1911) 435–438; R. A. Fisher, *The Genetical Theory of Natural Selection*, Clarendon Press
(1930), ch. II, pp. 26–27; J. H. Jones, "Population growth in continuous time", Stanford
Spring Workshop in Formal Demography, 5 May 2008, "Analyzing the characteristic equation" and
"Non-real roots", slides 12–14 and 17–20.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace WantedExt.Biology.Ecology.LotkaCharacteristicEquationWanted

open MeasureTheory Filter Topology Real

/-- The **Lotka characteristic function** `f(s) = ∫ e^{-sa} φ(a) da` of a net maternity
function `φ`. -/
noncomputable def charFun (φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ a, exp (-(s * a)) * φ a

/-- The characteristic function at a complex argument, `∫ e^{-za} φ(a) da`. -/
noncomputable def charFunComplex (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ a : ℝ, Complex.exp (-(z * a)) * φ a

/-- Standing hypotheses on a **net maternity function**: measurable, nonnegative, zero at
negative ages and beyond some last age of reproduction `β` (a bounded reproductive span, as in
Jones's notes), not almost everywhere zero, and with `a ↦ e^{-sa} φ(a)` integrable for every
real `s` (true, for example, when `φ` is bounded). -/
structure IsNetMaternity (φ : ℝ → ℝ) : Prop where
  measurable : Measurable φ
  nonneg : ∀ a, 0 ≤ φ a
  eq_zero_of_neg : ∀ a < 0, φ a = 0
  exists_eq_zero_of_gt : ∃ β : ℝ, ∀ a, β < a → φ a = 0
  not_ae_eq_zero : ¬ φ =ᵐ[volume] 0
  integrable_exp : ∀ s : ℝ, Integrable (fun a => exp (-(s * a)) * φ a)

/-- **Shape of the characteristic function** (Jones 2008). Assuming `IsNetMaternity φ`
(measurable, nonnegative, vanishing on negative ages and beyond some age `β`, not almost
everywhere zero, with `a ↦ e^{-sa} φ(a)` integrable for every `s : ℝ`), `charFun φ` is
continuous and strictly decreasing on `ℝ`, with `charFun φ s → ∞` as `s → -∞` and
`charFun φ s → 0` as `s → ∞`.

Source: Jones, "Population growth in continuous time" (2008), slides 12–14, eqs. (8)–(9). -/
public theorem_wanted charFun_shape {φ : ℝ → ℝ} (hφ : IsNetMaternity φ) :
    Continuous (charFun φ) ∧ StrictAnti (charFun φ) ∧
      Tendsto (charFun φ) atBot atTop ∧ Tendsto (charFun φ) atTop (𝓝 0)

/-- **Unique real root** (Sharpe–Lotka 1911; Fisher 1930, ch. II). Assuming `IsNetMaternity φ`
(so `φ` vanishes outside a bounded reproductive span), the characteristic equation
`∫ e^{-ra} φ(a) da = 1` has exactly one real solution `r`.

Source: Sharpe and Lotka (1911); Fisher (1930), ch. II; Jones, "Population growth in
continuous time" (2008), slides 12–14. -/
public theorem_wanted existsUnique_charFun_eq_one {φ : ℝ → ℝ} (hφ : IsNetMaternity φ) :
    ∃! r : ℝ, charFun φ r = 1

/-- **Sign of the intrinsic rate** (Fisher 1930, ch. II). Assuming `IsNetMaternity φ` (so `φ`
vanishes outside a bounded reproductive span), if `r` is the real root of `charFun φ r = 1`,
then `r > 0 ↔ R₀ > 1`, `r = 0 ↔ R₀ = 1` and `r < 0 ↔ R₀ < 1`, where `R₀ = ∫ φ = charFun φ 0`
is the net reproduction number.

Source: Fisher (1930), ch. II, pp. 26–27. -/
public theorem_wanted sign_of_charFun_eq_one {φ : ℝ → ℝ} (hφ : IsNetMaternity φ) {r : ℝ}
    (hr : charFun φ r = 1) :
    (0 < r ↔ 1 < ∫ a, φ a) ∧ (r = 0 ↔ ∫ a, φ a = 1) ∧ (r < 0 ↔ ∫ a, φ a < 1)

/-- **Dominance of the real root** (Lotka; Jones 2008). Assuming `IsNetMaternity φ` (so `φ`
vanishes outside a bounded reproductive span), if `r` is the real root of `charFun φ r = 1`,
then since `φ` is a density, every complex root `z ≠ r` of `∫ e^{-za} φ(a) da = 1` satisfies
`Re z < r`. (For a law on an arithmetic lattice of span `d` this fails: `r + 2πik/d` are roots.)

Source: Jones, "Population growth in continuous time" (2008), slides 12 and 17–20,
eqs. (10)–(12). -/
public theorem_wanted re_lt_of_charFunComplex_eq_one {φ : ℝ → ℝ} (hφ : IsNetMaternity φ)
    {r : ℝ} (hr : charFun φ r = 1) {z : ℂ} (hz : charFunComplex φ z = 1) (hzr : z ≠ r) :
    z.re < r

end WantedExt.Biology.Ecology.LotkaCharacteristicEquationWanted
