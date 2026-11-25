/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fisher's reproductive value: total reproductive value grows exactly like `e^{rt}`

In a continuously age-structured population with survival `l` (`l(0) = 1`, `l' = -μ l` for the
mortality rate `μ`), fecundity `b ≥ 0` vanishing after the last reproductive age `ω`, and
intrinsic rate `r` (the root of `∫ e^{-rx} l(x) b(x) dx = 1`), Fisher defined the reproductive
value `v(x) = (e^{rx} / l(x)) ∫_x^∞ e^{-ry} l(y) b(y) dy`. Then `v(0) = 1` and
`v'(x) = (μ(x) + r) v(x) - b(x) v(0)`. If the density `n(x, t)` of individuals of age `x` at
time `t` solves the McKendrick–von Foerster equation `∂_t n + ∂_x n = -μ n` with births
`n(0, t) = ∫ b(x) n(x, t) dx`, the total reproductive value `V(t) = ∫ n(x, t) v(x) dx` satisfies
`V(t) = V(0) e^{rt}` for every such solution `n` (satisfying continuity and the birth boundary
condition `n(0, 0) = ∫ b(x) n(x, 0) dx`).

The equation is used in characteristic form (`s ↦ n(x + s, t + s)` has derivative
`-μ(x) n(x, t)` at `s = 0`), which needs only continuity of `n`. Since `v` vanishes after `ω`,
all integrals run over the reproductive ages `[0, ω]`. Reproductive value appears in
`Domains.Biology.Demography.Leslie` only as the left eigenvector of a Leslie matrix.

Sources: R. A. Fisher, *The Genetical Theory of Natural Selection*, Clarendon Press (1930),
ch. II, "Reproductive value", pp. 27–30.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace WantedExt.Biology.Ecology.FisherReproductiveValueWanted

open MeasureTheory Set Real

/-- Fisher's **reproductive value** at age `x`:
`v(x) = (e^{rx} / l(x)) ∫_x^∞ e^{-ry} l(y) b(y) dy`. -/
noncomputable def reproductiveValue (l b : ℝ → ℝ) (r x : ℝ) : ℝ :=
  exp (r * x) / l x * ∫ y in Ioi x, exp (-(r * y)) * l y * b y

/-- Standing hypotheses on a **continuous life table** with last reproductive age `ω > 0`:
`pos_omega` requires `0 < ω`, survival `l` is positive on `[0, ∞)` with `l(0) = 1` and `l' = -μ l`
there (`μ` continuous), fecundity `b` is continuous and nonnegative on `[0, ∞)` and vanishes after
`ω`, and `r` is the root of the characteristic equation `∫_0^∞ e^{-rx} l(x) b(x) dx = 1`. -/
structure IsLifeTable (l μ b : ℝ → ℝ) (ω r : ℝ) : Prop where
  pos_omega : 0 < ω
  l_zero : l 0 = 1
  l_pos : ∀ x, 0 ≤ x → 0 < l x
  continuousOn_mu : ContinuousOn μ (Ici 0)
  hasDerivWithinAt_l : ∀ x, 0 ≤ x → HasDerivWithinAt l (-(μ x * l x)) (Ici 0) x
  continuousOn_b : ContinuousOn b (Ici 0)
  b_nonneg : ∀ x, 0 ≤ x → 0 ≤ b x
  b_eq_zero : ∀ x, ω < x → b x = 0
  char_eq : ∫ x in Ioi 0, exp (-(r * x)) * l x * b x = 1

/-- **Normalization and balance equation of reproductive value** (Fisher 1930, ch. II). Under
the continuous life-table assumptions `IsLifeTable l μ b ω r` (`ω > 0`, `l(0) = 1`, `l > 0` on
`[0, ∞)` with `l' = -μ l`, continuous `μ`, continuous `b ≥ 0` vanishing after `ω`, and
`∫_0^∞ e^{-rx} l(x) b(x) dx = 1`), we have `v(0) = 1`, and for every `x > 0`,
`v'(x) = (μ(x) + r) v(x) - b(x) v(0)`.

Source: Fisher (1930), ch. II, pp. 27, 30. -/
public theorem_wanted reproductiveValue_zero_and_hasDerivAt {l μ b : ℝ → ℝ} {ω r : ℝ}
    (h : IsLifeTable l μ b ω r) :
    reproductiveValue l b r 0 = 1 ∧
      ∀ x, 0 < x → HasDerivAt (reproductiveValue l b r)
        ((μ x + r) * reproductiveValue l b r x - b x * reproductiveValue l b r 0) x

/-- **Fisher's theorem on total reproductive value** (Fisher 1930, ch. II). Under the continuous
life-table assumptions `IsLifeTable l μ b ω r`, let `n(x, t)` be continuous on `[0, ∞) × [0, ∞)`,
solve `∂_t n + ∂_x n = -μ n` in characteristic form, and satisfy the birth condition
`n(0, t) = ∫_0^ω b(x) n(x, t) dx`. Then for every `t ≥ 0`,
`∫_0^ω n(x, t) v(x) dx = e^{rt} ∫_0^ω n(x, 0) v(x) dx` for every such solution `n` (note that
continuity and the birth condition at `t = 0` require `n(0, 0) = ∫_0^ω b(x) n(x, 0) dx`).

Source: Fisher (1930), ch. II, "Reproductive value", pp. 27–30. -/
public theorem_wanted totalReproductiveValue_eq {l μ b : ℝ → ℝ} {ω r : ℝ}
    (h : IsLifeTable l μ b ω r) (n : ℝ → ℝ → ℝ)
    (hn : ContinuousOn (fun p : ℝ × ℝ => n p.1 p.2) (Ici 0 ×ˢ Ici 0))
    (hchar : ∀ x t, 0 ≤ x → 0 ≤ t →
      HasDerivWithinAt (fun s => n (x + s) (t + s)) (-(μ x * n x t)) (Ici 0) 0)
    (hbirth : ∀ t, 0 ≤ t → n 0 t = ∫ x in Icc 0 ω, b x * n x t) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Icc 0 ω, n x t * reproductiveValue l b r x =
      exp (r * t) * ∫ x in Icc 0 ω, n x 0 * reproductiveValue l b r x

end WantedExt.Biology.Ecology.FisherReproductiveValueWanted
