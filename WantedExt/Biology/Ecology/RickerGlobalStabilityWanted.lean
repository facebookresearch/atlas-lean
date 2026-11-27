/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Global stability of the Ricker map for `0 < r ≤ 2`

The Ricker stock–recruitment map (Ricker 1954), in units where the carrying capacity is `1`, is
`f(x) = x e^{r(1 - x)}` on `(0, ∞)` with growth parameter `r > 0`; its positive fixed point is
`x* = 1`. For `0 < r ≤ 2` the fixed point is globally asymptotically stable: every orbit
starting at `x₀ > 0` converges to `1`, and `1` is Lyapunov stable. Cull's proof encloses `f` by
the involution `h(x) = 2 - x`: `f(x) < h(x)` on `(0, 1)` and `h(x) < f(x)` on `(1, 2)`, and an
enveloping function with `h(h(x)) = x` forces global stability. The endpoint `r = 2`, where
`f'(1) = -1`, is covered by the enveloping argument and not by linearization.

Recorded here: global attractivity and Lyapunov stability of `x* = 1` for `0 < r ≤ 2`, and the
two enveloping inequalities for `h(x) = 2 - x`. Cull (1981) was not read; the statement follows
the later restatement of Cull's enveloping theorem by Luís and Rodrigues (2016, Theorem 1.4 and
§4.1 with period `1`). Their Theorem 1.4 assumes the enveloping inequalities and gives
convergence; their §4.1 states that `h(x) = 2 - x` envelops the Ricker map for `0 < r ≤ 2`, so
the inequalities are cited to §4.1. Lyapunov stability is derived.

Sources: W. E. Ricker, "Stock and recruitment", J. Fish. Res. Board Can. 11 (1954) 559–623,
doi:10.1139/f54-039; P. Cull, "Global stability of population models", Bull. Math. Biol. 43
(1981) 47–58, doi:10.1007/BF02460938; R. Luís and E. Rodrigues, "Global stability in some
one-dimensional non-autonomous discrete periodic population models", arXiv:1603.02723 (2016),
Theorem 1.4 and §4.1, published as "A survey on the enveloping method of some one-dimensional
non-autonomous discrete periodic population models", J. Math. Sci. Adv. Appl. 39 (2016) 63–87,
doi:10.18642/jmsaa_7100121662, with the same Theorem 1.4 and §4.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace WantedExt.Biology.Ecology.RickerGlobalStabilityWanted

open Filter Topology

/-- The **Ricker map** `f(x) = x e^{r(1 - x)}` with growth parameter `r` and carrying
capacity `1`. -/
noncomputable def ricker (r x : ℝ) : ℝ := x * Real.exp (r * (1 - x))

/-- **Global asymptotic stability of the Ricker map** (Cull 1981; Luís and Rodrigues 2016,
§4.1): let `r` be a real number with `0 < r` and `r ≤ 2`. Then
(1) for every initial value `x₀ > 0`, the iterates `fⁿ(x₀)` of the Ricker map
`f(x) = x e^{r(1 - x)}` converge to `1` as `n → ∞`; and
(2) the fixed point `1` is Lyapunov stable on `(0, ∞)`: for every `ε > 0` there is `δ > 0` such
that every `x₀ > 0` with `|x₀ - 1| < δ` satisfies `|fⁿ(x₀) - 1| < ε` for every `n`.

Sources: Cull (1981); Luís and Rodrigues (2016), Theorem 1.4 and §4.1. -/
public theorem_wanted ricker_globally_asymptotically_stable (r : ℝ) (hr₀ : 0 < r)
    (hr₂ : r ≤ 2) :
    (∀ x₀ : ℝ, 0 < x₀ → Tendsto (fun n : ℕ => (ricker r)^[n] x₀) atTop (𝓝 1)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ : ℝ, 0 < x₀ → |x₀ - 1| < δ →
        ∀ n : ℕ, |(ricker r)^[n] x₀ - 1| < ε

/-- **Cull's enveloping inequalities for `h(x) = 2 - x`**: let `r` be a real number with
`0 < r` and `r ≤ 2`. Then the Ricker map `f(x) = x e^{r(1 - x)}` satisfies `f(x) < 2 - x` for
every `x` with `0 < x < 1`, and `2 - x < f(x)` for every `x` with `1 < x < 2`.

Sources: Cull (1981); Luís and Rodrigues (2016), §4.1. -/
public theorem_wanted ricker_enveloped (r : ℝ) (hr₀ : 0 < r) (hr₂ : r ≤ 2) :
    (∀ x : ℝ, 0 < x → x < 1 → ricker r x < 2 - x) ∧
      ∀ x : ℝ, 1 < x → x < 2 → 2 - x < ricker r x

end WantedExt.Biology.Ecology.RickerGlobalStabilityWanted
