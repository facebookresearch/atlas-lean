/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Nonpositive extended-real subharmonicity

For `u : ℂ → EReal`, `negativeCircleAverage u z r` is the normalized
nonnegative extended Lebesgue average of `(-u(circleMap z r θ)).toENNReal`
over the full angle interval `(0,2π]`. At nonpositive values this encoding
preserves `-u`, including `u=-∞`, which becomes a positive-infinite integrand.
The unrestricted average definition is total for every real radius.

`IsNonpositiveSubharmonicOn u D` requires a connected domain, upper
semicontinuity on it, values at most zero there, and at least one domain point
with value different from negative infinity. At every domain point there
must be a positive closed-disk radius contained in the domain such that, for
all smaller positive radii, the negative circle average is at most `-u(z)`
in the stated nonnegative-extended-real encoding. Thus the sign-reversed
condition is the local circular submean inequality. Nonpositive values are
always strictly below positive infinity; negative infinity remains allowed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Complex

/-- The normalized nonnegative extended integral of `(-u).toENNReal` on the circle centered at `z`,
using the full-period angle measure. Negative-infinite values of a nonpositive function remain
positive infinity in the integrand. -/
noncomputable def negativeCircleAverage (u : ℂ → EReal) (z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨍⁻ θ in Set.Ioc 0 (2 * Real.pi), (-u (circleMap z r θ)).toENNReal ∂volume

/-- A connected-domain, upper-semicontinuous, nonpositive extended-real function with at least one
value above negative infinity and the displayed local sign-reversed circle submean condition. -/
structure IsNonpositiveSubharmonicOn (u : ℂ → EReal) (D : Set ℂ) : Prop where
  isConnected : IsConnected D
  upperSemicontinuousOn : UpperSemicontinuousOn u D
  nonpositive : ∀ z ∈ D, u z ≤ 0
  exists_ne_bot : ∃ z ∈ D, u z ≠ ⊥
  eventually_circleAverage_le :
    ∀ z ∈ D, ∃ ε > 0, Metric.closedBall z ε ⊆ D ∧
      ∀ r : ℝ, 0 < r → r < ε →
        negativeCircleAverage u z r ≤ (-u z).toENNReal

/-- Every domain value of a nonpositive subharmonic function is strictly below positive infinity.

```lean
theorem IsNonpositiveSubharmonicOn.lt_top {u : ℂ → EReal} {D : Set ℂ}
    (h : IsNonpositiveSubharmonicOn u D)
    {z : ℂ} (hz : z ∈ D) : u z < ⊤
``` -/
theorem IsNonpositiveSubharmonicOn.lt_top {u : ℂ → EReal} {D : Set ℂ}
    (h : IsNonpositiveSubharmonicOn u D)
    {z : ℂ} (hz : z ∈ D) : u z < ⊤ :=
  lt_of_le_of_lt (h.nonpositive z hz) EReal.zero_lt_top

end Complex
