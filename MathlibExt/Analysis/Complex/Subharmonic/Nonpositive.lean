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

## References

Jiří Lebl, *Tasty Bits of Several Complex Variables*, Chapter 2 §4, “From harmonic to
plurisubharmonic functions”: the subharmonic-function definition uses upper semicontinuity and
harmonic comparison. The proposition “Mean-value property and sub-mean-value property”, part
(ii), gives the full-circle normalized submean inequality; the local-subharmonicity proposition
(`prop:shlocal`) permits that inequality for all sufficiently small positive radii at each
point. The nonpositive range, connected domain, and exclusion of the identically
negative-infinite function are additional restrictions of this interface. For `u≤0`, multiplying
the circular submean inequality by `-1` gives exactly the nonnegative extended-real average used
here.

[Source](https://github.com/jirilebl/scv/blob/ff52ab21051ac64190f28ce3dadbb9f881049a5e/scv.tex)
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Complex

/-- **Negative circular average of an extended-real function.** For `u : ℂ→EReal`, `z∈ℂ` and
any real radius `r`, define `negativeCircleAverage u z r = (1/(2π)) ∫⁻_{θ∈(0,2π]} (-u(z+r
exp(iθ))).toENNReal dθ`. This is a nonnegative extended Lebesgue average using the
full-period angle measure. When `u≤0`, the encoding retains `-u`; values `u=-∞` contribute
`+∞`. The definition is total, including zero and negative radii. -/
noncomputable def negativeCircleAverage (u : ℂ → EReal) (z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨍⁻ θ in Set.Ioc 0 (2 * Real.pi), (-u (circleMap z r θ)).toENNReal ∂volume

/-- **Local circular submean condition for a nonpositive function.** For `u : ℂ→EReal` and
`D⊆ℂ`, `IsNonpositiveSubharmonicOn u D` requires `D` connected, `u` upper semicontinuous
on `D`, `u(z)≤0` for every `z∈D`, and some `z∈D` with `u(z)≠-∞`. For each `z∈D` there must
exist `ε>0` with `closedBall z ε⊆D` such that for every `0<r<ε`,

`negativeCircleAverage u z r ≤ (-u(z)).toENNReal`,

where `negativeCircleAverage u z r=(1/(2π))∫⁻_{θ∈(0,2π]} (-u(z+r exp(iθ))).toENNReal dθ`.
Negative-infinite values are allowed, while the existence clause excludes the identically
negative-infinite function. -/
structure IsNonpositiveSubharmonicOn (u : ℂ → EReal) (D : Set ℂ) : Prop where
  isConnected : IsConnected D
  upperSemicontinuousOn : UpperSemicontinuousOn u D
  nonpositive : ∀ z ∈ D, u z ≤ 0
  exists_ne_bot : ∃ z ∈ D, u z ≠ ⊥
  eventually_circleAverage_le :
    ∀ z ∈ D, ∃ ε > 0, Metric.closedBall z ε ⊆ D ∧
      ∀ r : ℝ, 0 < r → r < ε →
        negativeCircleAverage u z r ≤ (-u z).toENNReal

/-- **Nonpositive subharmonic values are below positive infinity.** Let `u : ℂ→EReal`, `D⊆ℂ`,
and `h : IsNonpositiveSubharmonicOn u D`. For every `z∈D`, the nonpositivity condition
`u(z)≤0` implies `u(z)<+∞`. The value `-∞` is allowed. -/
theorem IsNonpositiveSubharmonicOn.lt_top {u : ℂ → EReal} {D : Set ℂ}
    (h : IsNonpositiveSubharmonicOn u D)
    {z : ℂ} (hz : z ∈ D) : u z < ⊤ :=
  lt_of_le_of_lt (h.nonpositive z hz) EReal.zero_lt_top

end Complex
