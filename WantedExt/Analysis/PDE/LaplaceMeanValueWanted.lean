/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PDE.LaplaceStrongMaximumPrinciple
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Mean-value property and Harnack's inequality for harmonic functions

Two classical properties of harmonic functions on open subsets of a finite-dimensional real inner
product space (Lebesgue measure on `ℝⁿ`), stated with Mathlib's `InnerProductSpace.HarmonicOnNhd`
and recorded as wanted:

* the mean-value property and its converse: a `C²` function is harmonic on `U` if and only if its
  average over every closed ball `closedBall x r ⊆ U` equals its value at the centre;
* Harnack's inequality for nonnegative harmonic functions on `V ⊂⊂ U`, `V` connected.

Mathlib proves the mean-value property for harmonic functions on the plane through circle
averages (`InnerProductSpace.HarmonicOnNhd.circleAverage_eq`); the `n`-dimensional ball-average
version needs the divergence theorem on balls. The weak maximum principle, which needs neither, is
proved in `MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple`.

## References

* M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  Chapter 3 (Laplace equation),
  https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf: Mean Value
  Property 3.3, Harnack's Inequality 3.8 and Strong Maximum Principle 3.10.
* L. C. Evans, *Entropy and Partial Differential Equations*, lecture notes,
  https://math.berkeley.edu/~evans/entropy.and.PDE.pdf, Chapter IV.A.3, Theorem 3 (Harnack's
  inequality) and Corollary (strong maximum principle) for `-∑ (aⁱʲ u_{xᵢ})_{xⱼ} = 0`.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.LaplaceMeanValueWanted

open InnerProductSpace Metric MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Mean-value property of harmonic functions, and its converse.** Let `U` be open and `u` be
`C²` on `U`. Then `u` is harmonic on `U` if and only if `⨍_{closedBall x r} u = u x` for every
closed ball of positive radius contained in `U`. This is Mean Value Property 3.3 of M. Schmidt,
*Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, Chapter 3, in
its ball-average form (balls with compact closure in `U`; the source also gives sphere averages). -/
theorem_wanted harmonicOnNhd_iff_forall_average_closedBall {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) :
    HarmonicOnNhd u U ↔
      ∀ x : E, ∀ r : ℝ, 0 < r → closedBall x r ⊆ U → ⨍ y in closedBall x r, u y = u x

/-- **Harnack's inequality for harmonic functions.** Let `U` be open and let `V` be open and
connected with `closure V` compact and contained in `U`. There is a constant `C > 0`, depending
only on `V` and `U`, such that every nonnegative harmonic function `u` on `U` satisfies
`u x ≤ C u y` for all `x, y ∈ V`; equivalently `sup_V u ≤ C inf_V u`. This is Harnack's
Inequality 3.8 of M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 3 (in its pointwise form "for all `x, y ∈ Ω′`"), and the case
`aⁱʲ = δⁱʲ` of Theorem 3 of Chapter IV.A.3 of L. C. Evans, *Entropy and Partial Differential
Equations*. -/
theorem_wanted harnack_inequality {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hVconn : IsConnected V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, HarmonicOnNhd u U → (∀ x ∈ U, 0 ≤ u x) →
      ∀ x ∈ V, ∀ y ∈ V, u x ≤ C * u y

end MathlibExt.Analysis.PDE.LaplaceMeanValueWanted
