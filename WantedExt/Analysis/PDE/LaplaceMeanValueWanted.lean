/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PDE.LaplaceMeanValue
public import MathlibExt.Analysis.PDE.LaplaceStrongMaximumPrinciple
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Harnack's inequality for harmonic functions

This module records Harnack's inequality for nonnegative harmonic functions on a connected
open set compactly contained in their domain. The ball mean-value property and its converse
are proved in `MathlibExt.Analysis.PDE.LaplaceMeanValue`.

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
