/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bounded mean oscillation on the real line (statements)

A locally integrable `f : ℝ → ℝ` has bounded mean oscillation with constant `B` when
`⨍_I |f - f_I| ≤ B` for every bounded interval `I = [a, b]`, `a < b`, where `f_I = ⨍_I f`.
The condition is written out in each statement below rather than packaged as a definition.
Both statements are the one-dimensional cases of results stated on `ℝ^n` in the sources.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted

/-- **John–Nirenberg inequality.** There is an absolute constant `c > 0` such that for every
locally integrable `f : ℝ → ℝ` whose mean oscillation over every bounded interval is at most
`B > 0`, every interval `I = [a, b]` with `a < b` and every `α > 0`,
`|{x ∈ I : |f(x) - f_I| > α}| ≤ 2 |I| exp(-α / (c B))`
(F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
14 (1961), 415–426; statement as in A. K. Lerner, *A "local mean oscillation" decomposition and
some its applications*, lecture notes, inequality (2.1), with `n = 1`). -/
public theorem_wanted exists_volume_abs_sub_average_gt_le :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ, LocallyIntegrable f → ∀ B : ℝ, 0 < B →
      (∀ a b : ℝ, a < b → ⨍ x in Icc a b, |f x - ⨍ y in Icc a b, f y| ≤ B) →
      ∀ a b : ℝ, a < b → ∀ α : ℝ, 0 < α →
        volume {x | x ∈ Icc a b ∧ α < |f x - ⨍ y in Icc a b, f y|} ≤
          ENNReal.ofReal (2 * (b - a) * Real.exp (-α / (c * B)))

/-- **Fefferman's `H¹`–`BMO` inequality.** There is an absolute constant `C > 0` such that for
every locally integrable `b : ℝ → ℝ` whose mean oscillation over every bounded interval is at
most `B > 0`, and every bounded, measurable, compactly supported `f : ℝ → ℝ`,
`|∫ f b| ≤ C B ‖f‖_{H¹}`, where `‖f‖_{H¹} = ∫ sup_{|y - x| ≤ t} |P_t * f (y)| dx` is the `L¹`
norm of the non-tangential maximal function of the Poisson integral,
`P_t(x) = t / (π (t² + x²))`; this norm characterizes `H¹(ℝ)` (P. Auscher and E. Russ,
*Hardy spaces and divergence operators on strongly Lipschitz domains of ℝⁿ*,
arXiv:math/0201301v1, §1, display (1), citing Fefferman–Stein 1972, Theorem 11). This is the
inclusion `BMO ⊆ (H¹)*` of the duality theorem `(H¹)* = BMO`
(C. Fefferman, *Characterizations of bounded mean oscillation*, Bull. Amer. Math. Soc. 77
(1971), 587–588; C. Fefferman and E. M. Stein, *H^p spaces of several variables*, Acta Math.
129 (1972), 137–193; the duality is stated in A. K. Lerner, *A "local mean oscillation"
decomposition and some its applications*, lecture notes, §3.1). When `∫ f ≠ 0` the right-hand
side is infinite, so the content is the case `∫ f = 0`. -/
public theorem_wanted exists_enorm_integral_mul_le_poissonMaximal :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ → ℝ, LocallyIntegrable b → ∀ B : ℝ, 0 < B →
      (∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B) →
      ∀ f : ℝ → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) → HasCompactSupport f →
        ‖∫ x, f x * b x‖ₑ ≤ ENNReal.ofReal (C * B) *
          ∫⁻ x, ⨆ t : ℝ, ⨆ (_ : 0 < t), ⨆ y : ℝ, ⨆ (_ : |y - x| ≤ t),
            ‖∫ z, t / (Real.pi * (t ^ 2 + (y - z) ^ 2)) * f z‖ₑ

end MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted
