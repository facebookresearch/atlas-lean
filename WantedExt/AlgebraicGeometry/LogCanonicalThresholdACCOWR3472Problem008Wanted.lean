/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACC for log canonical thresholds on smooth varieties (Oberwolfach Reports 22/2009)

Oberwolfach workshop Kommutative Algebra (2009), L. Ein (with T. de Fernex and M. Mustaţă), Theorem
0.1 stated as a question: for every `n`, does the set of log canonical thresholds of ideals on
smooth complex `n`-dimensional varieties satisfy the ascending chain condition?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.LogCanonicalThresholdACCOWR3472Problem008Wanted

/-!
Source: L. Ein (with T. de Fernex and M. Mustaţă), in Kommutative Algebra, Oberwolfach Reports 6
(2009), no. 22, p. 1182, Theorem 0.1, DOI 10.4171/OWR/2009/22. UnsolvedMath record UM-30001238
(`OWR-3472-008`), dataset ulamai/UnsolvedMath v1.8.0.

De Fernex, Ein and Mustaţă recall (Section 2, after de Fernex-Mustaţă, Proposition 3.3) that for `n
≥ 1` the source's set `T_n^sm` equals `{lct₀(a) | a ⊆ (x₁, …, xₙ) ⊂ k[x₁, …, xₙ]}`; the statement
uses the nonzero ideals `(f₁, …, f_r) ⊆ ℂ[x₁, …, xₙ]` vanishing at `0`, so its set is contained in
`T_n^sm` (the zero ideal only adds the convention value `0`). The threshold at `0` is taken in its
analytic form, the supremum of the `c ≥ 0` with `(∑ |f_i|²)^{-c}` integrable near `0` (`ℂⁿ` with
Lebesgue measure), which is `lct₀` by Theorem 1.2 of M. Mustaţă, IMPANGA lecture notes on log
canonical thresholds, EMS Ser. Congr. Rep. (2012), 407-442, arXiv:1107.2676. ACC is the absence of a
strictly increasing sequence.
-/

open MeasureTheory

/-- The log canonical threshold at the origin of the ideal `(f₁, …, f_r) ⊆ ℂ[x₁, …, xₙ]`, in its
analytic form: the supremum of the `c ≥ 0` for which `(∑ |f_i|²)^{-c}` is integrable on some ball
around the origin. -/
noncomputable def lctAtOrigin {n r : ℕ} (f : Fin r → MvPolynomial (Fin n) ℂ) : ℝ :=
  sSup {c : ℝ | 0 ≤ c ∧ ∃ ε > 0, IntegrableOn
    (fun z : Fin n → ℂ => (∑ i, ‖MvPolynomial.eval z (f i)‖ ^ 2) ^ (-c)) (Metric.ball 0 ε)}

/-- The log canonical thresholds at the origin of the nonzero ideals of `ℂ[x₁, …, xₙ]` that vanish
at the origin. -/
def lctSet (n : ℕ) : Set ℝ :=
  {t | ∃ (r : ℕ) (f : Fin r → MvPolynomial (Fin n) ℂ), (∃ i, f i ≠ 0) ∧
    (∀ i, MvPolynomial.eval 0 (f i) = 0) ∧ lctAtOrigin f = t}

/-- Shokurov's ACC conjecture on smooth varieties (Oberwolfach Report 22/2009, p. 1182): for every
`n`, the set of log canonical thresholds of ideals on smooth complex `n`-dimensional varieties
satisfies the ascending chain condition, i.e. contains no strictly increasing sequence. -/
def lctAscendingChainCondition : Prop :=
  ∀ n : ℕ, ¬ ∃ a : ℕ → ℝ, StrictMono a ∧ ∀ k, a k ∈ lctSet n

/--
Resolved true: de Fernex, Ein and Mustaţă proved (Theorem 1.1) that for every `n` the set `T_n^sm`
of log canonical thresholds of proper ideals on smooth varieties of dimension `n` satisfies the
ascending chain condition (Shokurov's conjecture in the smooth case); for `n ≥ 1` this set consists
of the thresholds at the origin of the ideals of `k[x₁, …, xₙ]` contained in `(x₁, …, xₙ)` (their
Section 2), and these thresholds have the analytic description used here (Mustaţă, IMPANGA notes,
Theorem 1.2). Source: L. Ein (with T. de Fernex and M. Mustaţă), in Kommutative Algebra, Oberwolfach
Reports 6 (2009), no. 22, p. 1182, Theorem 0.1, DOI 10.4171/OWR/2009/22; resolution: T. de Fernex,
L. Ein and M. Mustaţă, Shokurov's ACC conjecture for log canonical thresholds on smooth varieties,
Duke Math. J. 152 (2010), 93-114, arXiv:0905.3775, Theorem 1.1: for every n the set T_n^sm = {lct(a)
| X smooth, dim X = n, a ⊊ O_X} of log canonical thresholds on smooth varieties of dimension n
satisfies the ascending chain condition; Section 2: T_n^sm = {lct_0(a) | a ⊆ (x_1, ..., x_n) ⊂
k[x_1, ..., x_n]} for n ≥ 1, https://arxiv.org/abs/0905.3775.
-/
public theorem_wanted lctAscendingChainCondition_holds : lctAscendingChainCondition

end MathlibExt.AlgebraicGeometry.LogCanonicalThresholdACCOWR3472Problem008Wanted
