/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.LargeDeviationPrinciple
public import MathlibExt.Probability.LegendreTransform
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The Gärtner–Ellis theorem (wanted)

Cramér's theorem uses independence only through the identity
`(1/n) log E[exp ⟪t, Sₙ⟫] = log E[exp ⟪t, X₀⟫]`. The Gärtner–Ellis theorem keeps only the
existence of the limit `Λ(t) = lim (1/n) log E[exp (n ⟪t, Zₙ⟫)]` of the scaled cumulant
generating functions: if `Λ` is regular enough (essentially smooth and lower semicontinuous,
with `0` in the interior of its domain), the laws of `Zₙ` satisfy the large deviation
principle with the good rate function `Λ*`, the Legendre transform of `Λ`. In Varadhan's
words, log generating functions are dual to rate functions; here the duality is inverted.

The statement below is the special case where `Λ` is finite and differentiable on all of
`ℝᵈ`, which is essentially smooth with full domain.

## Source

A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer,
1998, Section 2.3 (the Gärtner–Ellis theorem); originally J. Gärtner, *Teor. Verojatnost. i
Primenen.* 22 (1977), 27–42, and R. S. Ellis, *Ann. Probab.* 12 (1984), 1–12. The role of the
limiting log generating function is discussed in S. R. S. Varadhan, "Large deviations",
*Ann. Probab.* 36 (2008), Sections 2 and 10 (arXiv:0804.2330).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.LegendreTransform

namespace MathlibExt.Probability.GartnerEllisWanted

/-- **Gärtner–Ellis theorem, differentiable case.** Let `νₙ` be probability measures on
`ℝᵈ` (the laws of random vectors `Zₙ`) such that `x ↦ exp (n ⟪t, x⟫)` is `νₙ`-integrable for
all `n` and `t`, and suppose the scaled cumulant generating functions converge,
`(1/n) log ∫ exp (n ⟪t, x⟫) dνₙ(x) → Λ(t)` for every `t`, to a function `Λ : ℝᵈ → ℝ` that is
differentiable everywhere. Then `νₙ` satisfies the large deviation principle with the good
rate function `Λ*(x) = sup_t (⟪t, x⟫ - Λ(t))`.
Source: A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
Section 2.3 (the case of a finite, everywhere differentiable limit, which is essentially
smooth). -/
theorem_wanted satisfiesLDP_of_tendsto_scaledCGF {d : ℕ}
    {ν : ℕ → Measure (EuclideanSpace ℝ (Fin d))} [∀ n, IsProbabilityMeasure (ν n)]
    (hexp : ∀ (n : ℕ) (t : EuclideanSpace ℝ (Fin d)),
      Integrable (fun x => Real.exp (n * ⟪t, x⟫_ℝ)) (ν n))
    {Λ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hlim : ∀ t, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      Real.log (∫ x, Real.exp (n * ⟪t, x⟫_ℝ) ∂(ν n))) atTop (𝓝 (Λ t)))
    (hdiff : Differentiable ℝ Λ) :
    SatisfiesLDP ν (fun x => (legendreTransform (fun t => (Λ t : EReal)) x).toENNReal) ∧
      IsGoodRateFunction (fun x => (legendreTransform (fun t => (Λ t : EReal)) x).toENNReal)

end MathlibExt.Probability.GartnerEllisWanted
