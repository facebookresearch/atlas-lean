/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BerryEsseenConstant
public import Batteries.Util.ProofWanted

/-!
# Source requests for the absolute i.i.d. Berry--Esseen constant

These propositions use actual standardized probability laws and normalized
i.i.d. sums. Every missing proof is private `ProofWanted` data, not a proof or
assumption. Decimal endpoints are source literals, not checked rounding
certificates. The catalogue's false four-term 2013 minimum is not requested.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BerryEsseenModel BerryEsseenConstant

namespace BerryEsseenWanted

/-- Source: catalogue C19a, upper row Z1967; the non-i.i.d. 0.9051 is context only. -/
def zolotarev1967UpperBound : Prop := value ≤ (82 / 100 : ℝ)

/-- Source: catalogue C19a, upper row vB1972; original primary text is not retained here. -/
def vanBeek1972UpperBound : Prop := value ≤ (7975 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row Shi1986; retained Shevtsova2011 introduction reports it. -/
def shiganov1986UpperBound : Prop := value ≤ (7655 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row She2006; retained Shevtsova2011 introduction reports it. -/
def shevtsova2006UpperBound : Prop := value ≤ (7056 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row KS2009; retained Shevtsova2011 lines 141-148. -/
def korolevShevtsova2009UpperBound : Prop := value ≤ (5129 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row Tyu2009; retained Shevtsova2011 lines 150-154. -/
def tyurin2009UpperBound : Prop := value ≤ (4785 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row She2011; retained arXiv1111.6554 Corollary 1. -/
def shevtsova2011UpperBound : Prop := value ≤ (4748 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row She2013. The original primary text and the
correct structural formula remain unresolved; this is only the literal bound request. -/
def shevtsova2013UpperBound : Prop := value ≤ (4690 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row XL2026, explicitly unverified. No external
repository certificate or compiler-trusting proof is accepted by this request. -/
def xiaoLi2026UnverifiedUpperBound : Prop := value ≤ (4395 / 10000 : ℝ)

/-- Source: catalogue C19a, upper row Lin2026, explicitly unverified. No external
repository certificate or comparator result is asserted here. -/
def lin2026UnverifiedUpperBound : Prop := value ≤ (423 / 1000 : ℝ)

/-- Source: catalogue C19a, KS2009 upper-row comment, and the exact retained
Shevtsova2011 quotation at lines 141-148. The additive offset is 0.489, not 0.429. -/
def korolevShevtsova2009Structural : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    kolmogorovError μ n ≤ (34445 / 100000 : ℝ) *
      (thirdMoment μ + 489 / 1000) / Real.sqrt (n.1 : ℝ)

/-- Source: catalogue C19a, lower row E1956, and retained Shevtsova2011 lines
185-194. The symbolic endpoint is not replaced by its decimal approximation. -/
def esseen1956LowerBound : Prop := esseenConstant ≤ value

/-- Source: catalogue C19a, lower-row Bernoulli asymptotic comment. A single
actual standardized two-point law is chosen before epsilon and the sample-size
threshold. Its normalized sums approach the lower coefficient along arbitrarily
large sample sizes; an original Esseen primary comparison remains a source gap. -/
def esseenBernoulliAsymptoticLowerBound : Prop :=
  ∃ μ : Measure ℝ, IsBernoulliLaw μ ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ+, N ≤ n.1 ∧
      (esseenConstant - ε) * thirdMoment μ / Real.sqrt (n.1 : ℝ) ≤ kolmogorovError μ n

/-- Source: catalogue C19a, Bernoulli/binomial comment and Sch2016 reference.
The actual subclass consists of centered variance-one two-point laws. The full
Schulz primary proof has not been acquired or verified in this lane. -/
def schulz2016BernoulliOptimum : Prop := bernoulliValue = esseenConstant

/-- Source: the right-CDF catalogue definition and retained Shevtsova2011
lines 104-108, which explicitly use a left-continuous CDF. This probability
bridge is requested, not inferred by replacing strict with non-strict events. -/
def leftRightCDFErrorEquivalence : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    sSup (Set.range (fun x : ℝ ↦
      |(normalizedLaw μ n).real (Set.Iio x) - normalCDF x|)) = kolmogorovError μ n

/-- Source: catalogue C19a, Z1967 upper row. -/
theorem_wanted zolotarev1967UpperBound_holds : zolotarev1967UpperBound

/-- Source: catalogue C19a, vB1972 upper row. -/
theorem_wanted vanBeek1972UpperBound_holds : vanBeek1972UpperBound

/-- Source: catalogue C19a, Shi1986 upper row. -/
theorem_wanted shiganov1986UpperBound_holds : shiganov1986UpperBound

/-- Source: catalogue C19a, She2006 upper row. -/
theorem_wanted shevtsova2006UpperBound_holds : shevtsova2006UpperBound

/-- Source: catalogue C19a, KS2009 upper row; retained Shevtsova2011 quotation. -/
theorem_wanted korolevShevtsova2009UpperBound_holds : korolevShevtsova2009UpperBound

/-- Source: catalogue C19a, Tyu2009 upper row. -/
theorem_wanted tyurin2009UpperBound_holds : tyurin2009UpperBound

/-- Source: catalogue C19a, She2011 upper row; retained primary Corollary 1. -/
theorem_wanted shevtsova2011UpperBound_holds : shevtsova2011UpperBound

/-- Source: catalogue C19a, She2013 upper row; the primary correction is unresolved. -/
theorem_wanted shevtsova2013UpperBound_holds : shevtsova2013UpperBound

/-- Source: catalogue C19a, explicitly unverified XL2026 row. -/
theorem_wanted xiaoLi2026UnverifiedUpperBound_holds : xiaoLi2026UnverifiedUpperBound

/-- Source: catalogue C19a, explicitly unverified Lin2026 row. -/
theorem_wanted lin2026UnverifiedUpperBound_holds : lin2026UnverifiedUpperBound

/-- Source: catalogue C19a, KS2009 structural comment; retained 2011 equation. -/
theorem_wanted korolevShevtsova2009Structural_holds : korolevShevtsova2009Structural

/-- Source: catalogue C19a, E1956 lower row; retained 2011 exact benchmark. -/
theorem_wanted esseen1956LowerBound_holds : esseen1956LowerBound

/-- Source: catalogue C19a, the asymptotic normalized Bernoulli lower-row clause. -/
theorem_wanted esseenBernoulliAsymptoticLowerBound_holds : esseenBernoulliAsymptoticLowerBound

/-- Source: catalogue C19a, Bernoulli/binomial comment, Schulz2016. -/
theorem_wanted schulz2016BernoulliOptimum_holds : schulz2016BernoulliOptimum

/-- Source: catalogue C19a right CDF and Shevtsova2011's explicit left convention. -/
theorem_wanted leftRightCDFErrorEquivalence_holds : leftRightCDFErrorEquivalence

end BerryEsseenWanted
