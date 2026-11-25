/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy

/-!
# Information gain of a decision-tree split

A decision tree chooses the attribute to split on by its **information gain**: the entropy of the
label minus the expected entropy of the label after the split. For a finite joint law
`p : PMF (α × β)` of an attribute and a label, this is `H(Y) - H(Y | X)` (in bits), with
MathlibExt's `shannonEntropy` and `finiteConditionalEntropy`.

* `infoGain_eq`: the information gain is `H(X) + H(Y) - H(X, Y)`.
* `ofReal_infoGain`: it is the mutual information `I(X; Y)` (MathlibExt's
  `measureMutualInformation`, a Kullback–Leibler divergence).
* `infoGain_nonneg`: **no split has negative information gain** (conditioning does not increase
  entropy).
* `infoGain_eq_zero_iff`: the gain is zero exactly when the attribute and the label are
  independent, so the split carries no information about the label.

## References

* T. M. Mitchell, *Machine Learning*, McGraw-Hill, 1997, §3.4.1.
* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press, 2022, §18.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.InformationTheory

open MeasureTheory Real _root_.InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Information gain of a split.** Let $p$ be a joint probability law on $\alpha \times \beta$
with $\alpha$ and $\beta$ finite, the law of an attribute $X$ (first coordinate) and a label $Y$
(second coordinate). The information gain of splitting on $X$ for predicting $Y$ is the real
number $H(Y) - H(Y \mid X)$, where $H(Y)$ is the Shannon entropy in bits of the marginal law of
$Y$ and $H(Y \mid X)$ is the conditional entropy in bits of $Y$ given $X$ under $p$. -/
noncomputable def infoGain (p : PMF (α × β)) : ℝ :=
  shannonEntropy (p.map Prod.snd) - finiteConditionalEntropy p

/-- **Information gain in terms of entropies.** Let $p$ be a joint probability law on
$\alpha \times \beta$ with $\alpha$ and $\beta$ finite, and let $p_X$ and $p_Y$ be its marginal
laws on $\alpha$ and on $\beta$. Writing $H$ for Shannon entropy in bits, the information gain of
$p$ equals $H(p_X) + H(p_Y) - H(p)$. -/
theorem infoGain_eq (p : PMF (α × β)) :
    infoGain p = shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) -
      shannonEntropy p := by
  rw [infoGain, shannonEntropy_eq_add_finiteConditionalEntropy]
  ring

/-- **No split has negative information gain.** For every joint probability law $p$ on
$\alpha \times \beta$ with $\alpha$ and $\beta$ finite, the information gain of $p$ is at least
$0$. -/
theorem infoGain_nonneg (p : PMF (α × β)) : 0 ≤ infoGain p :=
  sub_nonneg.mpr (finiteConditionalEntropy_le p)

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

/-- **Information gain is mutual information.** Let $\alpha$ and $\beta$ be finite sets carrying
σ-algebras in which singletons are measurable, and let $p$ be a joint probability law on
$\alpha \times \beta$. The information gain of $p$, regarded as an element of $[0, \infty]$, equals
the mutual information in bits of $p$ viewed as a probability measure on $\alpha \times \beta$. -/
theorem ofReal_infoGain (p : PMF (α × β)) :
    ENNReal.ofReal (infoGain p) =
      measureMutualInformation (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) := by
  rw [measureMutualInformation_toMeasure, infoGain_eq]

/-- **Zero information gain means independence.** Let $\alpha$ and $\beta$ be finite sets carrying
σ-algebras in which singletons are measurable, and let $p$ be a joint probability law on
$\alpha \times \beta$. The information gain of $p$ is zero if and only if $p$, as a measure, equals
the product of its marginal law on $\alpha$ and its marginal law on $\beta$; that is, exactly when
the attribute (first coordinate) and the label (second coordinate) are independent. -/
theorem infoGain_eq_zero_iff (p : PMF (α × β)) :
    infoGain p = 0 ↔
      p.toMeasure = (p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure := by
  rw [← measureMutualInformation_toMeasure_eq_zero_iff, ← ofReal_infoGain,
    ENNReal.ofReal_eq_zero]
  exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h (infoGain_nonneg p)⟩

end Cslib.MachineLearning.InformationTheory
