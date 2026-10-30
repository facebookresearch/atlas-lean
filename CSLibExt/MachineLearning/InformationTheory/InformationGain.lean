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

/-- The **information gain** `H(Y) - H(Y | X)` of splitting on the attribute `X` (first
coordinate) for predicting the label `Y` (second coordinate), in bits. -/
noncomputable def infoGain (p : PMF (α × β)) : ℝ :=
  shannonEntropy (p.map Prod.snd) - finiteConditionalEntropy p

/-- The information gain is `H(X) + H(Y) - H(X, Y)`. -/
theorem infoGain_eq (p : PMF (α × β)) :
    infoGain p = shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) -
      shannonEntropy p := by
  rw [infoGain, shannonEntropy_eq_add_finiteConditionalEntropy]
  ring

/-- **No split has negative information gain.** -/
theorem infoGain_nonneg (p : PMF (α × β)) : 0 ≤ infoGain p :=
  sub_nonneg.mpr (finiteConditionalEntropy_le p)

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

/-- **Information gain is mutual information.** -/
theorem ofReal_infoGain (p : PMF (α × β)) :
    ENNReal.ofReal (infoGain p) =
      measureMutualInformation (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) := by
  rw [measureMutualInformation_toMeasure, infoGain_eq]

/-- The gain is zero exactly when the attribute and the label are independent. -/
theorem infoGain_eq_zero_iff (p : PMF (α × β)) :
    infoGain p = 0 ↔
      p.toMeasure = (p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure := by
  rw [← measureMutualInformation_toMeasure_eq_zero_iff, ← ofReal_infoGain,
    ENNReal.ofReal_eq_zero]
  exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h (infoGain_nonneg p)⟩

end Cslib.MachineLearning.InformationTheory
