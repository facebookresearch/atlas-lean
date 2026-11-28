/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import CSLibExt.MachineLearning.PACLearning.NearestNeighbor
public import Mathlib.Probability.Kernel.Disintegration.Basic
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Topology.UnitInterval

/-!
# Joint-law binary Bayes optimality

For a joint probability distribution `D` over `X × Bool` (Shalev-Shwartz and
Ben-David, *Understanding Machine Learning: From Theory to Algorithms* (2014),
§3.2.1), the Bayes optimal predictor thresholds the conditional label
probability at `1/2`, and no classifier has lower 0-1 error (Exercise 3.7).
Labels are `Bool`, with `true` as label 1 and `false` as label 0.

The conditional label probability is read off a disintegrating Markov kernel
(`kernelTrueProb`), and the predictor reuses the existing
`binaryBayesClassifier` threshold (`1/2 < η`, ties to `false`). The textbook
display sends the tie `η = 1/2` to label 1 instead; both tie choices incur the
same conditional error `1/2`, so the optimality and risk statements are
unaffected by the tie convention.

Scope: `D` ranges over probability measures only; labels are binary; optimality
quantifies over measurable rivals, although `error` itself is total.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory ProbabilityTheory

/-- The conditional true-label probability at `x` from a Markov label kernel:
the kernel mass of `{true}`, as a point of the unit interval. For the regular
conditional probability `D.condKernel` of a joint law `D`, this is `P[y = 1 | x]`.
Deterministic labels give the endpoints `0` and `1`. -/
noncomputable def kernelTrueProb {X : Type*} [MeasurableSpace X]
    (κ : Kernel X Bool) [IsMarkovKernel κ] (x : X) : unitInterval :=
  ⟨(κ x {true}).toReal, by
    change (0 : ℝ) ≤ (κ x {true}).toReal ∧ (κ x {true}).toReal ≤ 1
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hle : (κ x {true}).toReal ≤ (1 : ENNReal).toReal :=
      ENNReal.toReal_mono (by simp) prob_le_one
    rwa [ENNReal.toReal_one] at hle⟩

/-- The conditional true-label probability of a Markov kernel is measurable. -/
theorem measurable_kernelTrueProb {X : Type*} [MeasurableSpace X]
    (κ : Kernel X Bool) [IsMarkovKernel κ] :
    Measurable (kernelTrueProb κ) := by
  have htoReal : Measurable fun x => (κ x {true}).toReal :=
    ENNReal.measurable_toReal.comp
      (Kernel.measurable_coe κ (measurableSet_singleton true))
  exact htoReal.subtype_mk

/-- A classifier's 0-1 error under a disintegrated joint law is the marginal
lower integral of its conditional wrong-label mass. -/
private theorem error_eq_lintegral_wrongProb {X : Type*} [MeasurableSpace X]
    (D : Measure (X × Bool)) [IsProbabilityMeasure D]
    (κ : Kernel X Bool) [IsMarkovKernel κ] [D.IsCondKernel κ]
    (g : X → Bool) (hg : Measurable g) :
    error D g = ∫⁻ x, (if g x then κ x {false} else κ x {true}) ∂D.fst := by
  have hs : MeasurableSet {p : X × Bool | g p.1 ≠ p.2} :=
    (measurableSet_eq_fun (hg.comp measurable_fst) measurable_snd).compl
  have hsec : ∀ x : X, Prod.mk x ⁻¹' {p : X × Bool | g p.1 ≠ p.2}
      = (if g x then ({false} : Set Bool) else {true}) := by
    intro x
    cases hgx : g x <;> ext y <;> cases y <;> simp [hgx]
  unfold error
  conv_lhs => rw [← Measure.disintegrate D κ]
  rw [Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  rw [hsec x, apply_ite (κ x)]

/-- At each point, the Bayes predictor's conditional wrong-label mass is the
minimum of the two conditional label masses. -/
private theorem bayes_condError_eq_min {X : Type*} [MeasurableSpace X]
    (κ : Kernel X Bool) [IsMarkovKernel κ] (x : X) :
    (if binaryBayesClassifier (kernelTrueProb κ) x then κ x {false}
      else κ x {true}) = min (κ x {true}) (κ x {false}) := by
  have hdisj : Disjoint ({true} : Set Bool) {false} :=
    Set.disjoint_singleton.2 (by decide)
  have hunion : ({true} : Set Bool) ∪ {false} = Set.univ := by
    ext b
    cases b <;> simp
  have hsum : κ x {true} + κ x {false} = 1 := by
    have h : κ x ({true} ∪ {false}) = κ x {true} + κ x {false} :=
      measure_union hdisj (measurableSet_singleton false)
    rw [hunion, measure_univ] at h
    exact h.symm
  have ht1 : κ x {true} ≠ ⊤ := ne_top_of_le_ne_top (by simp) prob_le_one
  have ht2 : κ x {false} ≠ ⊤ := ne_top_of_le_ne_top (by simp) prob_le_one
  have hmass : (κ x {true}).toReal + (κ x {false}).toReal = 1 := by
    have h := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add ht1 ht2, ENNReal.toReal_one] at h
  have hval : ((kernelTrueProb κ x : unitInterval) : ℝ)
      = (κ x {true}).toReal := rfl
  unfold binaryBayesClassifier
  rw [hval]
  by_cases h : (1 : ℝ) / 2 < (κ x {true}).toReal
  · rw [ite_eq_left h]
    change κ x {false} = min (κ x {true}) (κ x {false})
    rw [min_eq_right ((ENNReal.toReal_le_toReal ht2 ht1).mp (by linarith))]
  · rw [ite_eq_right h]
    change κ x {true} = min (κ x {true}) (κ x {false})
    rw [min_eq_left ((ENNReal.toReal_le_toReal ht1 ht2).mp (by linarith))]

/-- **Bayes optimality, kernel version.** For a probability joint law `D`
disintegrated by a Markov conditional kernel `κ`, thresholding the conditional
true-label probability at `1/2` minimizes 0-1 `error` over all measurable rival
classifiers. Any disintegrating version gives the same conclusion. -/
theorem error_binaryBayesClassifier_le {X : Type*} [MeasurableSpace X]
    (D : Measure (X × Bool)) [IsProbabilityMeasure D]
    (κ : Kernel X Bool) [IsMarkovKernel κ] [D.IsCondKernel κ]
    (g : X → Bool) (hg : Measurable g) :
    error D (binaryBayesClassifier (kernelTrueProb κ)) ≤ error D g := by
  have hBayes : Measurable (binaryBayesClassifier (kernelTrueProb κ)) :=
    measurable_binaryBayesClassifier (measurable_kernelTrueProb κ)
  rw [error_eq_lintegral_wrongProb D κ (binaryBayesClassifier (kernelTrueProb κ)) hBayes,
    error_eq_lintegral_wrongProb D κ g hg]
  apply lintegral_mono
  intro x
  change (if binaryBayesClassifier (kernelTrueProb κ) x then κ x {false}
      else κ x {true}) ≤ (if g x then κ x {false} else κ x {true})
  rw [bayes_condError_eq_min κ x]
  split_ifs with hgx
  · exact min_le_right _ _
  · exact min_le_left _ _

/-- **Bayes optimality for every joint law.** For every probability distribution
`D` on `X × Bool`, the Bayes predictor built from the regular conditional
probability `D.condKernel` has no greater 0-1 `error` than any measurable classifier.
Nonmeasurable rivals are outside this clause, although `error` itself is total. -/
theorem error_binaryBayesClassifier_condKernel_le {X : Type*} [MeasurableSpace X]
    (D : Measure (X × Bool)) [IsProbabilityMeasure D]
    (g : X → Bool) (hg : Measurable g) :
    error D (binaryBayesClassifier (kernelTrueProb D.condKernel)) ≤ error D g := by
  exact error_binaryBayesClassifier_le D D.condKernel g hg

/-- The Bayes predictor attains the optimal 0-1 error over the class of
measurable classifiers. -/
theorem optimalError_measurable_eq_error_binaryBayesClassifier {X : Type*}
    [MeasurableSpace X] (D : Measure (X × Bool)) [IsProbabilityMeasure D] :
    optimalError D {g : X → Bool | Measurable g} =
      error D (binaryBayesClassifier (kernelTrueProb D.condKernel)) := by
  have hBayes : Measurable (binaryBayesClassifier (kernelTrueProb D.condKernel)) :=
    measurable_binaryBayesClassifier (measurable_kernelTrueProb D.condKernel)
  unfold optimalError
  apply le_antisymm
  · exact iInf₂_le _ hBayes
  · apply le_iInf₂
    intro g hg
    exact error_binaryBayesClassifier_condKernel_le D g hg

/-- **Bayes-risk formula.** The 0-1 error of the Bayes predictor is the marginal
mean of the pointwise minimum of the conditional true- and false-label
probabilities. At the tie `η = 1/2` both labels err with probability `1/2`,
matching the minimum. -/
theorem error_binaryBayesClassifier_eq_lintegral_min {X : Type*} [MeasurableSpace X]
    (D : Measure (X × Bool)) [IsProbabilityMeasure D]
    (κ : Kernel X Bool) [IsMarkovKernel κ] [D.IsCondKernel κ] :
    error D (binaryBayesClassifier (kernelTrueProb κ)) =
      ∫⁻ x, min (κ x {true}) (κ x {false}) ∂D.fst := by
  have hBayes : Measurable (binaryBayesClassifier (kernelTrueProb κ)) :=
    measurable_binaryBayesClassifier (measurable_kernelTrueProb κ)
  rw [error_eq_lintegral_wrongProb D κ (binaryBayesClassifier (kernelTrueProb κ)) hBayes]
  apply lintegral_congr
  intro x
  exact bayes_condError_eq_min κ x

end Cslib.MachineLearning.PACLearning
