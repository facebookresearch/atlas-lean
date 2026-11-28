/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.BayesOptimal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Disintegration.Basic
public import Mathlib.Tactic.NormNum

/-!
# Tests for joint-law binary Bayes optimality

Finite checks on `Bool × Bool`: a noisy law with Bayes risk `1 / 4` (including
the tie conditional probability `1 / 2`), a deterministic law with zero Bayes
risk, and endpoint values of the kernel true-label probability.
-/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Noisy joint law on `Bool × Bool`: mass `1 / 2` at `(false, false)`, mass
`1 / 4` at `(true, true)` and mass `1 / 4` at `(true, false)`. -/
private noncomputable def noisyLaw : Measure (Bool × Bool) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (false, false)
    + (1 / 4 : ℝ≥0∞) • Measure.dirac (true, true)
    + (1 / 4 : ℝ≥0∞) • Measure.dirac (true, false)

private instance noisyLaw_prob : IsProbabilityMeasure noisyLaw where
  measure_univ := by
    simp [noisyLaw]
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num

/-- Disintegrating kernel for `noisyLaw`: deterministic `false` above `false`,
a fair coin above `true`. -/
private noncomputable def noisyKernel : Kernel Bool Bool where
  toFun := fun
    | false => Measure.dirac false
    | true =>
        (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false
  measurable' := measurable_of_countable _

private instance noisyKernel_markov : IsMarkovKernel noisyKernel where
  isProbabilityMeasure := by
    intro x
    cases x
    · exact ⟨by simp [noisyKernel]⟩
    · exact ⟨by
        simp [noisyKernel]
        rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
        rw [ENNReal.toReal_add (by simp) (by simp)]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num⟩

/-- Mass of `noisyLaw` at `(false, false)`. -/
private theorem noisyLaw_ff : noisyLaw {(false, false)} = 1 / 2 := by
  simp [noisyLaw]

/-- Mass of `noisyLaw` at `(true, true)`. -/
private theorem noisyLaw_tt : noisyLaw {(true, true)} = 1 / 4 := by
  simp [noisyLaw]

/-- Mass of `noisyLaw` at `(true, false)`. -/
private theorem noisyLaw_tf : noisyLaw {(true, false)} = 1 / 4 := by
  simp [noisyLaw]

/-- Mass of `noisyLaw` at `(false, true)`. -/
private theorem noisyLaw_ft : noisyLaw {(false, true)} = 0 := by
  simp [noisyLaw]

/-- True-label mass of `noisyKernel` above `false`. -/
private theorem noisyKernel_false_true : noisyKernel false {true} = 0 := by
  simp [noisyKernel]

/-- False-label mass of `noisyKernel` above `false`. -/
private theorem noisyKernel_false_false : noisyKernel false {false} = 1 := by
  simp [noisyKernel]

/-- True-label mass of `noisyKernel` above `true`: the tie `1 / 2`. -/
private theorem noisyKernel_true_true : noisyKernel true {true} = 1 / 2 := by
  simp [noisyKernel]

/-- False-label mass of `noisyKernel` above `true`: the tie `1 / 2`. -/
private theorem noisyKernel_true_false : noisyKernel true {false} = 1 / 2 := by
  simp [noisyKernel]

/-- Marginal mass of `noisyLaw` at `false`. -/
private theorem noisyFst_false : noisyLaw.fst {false} = 1 / 2 := by
  rw [Measure.fst_apply (measurableSet_singleton false)]
  have hpre : Prod.fst ⁻¹' ({false} : Set Bool)
      = ({false} : Set Bool) ×ˢ (Set.univ : Set Bool) := by
    ext p
    simp
  rw [hpre]
  simp [noisyLaw]

/-- Marginal mass of `noisyLaw` at `true`. -/
private theorem noisyFst_true : noisyLaw.fst {true} = 1 / 2 := by
  rw [Measure.fst_apply (measurableSet_singleton true)]
  have hpre : Prod.fst ⁻¹' ({true} : Set Bool)
      = ({true} : Set Bool) ×ˢ (Set.univ : Set Bool) := by
    ext p
    simp
  rw [hpre]
  simp [noisyLaw]
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- `noisyKernel` disintegrates `noisyLaw`. -/
private instance noisyLaw_condKernel : noisyLaw.IsCondKernel noisyKernel where
  disintegrate := by
    rw [Measure.ext_iff_singleton]
    intro p
    obtain ⟨b1, b2⟩ := p
    cases b1 <;> cases b2 <;>
      simp only [← Set.singleton_prod_singleton,
        Measure.compProd_apply_prod (measurableSet_singleton _)
          (measurableSet_singleton _),
        Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac,
        smul_eq_mul]
    · rw [Set.singleton_prod_singleton, noisyFst_false, noisyKernel_false_false,
        noisyLaw_ff, mul_one]
    · rw [Set.singleton_prod_singleton, noisyFst_false, noisyKernel_false_true,
        noisyLaw_ft, mul_zero]
    · rw [Set.singleton_prod_singleton, noisyFst_true, noisyKernel_true_false,
        noisyLaw_tf]
      have hs : ((1 / 2 : ℝ≥0∞) * (1 / 2)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (by simp)
      rw [← ENNReal.toReal_eq_toReal_iff' hs (by simp)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat]
      norm_num
    · rw [Set.singleton_prod_singleton, noisyFst_true, noisyKernel_true_true,
        noisyLaw_tt]
      have hs : ((1 / 2 : ℝ≥0∞) * (1 / 2)) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (by simp)
      rw [← ENNReal.toReal_eq_toReal_iff' hs (by simp)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat]
      norm_num

/-- Bayes risk of the noisy law via the explicit kernel: `1 / 4`. -/
private theorem noisyBayes_error :
    error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyKernel))
      = 1 / 4 := by
  rw [error_binaryBayesClassifier_eq_lintegral_min noisyLaw noisyKernel]
  rw [lintegral_fintype, Fintype.sum_bool]
  have mtrue :
      min (noisyKernel true {true}) (noisyKernel true {false}) = 1 / 2 := by
    rw [noisyKernel_true_true, noisyKernel_true_false, min_self]
  have mfalse :
      min (noisyKernel false {true}) (noisyKernel false {false}) = 0 := by
    rw [noisyKernel_false_true, noisyKernel_false_false, min_eq_left zero_le]
  rw [mtrue, mfalse, noisyFst_false, noisyFst_true]
  have hs1 : ((1 / 2 : ℝ≥0∞) * (1 / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hs2 : ((0 : ℝ≥0∞) * (1 / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hs1, hs2⟩) (by simp)]
  rw [ENNReal.toReal_add hs1 hs2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, ENNReal.toReal_zero]
  norm_num

/-- Bayes risk of the noisy law via the regular conditional probability. -/
private theorem noisyBayes_condKernel_error :
    error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyLaw.condKernel))
      = 1 / 4 := by
  have hBayesK : Measurable (binaryBayesClassifier (kernelTrueProb noisyKernel)) :=
    measurable_binaryBayesClassifier (measurable_kernelTrueProb noisyKernel)
  have hBayesC : Measurable
      (binaryBayesClassifier (kernelTrueProb noisyLaw.condKernel)) :=
    measurable_binaryBayesClassifier (measurable_kernelTrueProb noisyLaw.condKernel)
  have h1 : error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyLaw.condKernel))
      ≤ error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyKernel)) :=
    error_binaryBayesClassifier_condKernel_le noisyLaw _ hBayesK
  have h2 : error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyKernel))
      ≤ error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyLaw.condKernel)) :=
    error_binaryBayesClassifier_le noisyLaw noisyKernel _ hBayesC
  rw [noisyBayes_error] at h1 h2
  exact le_antisymm h1 h2

/-- Optimal error of the noisy law over measurable classifiers: `1 / 4`. -/
private theorem noisyOptimal_error :
    optimalError noisyLaw {g : Bool → Bool | Measurable g} = 1 / 4 := by
  rw [optimalError_measurable_eq_error_binaryBayesClassifier noisyLaw,
    noisyBayes_condKernel_error]

/-- No classifier has zero error under the noisy law. -/
private theorem noisy_noZeroError (g : Bool → Bool) : error noisyLaw g ≠ 0 := by
  have hgm : Measurable g := measurable_of_countable g
  have hle : error noisyLaw (binaryBayesClassifier (kernelTrueProb noisyLaw.condKernel))
      ≤ error noisyLaw g :=
    error_binaryBayesClassifier_condKernel_le noisyLaw g hgm
  rw [noisyBayes_condKernel_error] at hle
  intro h0
  rw [h0] at hle
  exact absurd hle (by simp)

/-- Deterministic joint law: all mass at `(true, true)`. -/
private noncomputable def detLaw : Measure (Bool × Bool) :=
  Measure.dirac (true, true)

private instance detLaw_prob : IsProbabilityMeasure detLaw where
  measure_univ := by
    simp [detLaw]

/-- Constant true-label kernel disintegrating `detLaw`. -/
private noncomputable def detKernel : Kernel Bool Bool where
  toFun := fun _ => Measure.dirac true
  measurable' := measurable_const

private instance detKernel_markov : IsMarkovKernel detKernel where
  isProbabilityMeasure := fun x => ⟨by simp [detKernel]⟩

/-- Marginal of the deterministic law. -/
private theorem detFst : detLaw.fst = Measure.dirac true := by
  rw [Measure.ext_iff_singleton]
  intro b
  cases b <;> rw [detLaw, Measure.fst_apply (measurableSet_singleton _)] <;> simp

/-- `detKernel` disintegrates `detLaw`. -/
private instance detLaw_condKernel : detLaw.IsCondKernel detKernel where
  disintegrate := by
    rw [Measure.ext_iff_singleton]
    intro p
    obtain ⟨b1, b2⟩ := p
    cases b1 <;> cases b2 <;>
      rw [← Set.singleton_prod_singleton,
        Measure.compProd_apply_prod (measurableSet_singleton _)
          (measurableSet_singleton _), detFst] <;>
      simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac,
        smul_eq_mul] <;>
      simp [detLaw, detKernel]

/-- Bayes risk of the deterministic law via the explicit kernel: `0`. -/
private theorem detBayes_error :
    error detLaw (binaryBayesClassifier (kernelTrueProb detKernel)) = 0 := by
  rw [error_binaryBayesClassifier_eq_lintegral_min detLaw detKernel]
  rw [detFst, lintegral_dirac]
  have h1 : detKernel true {true} = 1 := by simp [detKernel]
  have h0 : detKernel true {false} = 0 := by simp [detKernel]
  rw [h1, h0, min_eq_right zero_le]

/-- Optimal error of the deterministic law over measurable classifiers: `0`. -/
private theorem detOptimal_error :
    optimalError detLaw {g : Bool → Bool | Measurable g} = 0 := by
  have hBayesK : Measurable (binaryBayesClassifier (kernelTrueProb detKernel)) :=
    measurable_binaryBayesClassifier (measurable_kernelTrueProb detKernel)
  have hle : error detLaw (binaryBayesClassifier (kernelTrueProb detLaw.condKernel))
      ≤ 0 := by
    have h := error_binaryBayesClassifier_condKernel_le detLaw _ hBayesK
    rwa [detBayes_error] at h
  have hcond : error detLaw (binaryBayesClassifier (kernelTrueProb detLaw.condKernel))
      = 0 :=
    le_antisymm hle zero_le
  rw [optimalError_measurable_eq_error_binaryBayesClassifier detLaw, hcond]

example : (kernelTrueProb noisyKernel true : ℝ) = 1 / 2 := by
  show (noisyKernel true {true}).toReal = 1 / 2
  rw [noisyKernel_true_true]
  norm_num

example : binaryBayesClassifier (kernelTrueProb noisyKernel) true = false := by
  have hval : (kernelTrueProb noisyKernel true : ℝ) = 1 / 2 := by
    show (noisyKernel true {true}).toReal = 1 / 2
    rw [noisyKernel_true_true]
    norm_num
  unfold binaryBayesClassifier
  rw [hval, ite_eq_right (by norm_num)]

example : Measurable (kernelTrueProb detKernel) :=
  measurable_kernelTrueProb detKernel

example : (kernelTrueProb detKernel true : ℝ) = 1 := by
  show (detKernel true {true}).toReal = 1
  have h1 : detKernel true {true} = 1 := by simp [detKernel]
  rw [h1, ENNReal.toReal_one]

example : (kernelTrueProb noisyKernel false : ℝ) = 0 := by
  show (noisyKernel false {true}).toReal = 0
  rw [noisyKernel_false_true, ENNReal.toReal_zero]

#print axioms measurable_kernelTrueProb
#print axioms error_binaryBayesClassifier_le
#print axioms error_binaryBayesClassifier_condKernel_le
#print axioms optimalError_measurable_eq_error_binaryBayesClassifier
#print axioms error_binaryBayesClassifier_eq_lintegral_min

end Cslib.MachineLearning.PACLearning
