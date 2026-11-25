/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.ProbabilisticTreeDepth
public import MathlibExt.Probability.BranchingProcess.Binary

/-!
# Eventual termination of the random binary tree

Eventual termination is the increasing union of the bounded-depth
termination events. Its probability is the least fixed point of the
binary offspring generating function: it is `1` exactly when
`p ≤ 1/2`, and `(1 - p) / p` when `p > 1/2`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Cslib.Language

open MathlibExt.Probability

/-- The event that the random binary tree read off `ω` terminates, that is, terminates
within some finite depth. Its complement is the event of an infinite derivation. -/
def eventualTermination : Set BinaryTreeAddressLaw.Ω :=
  ⋃ h, terminationByDepth h

theorem terminationByDepth_subset_eventualTermination (h : ℕ) :
    terminationByDepth h ⊆ eventualTermination :=
  fun _ hx => Set.mem_iUnion.mpr ⟨h, hx⟩

theorem measurableSet_eventualTermination : MeasurableSet eventualTermination :=
  MeasurableSet.iUnion measurableSet_terminationByDepth

/-- Continuity from below: the probability of terminating within depth `h` increases to
the probability of eventual termination. -/
theorem tendsto_law_terminationByDepth {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Tendsto (fun h => BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h)) atTop
      (𝓝 (BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination)) := by
  show Tendsto (fun h => BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h)) atTop
    (𝓝 (BinaryTreeAddressLaw.law p hp0 hp1 (⋃ h, terminationByDepth h)))
  exact tendsto_measure_iUnion_atTop monotone_terminationByDepth

theorem law_eventualTermination_eq_iSup {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination =
      ⨆ h, BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h) := by
  have hmono : Monotone (fun h => BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h)) :=
    fun _ _ hij => measure_mono (monotone_terminationByDepth hij)
  exact tendsto_nhds_unique (tendsto_law_terminationByDepth hp0 hp1) (tendsto_atTop_iSup hmono)

/-- The cutoff mass of the trees of depth at most `h` is the `h`-th iterate at `0` of the
generating function `s ↦ 1 - p + p * s ^ 2` of the binary offspring law. -/
theorem cgTotal_eq_iterate_pgf_binaryOffspring {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : ℕ) :
    cgTotal p (1 - p) h = (pgf id (GaltonWatson.binaryOffspring p))^[h] 0 := by
  induction h with
  | zero =>
    show cgTotal p (1 - p) 0 = 0
    simp [cgTotal, cgTrees]
  | succ h ih =>
    rw [cgTotal_succ, Function.iterate_succ_apply',
      GaltonWatson.pgf_binaryOffspring hp0 hp1, ih]

/-- Terminating within depth `h` has the probability that generation `h` of the
Galton-Watson process with binary offspring law is empty. -/
theorem law_terminationByDepth_eq_law_real_zero {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : ℕ) :
    BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h) =
      ENNReal.ofReal ((GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0}) := by
  rw [law_terminationByDepth, cgTotal_eq_iterate_pgf_binaryOffspring hp0 hp1 h,
    GaltonWatson.law_binaryOffspring_real_zero hp0 hp1 h]

/-- The probability of eventual termination is the extinction probability of the
Galton-Watson process with binary offspring law. -/
theorem law_eventualTermination {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination =
      ENNReal.ofReal (GaltonWatson.extinctionProb (GaltonWatson.binaryOffspring p)) := by
  haveI := GaltonWatson.binaryOffspring_isProbabilityMeasure hp0 hp1
  have h2 : Tendsto
      (fun h => ENNReal.ofReal ((GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0}))
      atTop
      (𝓝 (ENNReal.ofReal (GaltonWatson.extinctionProb (GaltonWatson.binaryOffspring p)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (GaltonWatson.tendsto_law_real_zero (GaltonWatson.binaryOffspring p))
  have hfun : (fun h => ENNReal.ofReal ((GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0}))
      = (fun h => BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h)) :=
    funext fun h => (law_terminationByDepth_eq_law_real_zero hp0 hp1 h).symm
  rw [hfun] at h2
  exact tendsto_nhds_unique (tendsto_law_terminationByDepth hp0 hp1) h2

/-- The probability of eventual termination is the least root in `[0, 1]` of
`s = 1 - p + p * s ^ 2`. -/
theorem isLeast_law_eventualTermination {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsLeast {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - p + p * s ^ 2}
      (BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination).toReal := by
  have hL := GaltonWatson.isLeast_extinctionProb_binaryOffspring' hp0 hp1
  rw [law_eventualTermination hp0 hp1, ENNReal.toReal_ofReal hL.1.1.1]
  exact hL

/-- The cutoff sums of Chi and Geman converge to the probability of eventual
termination. -/
theorem tendsto_chiGemanS_law_eventualTermination {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Tendsto (chiGemanS p (1 - p)) atTop
      (𝓝 (BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination).toReal) := by
  have hlink : ∀ h, chiGemanS p (1 - p) (h + 1) =
      (GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0} := by
    intro h
    rw [chiGemanS_link, cgTotal_eq_iterate_pgf_binaryOffspring hp0 hp1 h,
      GaltonWatson.law_binaryOffspring_real_zero hp0 hp1 h]
  have hfun : (fun h => chiGemanS p (1 - p) (h + 1))
      = (fun h => (GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0}) :=
    funext hlink
  haveI := GaltonWatson.binaryOffspring_isProbabilityMeasure hp0 hp1
  have htail : Tendsto (fun h => chiGemanS p (1 - p) (h + 1)) atTop
      (𝓝 (⨆ h, (GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0})) := by
    rw [hfun]
    simpa [GaltonWatson.extinctionProb] using GaltonWatson.tendsto_law_real_zero (GaltonWatson.binaryOffspring p)
  have hfull := (tendsto_add_atTop_iff_nat (f := chiGemanS p (1 - p)) 1).mp htail
  have hL := GaltonWatson.isLeast_extinctionProb_binaryOffspring' hp0 hp1
  have hR : (BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination).toReal =
      ⨆ h, (GaltonWatson.law (GaltonWatson.binaryOffspring p) h).real {0} :=
    (congrArg ENNReal.toReal (law_eventualTermination hp0 hp1)).trans
      (ENNReal.toReal_ofReal hL.1.1.1)
  rw [hR]
  exact hfull

/-- Termination is almost sure exactly in the subcritical and critical regime. -/
theorem law_eventualTermination_eq_one_iff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination = 1 ↔ p ≤ 1 / 2 := by
  have hL := GaltonWatson.isLeast_extinctionProb_binaryOffspring' hp0 hp1
  rw [law_eventualTermination hp0 hp1, ← ENNReal.ofReal_one,
    ENNReal.ofReal_eq_ofReal_iff hL.1.1.1 zero_le_one,
    GaltonWatson.extinctionProb_binaryOffspring_eq_one_iff hp0 hp1]

theorem law_eventualTermination_of_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p ≤ 1 / 2) :
    BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination = 1 :=
  (law_eventualTermination_eq_one_iff hp0 hp1).2 hp

/-- Supercritical regime: the probability of eventual termination is the smaller root
`(1 - p) / p`. -/
theorem law_eventualTermination_of_gt {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination =
      ENNReal.ofReal ((1 - p) / p) := by
  rw [law_eventualTermination hp0 hp1,
    GaltonWatson.extinctionProb_binaryOffspring_of_gt hp0 hp1 hp]

/-- Supercritical regime: an infinite derivation has probability `(2 * p - 1) / p`. -/
theorem law_compl_eventualTermination_of_gt {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    BinaryTreeAddressLaw.law p hp0 hp1 eventualTerminationᶜ =
      ENNReal.ofReal ((2 * p - 1) / p) := by
  have hprob := BinaryTreeAddressLaw.law_isProbabilityMeasure hp0 hp1
  have hE := law_eventualTermination_of_gt hp0 hp1 hp
  have hfin : BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination ≠ ⊤ := by
    rw [hE]
    exact ENNReal.ofReal_ne_top
  have hq : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (by linarith)
  rw [measure_compl measurableSet_eventualTermination hfin, @measure_univ _ _ _ hprob, hE,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq]
  congr 1
  have hpne : p ≠ 0 := by linarith
  field_simp
  ring

/-- At `p = 2 / 3` the derivation terminates with probability `1 / 2` and is infinite
with probability `1 / 2`. -/
theorem law_eventualTermination_two_thirds :
    BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTermination =
        ENNReal.ofReal (1 / 2) ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) eventualTerminationᶜ =
        ENNReal.ofReal (1 / 2) := by
  have hE := law_eventualTermination_of_gt (p := 2 / 3) (by norm_num) (by norm_num)
    (by norm_num)
  have hC := law_compl_eventualTermination_of_gt (p := 2 / 3) (by norm_num) (by norm_num)
    (by norm_num)
  have e1 : ((1 : ℝ) - 2 / 3) / (2 / 3) = 1 / 2 := by norm_num
  have e2 : ((2 : ℝ) * (2 / 3) - 1) / (2 / 3) = 1 / 2 := by norm_num
  rw [e1] at hE
  rw [e2] at hC
  exact ⟨hE, hC⟩

/-- Eventual termination of the binary grammar `A → A A | a`, with branch probability `p`
at every address: it is a measurable event; the probabilities of terminating within
depth `h` increase to its probability; that probability is the Galton-Watson extinction
probability of the binary offspring law and the least root in `[0, 1]` of
`s = 1 - p + p * s ^ 2`; it is `1` for `p ≤ 1 / 2` and `(1 - p) / p` for `p > 1 / 2`. -/
theorem binaryGrammar_eventualTermination {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MeasurableSet eventualTermination ∧
      Tendsto (fun h => BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h)) atTop
        (𝓝 (BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination)) ∧
      BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination =
        ENNReal.ofReal (GaltonWatson.extinctionProb (GaltonWatson.binaryOffspring p)) ∧
      IsLeast {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s = 1 - p + p * s ^ 2}
        (BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination).toReal ∧
      (p ≤ 1 / 2 → BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination = 1) ∧
      (1 / 2 < p → BinaryTreeAddressLaw.law p hp0 hp1 eventualTermination =
        ENNReal.ofReal ((1 - p) / p)) :=
  ⟨measurableSet_eventualTermination, tendsto_law_terminationByDepth hp0 hp1,
    law_eventualTermination hp0 hp1, isLeast_law_eventualTermination hp0 hp1,
    fun hp => law_eventualTermination_of_le hp0 hp1 hp,
    fun hp => law_eventualTermination_of_gt hp0 hp1 hp⟩


end Cslib.Language
