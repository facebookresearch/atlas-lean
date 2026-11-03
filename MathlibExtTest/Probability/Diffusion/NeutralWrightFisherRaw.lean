/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw

/-!
# Compile checks for the raw neutral Wright--Fisher realization

The public objects below pin a concrete probability measure, an exactly
normalized raw process, its fourth-moment Kolmogorov bound, and an all-sample
continuous modification in `[0,1]`.
-/

namespace MathlibExtTest.Probability.Diffusion.NeutralWrightFisherRaw

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw

example (x : I) :
    IsKolmogorovProcess (rawProcess x) (rawMeasure x) 4 2
      kolmogorovConstant :=
  isKolmogorovProcess_rawProcess x

example : (kolmogorovConstant : ℝ) = 3 / 16 := by
  change (((3 : NNReal) / (16 : NNReal) : NNReal) : ℝ) = (3 : ℝ) / 16
  norm_num

example : neutralKernel 0 = (Kernel.id : Kernel I I) :=
  neutralKernel_zero

example (s t : NNReal) :
    neutralKernel (s + t) = neutralKernel t ∘ₖ neutralKernel s :=
  neutralKernel_add s t

example (x : I) (t : NNReal) :
    (rawMeasure x).map (fun ω => ω t) = neutralKernel t x :=
  map_eval_rawMeasure x t

example (x : I) {s t : NNReal} (hst : s < t) :
    (rawMeasure x).map (fun ω => (ω s, ω t)) =
      (neutralKernel s x) ⊗ₘ neutralKernel (t - s) :=
  map_pair_rawMeasure_of_lt x hst

example (x : I) :
    (rawMeasure x).map (fun ω => ω 0) = Measure.dirac x :=
  map_eval_zero_rawMeasure x

example (x : I) (ω : SamplePath) : rawProcess x 0 ω = x :=
  rawProcess_zero x ω

example (x : I) (t : NNReal) :
    ∫⁻ ω, edist (rawProcess x t ω) (rawProcess x t ω) ^ (4 : ℝ)
      ∂rawMeasure x = 0 := by
  simp

example (x : I) (J : Finset NNReal) :
    (rawMeasure x).map
        (fun ω => J.restrict (fun t => modifiedProcess x t ω)) =
      (rawMeasure x).map
        (fun ω => J.restrict (fun t => rawProcess x t ω)) :=
  map_restrict_modified_eq_raw x J

example (x : I) (J : Finset NNReal) :
    (rawMeasure x).map
        (fun ω => J.restrict (fun t => modifiedProcess x t ω)) =
      (rawMeasure x).map
        (fun ω => J.restrict (fun t => ((ω t : I) : ℝ))) :=
  map_restrict_modified_eq_coordinate x J

example (x : I) (ω : SamplePath) : modifiedProcess x 0 ω = x :=
  modifiedProcess_zero x ω

example (x : I) (t : NNReal) (ω : SamplePath) :
    modifiedProcess x t ω ∈ Set.Icc (0 : ℝ) 1 :=
  modifiedProcess_mem_Icc x t ω

example (x : I) (ω : SamplePath) :
    Continuous fun t => modifiedProcess x t ω :=
  continuous_modifiedProcess x ω

noncomputable example (x : I) : ContinuousRealization x :=
  continuousRealization x

/-- The concrete interior initial frequency. -/
noncomputable def xHalf : I := ⟨1 / 2, by constructor <;> norm_num⟩

noncomputable def modifiedState (x : I) (t : NNReal) (ω : SamplePath) : I :=
  ⟨modifiedProcess x t ω, modifiedProcess_mem_Icc x t ω⟩

/-- The actual constructed modified process has the transition marginal at
positive time; no process is supplied by the caller. -/
example :
    (rawMeasure xHalf).map (modifiedState xHalf 1) =
      neutralKernel 1 xHalf := by
  calc
    (rawMeasure xHalf).map (modifiedState xHalf 1) =
        (rawMeasure xHalf).map (fun ω => ω 1) := by
      apply Measure.map_congr
      filter_upwards [modifiedProcess_ae_eq_raw xHalf 1,
        rawProcess_ae_eq_coordinate xHalf 1] with ω hmod hraw
      apply Subtype.ext
      exact hmod.trans hraw
    _ = neutralKernel 1 xHalf := map_eval_rawMeasure xHalf 1

#print axioms isKolmogorovProcess_rawProcess
#print axioms continuousRealization

end MathlibExtTest.Probability.Diffusion.NeutralWrightFisherRaw
