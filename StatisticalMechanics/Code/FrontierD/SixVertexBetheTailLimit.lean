/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailSelectedDensity
import Mathlib.Topology.ContinuousMap.Ordered





namespace StatMech.FrontierD

noncomputable section

open Filter Topology

def sixVertexSelectedWeightedDensityMap
    {c : Real} (hc : 2 < c) (k : Nat) :
    C(Set.Icc (-Real.pi) Real.pi, Real) where
  toFun x := sixVertexRootDensityWeight c x *
    sixVertexSelectedFiniteRootDensity hc k x
  continuous_toFun := by
    apply Continuous.mul
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · exact (continuous_sixVertexFiniteRootDensity hc
        (sixVertexFourWidth 0 k) _ _).comp continuous_subtype_val

theorem sixVertexTailConvolutionError_fourWidth_pos
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k : Nat) :
    0 < sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) := by
  unfold sixVertexTailConvolutionError
  have hK := sixVertexRootDensityKernelLipschitzBound_pos hc
  have hfloor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hB : 0 < sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  positivity

theorem cauchySeq_sixVertexSelectedWeightedDensityMap
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    CauchySeq (sixVertexSelectedWeightedDensityMap hc) := by
  apply Metric.cauchySeq_iff.2
  intro eps heps
  let rate := sixVertexRootDensityContractionRate c
  let D := (2 * Real.pi) * (1 - rate)
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hD : 0 < D := by
    dsimp [D, rate]
    exact mul_pos (by positivity) (sub_pos.mpr hrate.2)
  have herror := sixVertexTailConvolutionError_fourWidth_tendsto_zero hc htail
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 herror)
    (eps * D / 4) (by positivity)
  refine ⟨K, ?_⟩
  intro m hm n hn
  have hemDist := hK m hm
  have henDist := hK n hn
  have hem : sixVertexTailConvolutionError c (sixVertexFourWidth 0 m) <
      eps * D / 4 := by
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (sixVertexTailConvolutionError_fourWidth_pos hc htail m)] at hemDist
    exact hemDist
  have hen : sixVertexTailConvolutionError c (sixVertexFourWidth 0 n) <
      eps * D / 4 := by
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (sixVertexTailConvolutionError_fourWidth_pos hc htail n)] at henDist
    exact henDist
  let B := ((sixVertexTailConvolutionError c (sixVertexFourWidth 0 m) +
      sixVertexTailConvolutionError c (sixVertexFourWidth 0 n)) /
        (2 * Real.pi)) / (1 - rate)
  have hB : 0 <= B := by
    dsimp [B, rate]
    exact div_nonneg
      (div_nonneg (add_nonneg
        (sixVertexTailConvolutionError_fourWidth_pos hc htail m).le
        (sixVertexTailConvolutionError_fourWidth_pos hc htail n).le)
        (by positivity))
      (sub_nonneg.mpr hrate.2.le)
  have hdist : dist (sixVertexSelectedWeightedDensityMap hc m)
      (sixVertexSelectedWeightedDensityMap hc n) <= B := by
    apply (ContinuousMap.dist_le hB).2
    intro x
    rw [Real.dist_eq]
    change |sixVertexRootDensityWeight c x *
        sixVertexSelectedFiniteRootDensity hc m x -
      sixVertexRootDensityWeight c x *
        sixVertexSelectedFiniteRootDensity hc n x| <= B
    rw [← mul_sub]
    exact sixVertexSelectedFiniteRootDensity_weighted_cauchy_tail
      hc htail m n x x.property
  calc
    dist (sixVertexSelectedWeightedDensityMap hc m)
        (sixVertexSelectedWeightedDensityMap hc n) <= B := hdist
    _ < eps := by
      dsimp [B, D, rate] at *
      rw [div_div, div_lt_iff₀ (mul_pos (by positivity : 0 < 2 * Real.pi)
        (by linarith [hrate.2] : 0 < 1 - sixVertexRootDensityContractionRate c))]
      nlinarith

def sixVertexTailWeightedDensityLimitMap
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    C(Set.Icc (-Real.pi) Real.pi, Real) :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (cauchySeq_sixVertexSelectedWeightedDensityMap hc htail))

theorem tendsto_sixVertexSelectedWeightedDensityMap
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Tendsto (sixVertexSelectedWeightedDensityMap hc) atTop
      (nhds (sixVertexTailWeightedDensityLimitMap hc htail)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (cauchySeq_sixVertexSelectedWeightedDensityMap hc htail))

def sixVertexTailWeightedDensityLimit
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) : Real → Real :=
  sixVertexTailWeightedDensityLimitMap hc htail |>.IccExtend
    (by linarith [Real.pi_pos])

def sixVertexTailRootDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (x : Real) : Real :=
  sixVertexTailWeightedDensityLimit hc htail x /
    sixVertexRootDensityWeight c x

theorem continuous_sixVertexTailRootDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Continuous (sixVertexTailRootDensity hc htail) := by
  apply Continuous.div
  · exact (sixVertexTailWeightedDensityLimitMap hc htail |>.IccExtend
      (by linarith [Real.pi_pos])).continuous
  · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  · intro x
    exact (sixVertexRootDensityWeight_pos hc x).ne'

theorem sixVertexRootDensityWeight_mul_tailRootDensity_of_mem
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRootDensityWeight c x * sixVertexTailRootDensity hc htail x =
      sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
  have hlimit : sixVertexTailWeightedDensityLimit hc htail x =
      sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
    unfold sixVertexTailWeightedDensityLimit
    rw [ContinuousMap.coe_IccExtend,
      Set.IccExtend_of_mem (by linarith [Real.pi_pos]) _ hx]
  rw [sixVertexTailRootDensity, hlimit]
  field_simp [(sixVertexRootDensityWeight_pos hc x).ne']

theorem tendsto_sixVertexSelectedWeightedDensity_at
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    Tendsto (fun k => sixVertexRootDensityWeight c x *
        sixVertexSelectedFiniteRootDensity hc k x) atTop
      (nhds (sixVertexRootDensityWeight c x *
        sixVertexTailRootDensity hc htail x)) := by
  have heval := (continuous_eval_const (⟨x, hx⟩ :
      Set.Icc (-Real.pi) Real.pi)).tendsto
    (sixVertexTailWeightedDensityLimitMap hc htail)
  have h := heval.comp
    (tendsto_sixVertexSelectedWeightedDensityMap hc htail)
  have htarget : sixVertexRootDensityWeight c x *
      sixVertexTailRootDensity hc htail x =
        sixVertexTailWeightedDensityLimitMap hc htail ⟨x, hx⟩ := by
    exact sixVertexRootDensityWeight_mul_tailRootDensity_of_mem hc htail hx
  rw [htarget]
  simpa [Function.comp_def, sixVertexSelectedWeightedDensityMap] using h

end

end StatMech.FrontierD
