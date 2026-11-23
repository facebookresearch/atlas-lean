/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.ScaleNormalization
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.ScaleNormalization

example (b a : ℝ → ℝ)
    (h : MathlibExt.Biology.PopulationGenetics.Diffusion.IsRegularDiffusion b a) :
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2) (3 / 4) =
      MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (3 / 4) -
        MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (1 / 2) := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
    (1 / 2) (3 / 4) hc hp

example (b a : ℝ → ℝ)
    (h : MathlibExt.Biology.PopulationGenetics.Diffusion.IsRegularDiffusion b a)
    (v34 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (3 / 4) =
      3 / 4)
    (v12 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (1 / 2) =
      1 / 2) :
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2) (3 / 4) =
      1 / 4 := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have e :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) (3 / 4) hc hp
  rw [e, v34, v12]
  norm_num

example (b a : ℝ → ℝ)
    (h : MathlibExt.Biology.PopulationGenetics.Diffusion.IsRegularDiffusion b a)
    (v0 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a 0 = 0)
    (v12 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (1 / 2) =
      1 / 2)
    (v1 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a 1 = 1) :
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb b a (1 / 2) = 1 / 2 := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_eq_ratio_scaleFunctionFrom
      b a h (1 / 2) (1 / 2) hc hc
  have s12 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) (1 / 2) hc hc
  have s0 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) 0 hc h0
  have s1 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) 1 hc h1
  rw [e, s12, s0, s1, v0, v12, v1]
  norm_num

example (b a : ℝ → ℝ)
    (h : MathlibExt.Biology.PopulationGenetics.Diffusion.IsRegularDiffusion b a)
    (v0 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a 0 = 0)
    (v12 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (1 / 2) =
      1 / 2)
    (v1 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a 1 = 1) :
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb b a 0 = 0 := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_eq_ratio_scaleFunctionFrom
      b a h (1 / 2) 0 hc h0
  have s0 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) 0 hc h0
  have s1 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) 1 hc h1
  rw [e, s0, s1, v0, v12, v1]
  norm_num

example (b a : ℝ → ℝ)
    (h : MathlibExt.Biology.PopulationGenetics.Diffusion.IsRegularDiffusion b a)
    (v0 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a 0 = 0)
    (v12 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a (1 / 2) =
      1 / 2)
    (v1 : MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunction b a 1 = 1) :
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb b a 1 = 1 := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_eq_ratio_scaleFunctionFrom
      b a h (1 / 2) 1 hc h1
  have s0 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) 0 hc h0
  have s1 :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub b a h
      (1 / 2) 1 hc h1
  rw [e, s0, s1, v0, v12, v1]
  norm_num

example (b a : ℝ → ℝ)
    (h : MathlibExt.Biology.PopulationGenetics.Diffusion.IsRegularDiffusion b a) :
    MathlibExt.Biology.PopulationGenetics.Diffusion.greenFunction b a (1 / 4) (3 / 4) =
      2 * (MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2)
        (min (1 / 4) (3 / 4)) -
        MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2) 0) *
        (MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2) 1 -
        MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2)
          (max (1 / 4) (3 / 4))) /
        ((MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2) 1 -
        MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom b a (1 / 2) 0) *
        a (3 / 4) *
        MathlibExt.Biology.PopulationGenetics.Diffusion.scaleDensity b a (3 / 4)) := by
  have hc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hx : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact MathlibExt.Biology.PopulationGenetics.Diffusion.greenFunction_eq_scaleFunctionFrom
    b a h (1 / 2) (1 / 4) (3 / 4) hc hp hx

#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.scaleFunctionFrom_eq_sub
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_eq_ratio_scaleFunctionFrom
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.greenFunction_eq_scaleFunctionFrom

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.ScaleNormalization
