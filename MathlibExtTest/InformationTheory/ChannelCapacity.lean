/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ChannelCapacity

import Mathlib.Tactic.NormNum

open scoped ENNReal
open InformationTheory

/-- Boundary check: at crossover `δ = 1 / 2` the output is
independent of the input, so the mutual information is
`1 - h (1/2) / log 2 = 0`, verified independently of the
production theorem's statement by simplifying the binary
entropy at `1 / 2`. -/
example : finiteMutualInformation
    (bscJoint (1 / 2 : ℝ≥0∞) (by norm_num) (PMF.uniformFintype (Fin 2))) = 0 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [bsc_finiteMutualInformation_uniform]
  simp [Real.binEntropy_two_inv, div_self hlog]

/-- Endpoint check: at crossover `δ = 0` the channel is the
identity, so the mutual information is one bit. -/
example : finiteMutualInformation
    (bscJoint (0 : ℝ≥0∞) (by norm_num) (PMF.uniformFintype (Fin 2))) = 1 := by
  rw [bsc_finiteMutualInformation_uniform]
  simp

/-- Endpoint check: at crossover `δ = 1` the channel flips every
bit, so the mutual information is again one bit. -/
example : finiteMutualInformation
    (bscJoint (1 : ℝ≥0∞) (by norm_num) (PMF.uniformFintype (Fin 2))) = 1 := by
  rw [bsc_finiteMutualInformation_uniform]
  simp

/-- Pointwise check: at crossover `δ = 1 / 2` every joint atom
has probability `1 / 4`. -/
example (x y : Fin 2) :
    ((bscJoint (1 / 2 : ℝ≥0∞) (by norm_num) (PMF.uniformFintype (Fin 2))) (x, y)).toReal =
      (1 / 4 : ℝ) := by
  rw [bscJoint_apply_uniform, ENNReal.toReal_mul]
  split_ifs <;> simp <;> norm_num

/-- Pointwise check: at crossover `δ = 0` off-diagonal atoms have
probability `0`. -/
example :
    (bscJoint (0 : ℝ≥0∞) (by norm_num) (PMF.uniformFintype (Fin 2))) (0, 1) =
      (0 : ℝ≥0∞) := by
  rw [bscJoint_apply_uniform]
  simp
