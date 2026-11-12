/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! # Binary symmetric channel capacity computation

For the binary symmetric channel with crossover `δ` and uniform
input, the input-output mutual information is `log 2 - h δ`,
where `h` is the binary entropy function. This is the BSC case
of roadmap package QCI-34 of the Atlas TCS canon roadmap.
`mutualInfo` agrees with
`MathlibExt/InformationTheory/MutualInformation.lean`.

Source: Cover and Thomas, Elements of Information Theory (2006),
Section 7.1.
-/

open Finset
open scoped ENNReal

/-- Binary entropy function (nats): `h p = -p log p - (1-p)
log (1-p)` with the usual continuous conventions at the endpoints
(real arithmetic: `0 * log 0 = 0`). -/
noncomputable def binEntropy (p : ℝ) : ℝ :=
  -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- Mutual information (nats) of a joint PMF on a finite product
type. -/
noncomputable def mutualInfo {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : ℝ :=
  ∑ x, ∑ y, (p (x, y)).toReal *
    Real.log ((p (x, y)).toReal /
      ((∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal)))

/-- The uniform PMF on `Fin 2`. -/
noncomputable def uniformFin2 : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (1 / 2 : ℝ≥0∞)) (by
    simp [Finset.sum_const, ENNReal.mul_inv_cancel])

/-- The joint law of input and output of the binary symmetric
channel with crossover probability `δ ≤ 1` under input PMF `p`. -/
noncomputable def bscJoint (δ : ℝ≥0∞) (hδ : δ ≤ 1) (p : PMF (Fin 2)) :
    PMF (Fin 2 × Fin 2) :=
  p.bind fun x => (PMF.ofFintype
    (fun y => if y = x then 1 - δ else δ) (by
      fin_cases x <;> simp [Finset.sum] <;>
        (first | exact tsub_add_cancel_of_le hδ |
          rw [add_comm]; exact tsub_add_cancel_of_le hδ))).map fun y => (x, y)

private theorem joint_val {δ : ℝ≥0∞} (hδ : δ ≤ 1) (x y : Fin 2) :
    (bscJoint δ hδ uniformFin2) (x, y) = (1/2) * (if y = x then 1 - δ else δ) := by
  simp only [bscJoint, PMF.bind_apply, PMF.map_apply, PMF.ofFintype_apply, uniformFin2,
    PMF.ofFintype_apply]
  rw [tsum_fintype, Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;> simp [tsum_fintype]

private theorem toReal_sub_one {δ : ℝ≥0∞} (hδ : δ ≤ 1) :
    (1 - δ).toReal = 1 - δ.toReal := by
  rw [ENNReal.toReal_sub_of_le hδ ENNReal.one_ne_top, ENNReal.toReal_one]

private theorem joint_toReal {δ : ℝ≥0∞} (hδ : δ ≤ 1) (x y : Fin 2) :
    ((bscJoint δ hδ uniformFin2) (x, y)).toReal =
      (1/2 : ℝ) * (if y = x then 1 - δ.toReal else δ.toReal) := by
  rw [joint_val hδ x y, ENNReal.toReal_mul]
  have hhalf : ((1 / 2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by simp
  rw [hhalf, apply_ite ENNReal.toReal, toReal_sub_one hδ]

private theorem margX {δ : ℝ≥0∞} (hδ : δ ≤ 1) (x : Fin 2) :
    (∑ y, ((bscJoint δ hδ uniformFin2) (x, y)).toReal) = 1/2 := by
  rw [Fin.sum_univ_two]
  rw [joint_toReal hδ x 0, joint_toReal hδ x 1]
  fin_cases x <;> simp <;> ring

private theorem margY {δ : ℝ≥0∞} (hδ : δ ≤ 1) (y : Fin 2) :
    (∑ x, ((bscJoint δ hδ uniformFin2) (x, y)).toReal) = 1/2 := by
  rw [Fin.sum_univ_two]
  rw [joint_toReal hδ 0 y, joint_toReal hδ 1 y]
  fin_cases y <;> simp <;> ring

/-- Binary symmetric channel with uniform input: the mutual
information between input and output is `log 2 - h δ`. -/
theorem bsc_mutualInfo_uniform {δ : ℝ≥0∞} (hδ : δ ≤ 1) :
    mutualInfo (bscJoint δ hδ uniformFin2) =
      Real.log 2 - binEntropy δ.toReal := by
  unfold mutualInfo
  simp only [margX hδ, margY hδ]
  simp only [Fin.sum_univ_two]
  rw [joint_toReal hδ 0 0, joint_toReal hδ 0 1, joint_toReal hδ 1 0, joint_toReal hδ 1 1]
  simp only [show (1 : Fin 2) ≠ 0 from by decide, show (0 : Fin 2) ≠ 1 from by decide,
    ite_true, ite_false]
  have hA1 : (1/2 : ℝ) * (1 - δ.toReal) / ((1/2 : ℝ) * (1/2 : ℝ)) = 2 * (1 - δ.toReal) := by
    ring
  have hA2 : (1/2 : ℝ) * δ.toReal / ((1/2 : ℝ) * (1/2 : ℝ)) = 2 * δ.toReal := by ring
  rw [hA1, hA2]
  by_cases hd0 : δ.toReal = 0
  · rw [hd0]
    unfold binEntropy
    simp
    ring
  · by_cases hd1 : δ.toReal = 1
    · rw [hd1]
      unfold binEntropy
      simp
      ring
    · have h1d : (1 : ℝ) - δ.toReal ≠ 0 := sub_ne_zero.mpr (Ne.symm hd1)
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      rw [Real.log_mul h2 h1d, Real.log_mul h2 hd0]
      unfold binEntropy
      ring
