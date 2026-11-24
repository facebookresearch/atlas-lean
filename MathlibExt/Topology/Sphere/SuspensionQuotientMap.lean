/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Sphere.StandardCover

/-!
# The sphere suspension map

Defines the continuous map from a unit sphere times the unit interval to the
next-dimensional unit sphere using a scaled horizontal coordinate and height
`2t - 1`. Proves that the two interval ends are sent to the south and north
poles, respectively.
-/

public section

open Metric

noncomputable section

namespace AlgebraicTopology

@[expose] def sphereSuspensionVector (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin ((m + 1) + 1)) :=
  EuclideanSpace.finAddEquivProd.symm
    ((2 * Real.sqrt (t * (1 - t))) • x,
      WithLp.toLp 2 (fun _ : Fin 1 => 2 * t - 1))

private theorem norm_sphereSuspensionVector_sq (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    ‖sphereSuspensionVector m x t‖ ^ 2 =
      ‖(2 * Real.sqrt (t * (1 - t))) • x‖ ^ 2 + |2 * t - 1| ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  let g : Fin (m + 1) ⊕ Fin 1 → ℝ := fun z =>
    (Sum.rec
      ((2 * Real.sqrt (t * (1 - t))) • x.ofLp)
      (fun _ => 2 * t - 1) z) ^ 2
  have hsum :
      (∑ i, g ((finSumFinEquiv (m := m + 1) (n := 1)).symm i)) =
        ‖(2 * Real.sqrt (t * (1 - t))) • x‖ ^ 2 + (2 * t - 1) ^ 2 := by
    rw [(finSumFinEquiv (m := m + 1) (n := 1)).symm.sum_comp]
    simp only [g, Fintype.sum_sum_type, Fintype.sum_unique]
    apply congrArg (fun z : ℝ => z + (2 * t - 1) ^ 2)
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  simpa [sphereSuspensionVector, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, PiLp.norm_sq_eq_of_L2] using hsum

theorem sphereSuspensionVector_mem_sphere (m : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (t : unitInterval) :
    sphereSuspensionVector m x.1 t.1 ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 := by
  have ht : 0 ≤ t.1 * (1 - t.1) :=
    mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2)
  have hx : ‖x.1‖ = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h
  have hsq : ‖sphereSuspensionVector m x.1 t.1‖ ^ 2 = 1 := by
    rw [norm_sphereSuspensionVector_sq]
    rw [norm_smul, Real.norm_eq_abs, hx, mul_one]
    rw [sq_abs, sq_abs]
    rw [show (2 * Real.sqrt (t.1 * (1 - t.1))) ^ 2 =
      4 * Real.sqrt (t.1 * (1 - t.1)) ^ 2 by ring]
    rw [Real.sq_sqrt ht]
    ring
  rw [Metric.mem_sphere, dist_zero_right]
  nlinarith [norm_nonneg (sphereSuspensionVector m x.1 t.1)]

/-- The standard quotient presentation of `S^(m+1)` by the cylinder `S^m × I`. -/
@[expose] noncomputable def sphereSuspensionQuotientMap (m : ℕ) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × unitInterval,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) where
  toFun p := ⟨EuclideanSpace.finAddEquivProd.symm
      ((2 * Real.sqrt (p.2.1 * (1 - p.2.1))) • p.1.1,
        WithLp.toLp 2 (fun _ : Fin 1 => 2 * p.2.1 - 1)),
    sphereSuspensionVector_mem_sphere m p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun p :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × unitInterval =>
      EuclideanSpace.finAddEquivProd.symm
        ((2 * Real.sqrt (p.2.1 * (1 - p.2.1))) • p.1.1,
          WithLp.toLp 2 (fun _ : Fin 1 => 2 * p.2.1 - 1)))
    fun_prop

@[simp] theorem sphereSuspensionQuotientMap_zero (m : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    sphereSuspensionQuotientMap m (x, (0 : unitInterval)) = southPt (m + 1) := by
  apply Subtype.ext
  apply EuclideanSpace.finAddEquivProd.injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    simp [sphereSuspensionQuotientMap, southPt,
      EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  · apply PiLp.ext
    intro i
    fin_cases i
    norm_num [sphereSuspensionQuotientMap, southPt, EuclideanSpace.finAddEquivProd,
      EuclideanSpace.sumEquivProd]

@[simp] theorem sphereSuspensionQuotientMap_one (m : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    sphereSuspensionQuotientMap m (x, (1 : unitInterval)) = northPt (m + 1) := by
  apply Subtype.ext
  apply EuclideanSpace.finAddEquivProd.injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    simp [sphereSuspensionQuotientMap, northPt,
      EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  · apply PiLp.ext
    intro i
    fin_cases i
    norm_num [sphereSuspensionQuotientMap, northPt, EuclideanSpace.finAddEquivProd,
      EuclideanSpace.sumEquivProd]

end AlgebraicTopology
