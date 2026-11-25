/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Sphere.SuspensionQuotientMap

/-!
# The quotient map for sphere suspension

The sphere suspension map has equal values precisely when the interval
coordinates agree and either the coordinate is an endpoint or the sphere
coordinates agree. Together with surjectivity and continuity, the fiber
calculation identifies the map from a sphere times the unit interval as a
topological quotient map.
-/

public section

open Metric

noncomputable section

namespace AlgebraicTopology

private theorem norm_sq_eq_finAdd (m : ℕ)
    (z : EuclideanSpace ℝ (Fin ((m + 1) + 1))) :
    ‖z‖ ^ 2 = ‖(EuclideanSpace.finAddEquivProd z).1‖ ^ 2 +
      |(EuclideanSpace.finAddEquivProd z).2 (0 : Fin 1)| ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_add]
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    PiLp.norm_sq_eq_of_L2]

theorem sphereSuspensionQuotientMap_eq (m : ℕ)
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × unitInterval)
    (h : sphereSuspensionQuotientMap m p = sphereSuspensionQuotientMap m q) :
    p.2 = q.2 ∧ (p.2 = 0 ∨ p.2 = 1 ∨ p.1 = q.1) := by
  have hlast : 2 * p.2.1 - 1 = 2 * q.2.1 - 1 := by
    have h' := congrArg
      (fun z => (EuclideanSpace.finAddEquivProd z.1).2 (0 : Fin 1)) h
    simpa [sphereSuspensionQuotientMap] using h'
  have htval : p.2.1 = q.2.1 := by linarith
  have ht : p.2 = q.2 := Subtype.ext htval
  refine ⟨ht, ?_⟩
  rcases eq_or_ne p.2 (0 : unitInterval) with hp0 | hp0
  · exact Or.inl hp0
  rcases eq_or_ne p.2 (1 : unitInterval) with hp1 | hp1
  · exact Or.inr (Or.inl hp1)
  · right
    right
    have htpos : 0 < p.2.1 := lt_of_le_of_ne p.2.2.1 (by
      intro hz
      apply hp0
      apply Subtype.ext
      exact hz.symm)
    have htlt : p.2.1 < 1 := lt_of_le_of_ne p.2.2.2 (by
      intro h1
      apply hp1
      apply Subtype.ext
      exact h1)
    have hrad : 0 < p.2.1 * (1 - p.2.1) :=
      mul_pos htpos (sub_pos.mpr htlt)
    have hscale : 2 * Real.sqrt (p.2.1 * (1 - p.2.1)) ≠ 0 := by positivity
    have hfirst := congrArg
      (fun z => (EuclideanSpace.finAddEquivProd z.1).1) h
    have hsmul :
        (2 * Real.sqrt (p.2.1 * (1 - p.2.1))) • p.1.1 =
          (2 * Real.sqrt (p.2.1 * (1 - p.2.1))) • q.1.1 := by
      have hfirst' :
          (fun i => 2 * Real.sqrt (p.2.1 * (1 - p.2.1)) * p.1.1.ofLp i) =
            (fun i => 2 * Real.sqrt (q.2.1 * (1 - q.2.1)) * q.1.1.ofLp i) := by
        simpa [sphereSuspensionQuotientMap] using hfirst
      rw [← ht] at hfirst'
      apply PiLp.ext
      exact congrFun hfirst'
    apply Subtype.ext
    exact smul_right_injective _ hscale hsmul

private theorem sphereSuspensionQuotientMap_surjective (m : ℕ) :
    Function.Surjective (sphereSuspensionQuotientMap m) := by
  intro z
  let e := EuclideanSpace.finAddEquivProd (n := m + 1) (m := 1) (𝕜 := ℝ)
  let y : EuclideanSpace ℝ (Fin (m + 1)) := (e z.1).1
  let a : ℝ := (e z.1).2 (0 : Fin 1)
  have hzNorm : ‖z.1‖ = 1 := by
    have h := z.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h
  have hsum : ‖y‖ ^ 2 + a ^ 2 = 1 := by
    have h := norm_sq_eq_finAdd m z.1
    rw [hzNorm, one_pow, sq_abs] at h
    simpa [e, y, a] using h.symm
  have haLower : -1 ≤ a := by nlinarith [sq_nonneg (a + 1), sq_nonneg ‖y‖]
  have haUpper : a ≤ 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg ‖y‖]
  let tval : ℝ := (a + 1) / 2
  have htval0 : 0 ≤ tval := by dsimp [tval]; linarith
  have htval1 : tval ≤ 1 := by dsimp [tval]; linarith
  let t : unitInterval := ⟨tval, htval0, htval1⟩
  have hlast : WithLp.toLp 2 (fun _ : Fin 1 => 2 * tval - 1) = (e z.1).2 := by
    apply PiLp.ext
    intro i
    fin_cases i
    change 2 * tval - 1 = a
    dsimp [tval]
    ring
  have hez : e z.1 = (y, WithLp.toLp 2 (fun _ : Fin 1 => 2 * tval - 1)) := by
    apply Prod.ext
    · rfl
    · exact hlast.symm
  by_cases hy : y = 0
  · let x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := northPt m
    refine ⟨(x, t), ?_⟩
    apply Subtype.ext
    apply e.injective
    change
      e (EuclideanSpace.finAddEquivProd.symm
        ((2 * Real.sqrt (t.1 * (1 - t.1))) • x.1,
          WithLp.toLp 2 (fun _ : Fin 1 => 2 * t.1 - 1))) = e z.1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change
      ((2 * Real.sqrt (tval * (1 - tval))) • x.1,
        WithLp.toLp 2 (fun _ : Fin 1 => 2 * tval - 1)) = e z.1
    rw [hez]
    have haSq : a ^ 2 = 1 := by simpa [hy] using hsum
    have hrad : tval * (1 - tval) = 0 := by
      dsimp [tval]
      nlinarith
    have hscale : 2 * Real.sqrt (tval * (1 - tval)) = 0 := by
      rw [hrad]
      simp
    apply Prod.ext
    · rw [hscale, zero_smul, hy]
    · rfl
  · have hyNorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hxmem : ‖y‖⁻¹ • y ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hyNorm)]
      exact inv_mul_cancel₀ hyNorm.ne'
    let x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      ⟨‖y‖⁻¹ • y, hxmem⟩
    have hradNonneg : 0 ≤ tval * (1 - tval) :=
      mul_nonneg htval0 (sub_nonneg.mpr htval1)
    have hradEq : 4 * (tval * (1 - tval)) = ‖y‖ ^ 2 := by
      dsimp [tval]
      nlinarith
    have hscale : 2 * Real.sqrt (tval * (1 - tval)) = ‖y‖ := by
      have hsqrtSq := Real.sq_sqrt hradNonneg
      have hsqrtNonneg := Real.sqrt_nonneg (tval * (1 - tval))
      nlinarith [norm_nonneg y]
    refine ⟨(x, t), ?_⟩
    apply Subtype.ext
    apply e.injective
    change
      e (EuclideanSpace.finAddEquivProd.symm
        ((2 * Real.sqrt (t.1 * (1 - t.1))) • x.1,
          WithLp.toLp 2 (fun _ : Fin 1 => 2 * t.1 - 1))) = e z.1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change
      ((2 * Real.sqrt (tval * (1 - tval))) • x.1,
        WithLp.toLp 2 (fun _ : Fin 1 => 2 * tval - 1)) = e z.1
    rw [hez]
    apply Prod.ext
    · change (2 * Real.sqrt (tval * (1 - tval))) • (‖y‖⁻¹ • y) = y
      rw [hscale, smul_smul, mul_inv_cancel₀ hyNorm.ne', one_smul]
    · rfl

theorem sphereSuspensionQuotientMap_isQuotientMap (m : ℕ) :
    Topology.IsQuotientMap (sphereSuspensionQuotientMap m) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (sphereSuspensionQuotientMap_surjective m)
    (sphereSuspensionQuotientMap m).continuous

end AlgebraicTopology
