/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev











namespace StatMech.Universality

open Filter Metric Set

noncomputable section




theorem norm_sub_sq_le_pathLength_mul_sum_dist
    (F : Complex → Complex) (gamma : Nat → Complex)
    (steps : Nat) (C : Real)
    (hstep : ∀ k < steps,
      ‖F (gamma k) - F (gamma (k + 1))‖ ^ 2 ≤
        C * dist (gamma k) (gamma (k + 1))) :
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤
      (steps : Real) * C *
        ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := by
  let a : Nat → Real := fun k ↦ dist (F (gamma k)) (F (gamma (k + 1)))
  let d : Nat → Real := fun k ↦ dist (gamma k) (gamma (k + 1))
  have hpath : dist (F (gamma 0)) (F (gamma steps)) ≤
      ∑ k ∈ Finset.range steps, a k :=
    dist_le_range_sum_dist (fun k ↦ F (gamma k)) steps
  have hpathSq : dist (F (gamma 0)) (F (gamma steps)) ^ 2 ≤
      (∑ k ∈ Finset.range steps, a k) ^ 2 := by
    nlinarith [show 0 ≤ dist (F (gamma 0)) (F (gamma steps)) from dist_nonneg,
      Finset.sum_nonneg (s := Finset.range steps) (fun k _ ↦
        (show 0 ≤ dist (F (gamma k)) (F (gamma (k + 1))) from dist_nonneg))]
  have hcauchy : (∑ k ∈ Finset.range steps, a k) ^ 2 ≤
      (steps : Real) * ∑ k ∈ Finset.range steps, a k ^ 2 := by
    simpa [a] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range steps)
        (f := fun k ↦ dist (F (gamma k)) (F (gamma (k + 1)))))
  have hsum : (∑ k ∈ Finset.range steps, a k ^ 2) ≤
      C * ∑ k ∈ Finset.range steps, d k := by
    calc
      (∑ k ∈ Finset.range steps, a k ^ 2) ≤
          ∑ k ∈ Finset.range steps, C * d k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simpa [a, d, dist_eq_norm] using hstep k hk'
      _ = C * ∑ k ∈ Finset.range steps, d k := by
        rw [Finset.mul_sum]
  calc
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 =
        dist (F (gamma 0)) (F (gamma steps)) ^ 2 := by rw [dist_eq_norm]
    _ ≤ (∑ k ∈ Finset.range steps, a k) ^ 2 := hpathSq
    _ ≤ (steps : Real) * ∑ k ∈ Finset.range steps, a k ^ 2 := hcauchy
    _ ≤ (steps : Real) * (C * ∑ k ∈ Finset.range steps, d k) := by
      gcongr
    _ = (steps : Real) * C *
        ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := by
      simp only [d]
      ring




theorem norm_sub_sq_le_pathLength_sq_mul_mesh
    (F : Complex → Complex) (gamma : Nat → Complex)
    (steps : Nat) (C mesh : Real) (hC : 0 ≤ C)
    (hstepDist : ∀ k < steps,
      dist (gamma k) (gamma (k + 1)) ≤ mesh)
    (hstepHolder : ∀ k < steps,
      ‖F (gamma k) - F (gamma (k + 1))‖ ^ 2 ≤
        C * dist (gamma k) (gamma (k + 1))) :
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤
      C * (steps : Real) ^ 2 * mesh := by
  have hpath := norm_sub_sq_le_pathLength_mul_sum_dist
    F gamma steps C hstepHolder
  have hsum : (∑ k ∈ Finset.range steps,
      dist (gamma k) (gamma (k + 1))) ≤ (steps : Real) * mesh := by
    calc
      _ ≤ ∑ _k ∈ Finset.range steps, mesh := by
        apply Finset.sum_le_sum
        intro k hk
        exact hstepDist k (Finset.mem_range.mp hk)
      _ = (steps : Real) * mesh := by simp
  calc
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤
        (steps : Real) * C *
          ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := hpath
    _ ≤ (steps : Real) * C * ((steps : Real) * mesh) := by
      gcongr
    _ = C * (steps : Real) ^ 2 * mesh := by ring




noncomputable def constantRadialTensorTent (k : Nat) : Complex → Complex :=
  finiteRadialGridInterpolant (k + 2) (1 / (k + 2 : Real)) (fun _ _ ↦ 1)


def constantRadialTensorTentBoundaryPoint (k : Nat) : Complex :=
  isingRadialGridPosition (1 / (k + 2 : Real)) 0 0


def constantRadialTensorTentExteriorPoint (k : Nat) : Complex :=
  isingRadialGridCellPoint (1 / (k + 2 : Real)) 0 0 (-1) 0

@[simp] theorem constantRadialTensorTent_boundaryPoint (k : Nat) :
    constantRadialTensorTent k (constantRadialTensorTentBoundaryPoint k) = 1 := by
  let i : Fin (k + 2) := ⟨0, by omega⟩
  let j : Fin (k + 2) := ⟨0, by omega⟩
  simpa [constantRadialTensorTent, constantRadialTensorTentBoundaryPoint, i, j]
    using finiteRadialGridInterpolant_position
      (k + 2) (1 / (k + 2 : Real)) (by positivity)
      (fun _ _ : Fin (k + 2) ↦ (1 : Complex)) i j



theorem constantRadialTensorTent_cellPoint
    (k i j : Nat) (hi : i + 1 < k + 2) (hj : j + 1 < k + 2)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    constantRadialTensorTent k
      (isingRadialGridCellPoint (1 / (k + 2 : Real)) i j x y) = 1 := by
  rw [constantRadialTensorTent, finiteRadialGridInterpolant_cellPoint
    (1 / (k + 2 : Real)) (by positivity) _ i j hi hj x y hx0 hx1 hy0 hy1]
  simp [complexBilinearCell]
  ring

@[simp] theorem constantRadialTensorTent_exteriorPoint (k : Nat) :
    constantRadialTensorTent k (constantRadialTensorTentExteriorPoint k) = 0 := by
  classical
  unfold constantRadialTensorTent constantRadialTensorTentExteriorPoint
  unfold finiteRadialGridInterpolant
  rw [isingRadialGridCoordinate_cellPoint (1 / (k + 2 : Real))
    (by positivity) 0 0 (-1) 0]
  apply Finset.sum_eq_zero
  intro i hi
  have hi0 : (0 : Real) ≤ i.1 := by positivity
  have htent : isingLinearTent ((-1 : Real) - (i.1 : Real)) = 0 := by
    unfold isingLinearTent
    rw [abs_of_nonpos (by linarith)]
    simp
  simp [htent]

theorem constantRadialTensorTent_points_tendsto_same :
    Tendsto (fun k ↦ dist (constantRadialTensorTentBoundaryPoint k)
      (constantRadialTensorTentExteriorPoint k)) atTop (nhds 0) := by
  have hmesh : Tendsto (fun k : Nat ↦ 1 / (k + 2 : Real)) atTop (nhds 0) := by
    convert ((tendsto_natCast_atTop_atTop (R := Real)).comp
      (Filter.tendsto_add_atTop_nat 2) |>.const_div_atTop 1) using 1 <;>
      simp [Function.comp_apply]
  have hboundary : Tendsto constantRadialTensorTentBoundaryPoint atTop (nhds 0) := by
    change Tendsto (fun k : Nat ↦
      isingRadialGridPosition (1 / (k + 2 : Real)) 0 0) atTop (nhds 0)
    simpa [isingRadialGridPosition, Nat.cast_add, Nat.cast_ofNat] using
      hmesh.ofReal.mul_const (⟨(1 : Real) / 2, 0⟩ : Complex)
  have hexterior : Tendsto constantRadialTensorTentExteriorPoint atTop (nhds 0) := by
    change Tendsto (fun k : Nat ↦
      isingRadialGridCellPoint (1 / (k + 2 : Real)) 0 0 (-1) 0)
        atTop (nhds 0)
    simpa [isingRadialGridCellPoint, Nat.cast_add, Nat.cast_ofNat] using
      hmesh.ofReal.mul_const (⟨0, (-1 : Real) / 2⟩ : Complex)
  simpa using hboundary.dist hexterior





theorem constantRadialTensorTent_not_meshUniformFullHolder :
    ¬ Nonempty
      (FKIsingCaratheodoryApproximation.MeshUniformFullHolder
        constantRadialTensorTent) := by
  rintro ⟨H⟩
  have hdistOut (k : Nat) :
      dist (constantRadialTensorTent k (constantRadialTensorTentBoundaryPoint k))
        (constantRadialTensorTent k (constantRadialTensorTentExteriorPoint k)) = 1 := by
    simp [dist_eq_norm]
  have hinput := constantRadialTensorTent_points_tendsto_same
  have halpha : (0 : Real) < (H.exponent : Real) := H.exponent_pos
  have hrpow : Tendsto (fun k ↦
      dist (constantRadialTensorTentBoundaryPoint k)
        (constantRadialTensorTentExteriorPoint k) ^ (H.exponent : Real))
      atTop (nhds 0) := by
    have ht := (Real.continuousAt_rpow_const 0 (H.exponent : Real)
      (Or.inr halpha.le)).tendsto.comp hinput
    simpa [Real.zero_rpow halpha.ne'] using ht
  have hrhs : Tendsto (fun k ↦ (H.constant : Real) *
      dist (constantRadialTensorTentBoundaryPoint k)
        (constantRadialTensorTentExteriorPoint k) ^ (H.exponent : Real))
      atTop (nhds 0) := by
    simpa using hrpow.const_mul (H.constant : Real)
  have hevent : ∀ᶠ k in atTop, (H.constant : Real) *
      dist (constantRadialTensorTentBoundaryPoint k)
        (constantRadialTensorTentExteriorPoint k) ^ (H.exponent : Real) < 1 :=
    (tendsto_order.1 hrhs).2 1 (by norm_num)
  rw [eventually_atTop] at hevent
  obtain ⟨k, hk⟩ := hevent
  have hk' := hk k (le_refl k)
  have hholder := (H.holder k).dist_le
    (constantRadialTensorTentBoundaryPoint k)
    (constantRadialTensorTentExteriorPoint k)
  rw [hdistOut k] at hholder
  exact (not_lt_of_ge hholder) hk'

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)




structure MeshUniformCompactHolder (F : Nat → Complex → Complex) where
  holder : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ constant exponent : NNReal, 0 < exponent ∧
      ∀ n, HolderOnWith constant exponent (F n) K

theorem MeshUniformCompactHolder.equicontinuousOn
    {F : Nat → Complex → Complex} (H : A.MeshUniformCompactHolder F)
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U) :
    EquicontinuousOn F K := by
  obtain ⟨C, alpha, halpha, hholder⟩ := H.holder K hK hKU
  rw [← equicontinuous_restrict_iff]
  apply UniformEquicontinuous.equicontinuous
  apply Metric.uniformEquicontinuous_of_continuity_modulus
    (fun d : Real ↦ (C : Real) * d ^ (alpha : Real))
  · have hp : (0 : Real) < (alpha : Real) := halpha
    have ht := (Real.continuousAt_rpow_const 0 (alpha : Real)
      (Or.inr hp.le)).tendsto.const_mul (C : Real)
    simpa [Real.zero_rpow hp.ne'] using ht
  · intro x y n
    simpa using (hholder n).dist_le x.property y.property



noncomputable def StableFullMedialInterpolation.ofTensorTentCompactHolder
    (tangent : ∀ n, A.M n → Complex)
    (F : Nat → Complex → Complex)
    (hcontinuous : ∀ n, Continuous (F n))
    (hprojected : ∀ n e,
      isingProj (tangent n e) (F n (A.medialEmbedding n e)) =
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
    (H : A.MeshUniformCompactHolder F) :
    A.StableFullMedialInterpolation tangent where
  interpolant := F
  continuousOn n := (hcontinuous n).continuousOn
  projectedMedial := hprojected
  compactEquicontinuous K hK hKU :=
    MeshUniformCompactHolder.equicontinuousOn A H K hK hKU



noncomputable def BoundaryRadialTensorTentGeometry.toStableFullMedialInterpolationCompact
    (G : BoundaryRadialTensorTentGeometry A)
    (H : A.MeshUniformCompactHolder
      (BoundaryRadialTensorTentGeometry.interpolant A G)) :
    A.StableFullMedialInterpolation
      (BoundaryRadialTensorTentGeometry.tangent A G) :=
  StableFullMedialInterpolation.ofTensorTentCompactHolder A
    (BoundaryRadialTensorTentGeometry.tangent A G)
    (BoundaryRadialTensorTentGeometry.interpolant A G)
    (BoundaryRadialTensorTentGeometry.interpolant_continuous A G)
    (BoundaryRadialTensorTentGeometry.projectedMedial A G) H

variable {tangent : ∀ n, A.M n → Complex}
variable (I : A.StableFullMedialInterpolation tangent)




theorem StableFullMedialInterpolation.hasCompactLocalBounds_of_compactHolder_anchor
    (H : A.MeshUniformCompactHolder I.interpolant)
    (B : Real) (hanchor : ∀ n, ‖I.interpolant n A.root‖ ≤ B) :
    I.HasCompactLocalBounds := by
  intro K hK hKU
  let K' : Set Complex := insert A.root K
  have hK' : IsCompact K' := hK.insert A.root
  have hK'U : K' ⊆ A.U := by
    intro z hz
    rcases hz with rfl | hz
    · exact A.root_mem
    · exact hKU hz
  obtain ⟨C, alpha, _halpha, hholder⟩ := H.holder K' hK' hK'U
  have hdistContinuous : Continuous (fun z : Complex ↦ dist z A.root) :=
    continuous_id.dist continuous_const
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    hdistContinuous.continuousOn
  refine ⟨B + (C : Real) * D ^ (alpha : Real), ?_⟩
  intro n z hz
  have hz' : z ∈ K' := Or.inr hz
  have hroot' : A.root ∈ K' := Or.inl rfl
  calc
    ‖I.interpolant n z‖ ≤ ‖I.interpolant n A.root‖ +
        ‖I.interpolant n z - I.interpolant n A.root‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ = ‖I.interpolant n A.root‖ +
        dist (I.interpolant n z) (I.interpolant n A.root) := by
      rw [dist_eq_norm]
    _ ≤ B + (C : Real) * dist z A.root ^ (alpha : Real) :=
      add_le_add (hanchor n) ((hholder n).dist_le hz' hroot')
    _ ≤ B + (C : Real) * D ^ (alpha : Real) := by
      gcongr
      simpa [Real.norm_of_nonneg dist_nonneg] using hD z hz



theorem StableFullMedialInterpolation.scalingLimit_of_tensorTentCompactHolder
    (H : A.MeshUniformCompactHolder I.interpolant)
    (B : Real) (hanchorBound : ∀ n, ‖I.interpolant n A.root‖ ≤ B)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  exact StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    A I target Phi htarget htarget_ne hPhi hPhideriv E
      (StableFullMedialInterpolation.hasCompactLocalBounds_of_compactHolder_anchor
        A I H B hanchorBound) hidentify

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
