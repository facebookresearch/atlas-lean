/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSpatialResidualComparison
import Mathlib.NumberTheory.Harmonic.Bounds










namespace StatMech.Universality

open Finset Filter
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section





theorem finiteSum_le_harmonic_of_radialShellBoundAtScale
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (scale shellCount : Nat) (hscale : 0 < scale)
    (radius : alpha -> Nat) (f : alpha -> Real) (C D : Real)
    (hC : 0 <= C)
    (hradius : forall a, radius a < shellCount)
    (hf : forall a, f a <=
      C / ((scale : Real) * ((radius a + 1 : Nat) : Real) ^ 2))
    (hshell : forall r, r < shellCount ->
      (((univ.filter (fun a => radius a = r)).card : Nat) : Real) <=
        D * ((r + 1 : Nat) : Real)) :
    (∑ a, f a : Real) <=
      C * D * (harmonic shellCount : Real) / (scale : Real) := by
  have hscaleR : (0 : Real) < scale := by exact_mod_cast hscale
  rw [<- sum_fiberwise_of_maps_to
    (s := univ) (t := range shellCount) (g := radius)
    (fun a _ => mem_range.mpr (hradius a)) f]
  calc
    (∑ r ∈ range shellCount,
        ∑ a ∈ univ.filter (fun a => radius a = r), f a : Real) <=
        ∑ r ∈ range shellCount,
          (C * D / (scale : Real)) *
            (1 / ((r + 1 : Nat) : Real)) := by
      apply sum_le_sum
      intro r hr
      have hrn : r < shellCount := mem_range.mp hr
      have hrpos : (0 : Real) < ((r + 1 : Nat) : Real) := by positivity
      calc
        (∑ a ∈ univ.filter (fun a => radius a = r), f a : Real) <=
            ∑ _a ∈ univ.filter (fun a => radius a = r),
              C / ((scale : Real) * ((r + 1 : Nat) : Real) ^ 2) := by
          apply sum_le_sum
          intro a ha
          have har : radius a = r := (mem_filter.mp ha).2
          simpa [har] using hf a
        _ = (((univ.filter (fun a => radius a = r)).card : Nat) : Real) *
              (C / ((scale : Real) * ((r + 1 : Nat) : Real) ^ 2)) := by
          simp
        _ <= (D * ((r + 1 : Nat) : Real)) *
              (C / ((scale : Real) * ((r + 1 : Nat) : Real) ^ 2)) := by
          apply mul_le_mul_of_nonneg_right (hshell r hrn)
          positivity
        _ = (C * D / (scale : Real)) *
              (1 / ((r + 1 : Nat) : Real)) := by
          field_simp [hscaleR.ne', hrpos.ne']
    _ = C * D * (harmonic shellCount : Real) / (scale : Real) := by
      rw [<- Finset.mul_sum]
      simp_rw [one_div]
      rw [show (∑ r ∈ range shellCount,
          (((r + 1 : Nat) : Real))⁻¹ : Real) =
          (harmonic shellCount : Real) by
        simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]]
      ring


theorem finiteSum_le_harmonic_of_radialShellBound
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (n : Nat) (hn : 0 < n)
    (radius : alpha -> Nat) (f : alpha -> Real) (C D : Real)
    (hC : 0 <= C)
    (hradius : forall a, radius a < n)
    (hf : forall a, f a <=
      C / ((n : Real) * ((radius a + 1 : Nat) : Real) ^ 2))
    (hshell : forall r, r < n ->
      (((univ.filter (fun a => radius a = r)).card : Nat) : Real) <=
        D * ((r + 1 : Nat) : Real)) :
    (∑ a, f a : Real) <=
      C * D * (harmonic n : Real) / (n : Real) := by
  exact finiteSum_le_harmonic_of_radialShellBoundAtScale
    n n hn radius f C D hC hradius hf hshell



theorem tendsto_harmonic_div_natCast_succ :
    Tendsto (fun n : Nat =>
      (harmonic (n + 1) : Real) / ((n + 1 : Nat) : Real))
      atTop (nhds 0) := by
  have hlogBase : Tendsto (fun n : Nat =>
      Real.log (n : Real) / (n : Real)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : Nat =>
      Real.log ((n + 1 : Nat) : Real) / ((n + 1 : Nat) : Real))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hlogBase.comp (Filter.tendsto_add_atTop_nat 1)
  have hone : Tendsto (fun n : Nat =>
      1 / ((n + 1 : Nat) : Real)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => 1 / ((n : Real) + 1)) atTop (nhds 0))
  have hupper : Tendsto (fun n : Nat =>
      (1 + Real.log ((n + 1 : Nat) : Real)) /
        ((n + 1 : Nat) : Real)) atTop (nhds 0) := by
    simpa [add_div] using hone.add hlog
  apply squeeze_zero
  · intro n
    exact div_nonneg (by
      rw [harmonic, Rat.cast_sum]
      exact Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
  · exact fun n => div_le_div_of_nonneg_right
      (harmonic_le_one_add_log (n + 1)) (by positivity)
  · exact hupper


theorem tendsto_const_mul_harmonic_div_natCast_succ (C D : Real) :
    Tendsto (fun n : Nat =>
      C * D * (harmonic (n + 1) : Real) / ((n + 1 : Nat) : Real))
      atTop (nhds 0) := by
  have hconst : Tendsto (fun _ : Nat => C * D) atTop (nhds (C * D)) :=
    tendsto_const_nhds
  convert hconst.mul tendsto_harmonic_div_natCast_succ using 1
  · funext n
    ring
  · norm_num

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



theorem vertexSpatialTargetResidualPotential_le_harmonic_of_radialShellBound
    (n : Nat) (hn : 0 < n)
    (shellCount : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (x : Option (FKIsingSquareFullVertexNode n))
    (radius : Option (FKIsingSquareFullVertexNode n) -> Nat)
    (C D : Real) (hC : 0 <= C)
    (hradius : forall z, radius z < shellCount)
    (hpoint : forall z,
      vertexSpatialTargetResidual n target z *
          vertexPointPoissonBarrier n z x <=
        C / ((n : Real) * ((radius z + 1 : Nat) : Real) ^ 2))
    (hshell : forall r, r < shellCount ->
      (((Finset.univ.filter (fun z => radius z = r)).card : Nat) : Real) <=
        D * ((r + 1 : Nat) : Real)) :
    vertexSpatialTargetResidualPotential n target x <=
      C * D * (harmonic shellCount : Real) / (n : Real) := by
  rw [vertexSpatialTargetResidualPotential_eq_sum_point]
  simpa [smul_eq_mul] using
    finiteSum_le_harmonic_of_radialShellBoundAtScale n shellCount hn radius
      (fun z => vertexSpatialTargetResidual n target z *
        vertexPointPoissonBarrier n z x) C D hC hradius hpoint hshell



theorem faceSpatialTargetResidualPotential_le_harmonic_of_radialShellBound
    (n : Nat) (hn : 0 < n)
    (shellCount : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (x : Option (FKIsingSquareFullFaceNode n))
    (radius : Option (FKIsingSquareFullFaceNode n) -> Nat)
    (C D : Real) (hC : 0 <= C)
    (hradius : forall z, radius z < shellCount)
    (hpoint : forall z,
      faceSpatialTargetResidual n target z *
          facePointPoissonBarrier n z x <=
        C / ((n : Real) * ((radius z + 1 : Nat) : Real) ^ 2))
    (hshell : forall r, r < shellCount ->
      (((Finset.univ.filter (fun z => radius z = r)).card : Nat) : Real) <=
        D * ((r + 1 : Nat) : Real)) :
    faceSpatialTargetResidualPotential n target x <=
      C * D * (harmonic shellCount : Real) / (n : Real) := by
  rw [faceSpatialTargetResidualPotential_eq_sum_point]
  simpa [smul_eq_mul] using
    finiteSum_le_harmonic_of_radialShellBoundAtScale n shellCount hn radius
      (fun z => faceSpatialTargetResidual n target z *
        facePointPoissonBarrier n z x) C D hC hradius hpoint hshell

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
