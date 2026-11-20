/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicReflection
import Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity











open Filter Metric Set Topology

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)
variable (G : BoundaryRadialTensorTentGeometry A)


noncomputable def BoundaryRadialTensorTentGeometry.reflectedInterpolant :
    Nat → Complex → Complex := fun n z ↦
  BoundaryRadialTensorTentGeometry.interpolant A G n
    ((starRingEnd Complex) z)



noncomputable def BoundaryRadialTensorTentGeometry.reflectedTangent :
    ∀ n, A.reflect.M n → Complex :=
  BoundaryRadialTensorTentGeometry.tangent A G

theorem BoundaryRadialTensorTentGeometry.reflectedInterpolant_continuous
    (n : Nat) : Continuous (G.reflectedInterpolant A n) := by
  exact (G.interpolant_continuous A n).comp Complex.continuous_conj



theorem BoundaryRadialTensorTentGeometry.reflected_projectedMedial
    (n : Nat) (e : A.reflect.M n) :
    isingProj (G.reflectedTangent A n e)
        (G.reflectedInterpolant A n (A.reflect.medialEmbedding n e)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.reflect.P n) (A.reflect.M n) (A.reflect.decEqM n)
        (A.reflect.dobrushin n) (A.reflect.mesh n) e := by
  simpa [BoundaryRadialTensorTentGeometry.reflectedInterpolant,
    BoundaryRadialTensorTentGeometry.reflectedTangent] using
      G.projectedMedial A n e



theorem MeshUniformCompactHolder.reflected
    {F : Nat → Complex → Complex} (H : A.MeshUniformCompactHolder F) :
    A.reflect.MeshUniformCompactHolder
      (fun n z ↦ F n ((starRingEnd Complex) z)) := by
  refine { holder := ?_ }
  intro K hK hKU
  have hK' : IsCompact (reflectComplexSet K) :=
    reflectComplexSet_isCompact hK
  have hKU' : reflectComplexSet K ⊆ A.U := by
    intro z hz
    rw [mem_reflectComplexSet] at hz
    have hz' := hKU hz
    simpa using (mem_reflectComplexSet.mp hz')
  obtain ⟨C, alpha, halpha, hholder⟩ := H.holder _ hK' hKU'
  refine ⟨C, alpha, halpha, ?_⟩
  intro n x hx y hy
  have hx' : (starRingEnd Complex) x ∈ reflectComplexSet K :=
    mem_reflectComplexSet.mpr (by simpa using hx)
  have hy' : (starRingEnd Complex) y ∈ reflectComplexSet K :=
    mem_reflectComplexSet.mpr (by simpa using hy)
  have h := hholder n ((starRingEnd Complex) x) hx'
    ((starRingEnd Complex) y) hy'
  simpa [Complex.isometry_conj.edist_eq] using h



noncomputable def BoundaryRadialTensorTentGeometry.toReflectedStableFullMedialInterpolation
    (H : A.MeshUniformCompactHolder
      (BoundaryRadialTensorTentGeometry.interpolant A G)) :
    A.reflect.StableFullMedialInterpolation (G.reflectedTangent A) :=
  StableFullMedialInterpolation.ofTensorTentCompactHolder A.reflect
    (G.reflectedTangent A) (G.reflectedInterpolant A)
    (G.reflectedInterpolant_continuous A)
    (G.reflected_projectedMedial A)
    H.reflected



theorem BoundaryRadialTensorTentGeometry.reflected_tendsto_iff
    {f : Complex → Complex} :
    TendstoLocallyUniformlyOn (G.reflectedInterpolant A)
        (fun z ↦ f ((starRingEnd Complex) z)) atTop
        (reflectComplexSet A.U) ↔
      TendstoLocallyUniformlyOn
        (BoundaryRadialTensorTentGeometry.interpolant A G)
        f atTop A.U := by
  exact tendstoLocallyUniformlyOn_reflect_iff

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
