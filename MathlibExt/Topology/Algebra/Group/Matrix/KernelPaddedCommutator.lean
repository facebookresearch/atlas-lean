/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Whitehead
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section

open Matrix Topology

namespace Matrix.GeneralLinearGroup
namespace KernelPaddedCommutator

universe uI uR uS uX

variable {I : Type uI} [Fintype I] [DecidableEq I]

private theorem upperUnit_inv
    {R : Type uR} [Ring R] (A : Matrix I I R) :
    (BlockElementary.upperUnit A)⁻¹ = BlockElementary.upperUnit (-A) := by
  apply Units.ext
  rfl

private theorem lowerUnit_inv
    {R : Type uR} [Ring R] (A : Matrix I I R) :
    (BlockElementary.lowerUnit A)⁻¹ = BlockElementary.lowerUnit (-A) := by
  apply Units.ext
  rfl

private theorem map_upperUnit_eq_of_map_eq
    {R : Type uR} {S : Type uS} [Ring R] [Semiring S]
    (σ : R →+* S) (A B : Matrix I I R)
    (h : A.map σ = B.map σ) :
    mapRingHom σ (BlockElementary.upperUnit A) =
      mapRingHom σ (BlockElementary.upperUnit B) := by
  apply Units.ext
  simp only [coe_mapRingHom, BlockElementary.coe_upperUnit,
    Matrix.fromBlocks_map]
  rw [h]

private theorem map_lowerUnit_eq_of_map_eq
    {R : Type uR} {S : Type uS} [Ring R] [Semiring S]
    (σ : R →+* S) (A B : Matrix I I R)
    (h : A.map σ = B.map σ) :
    mapRingHom σ (BlockElementary.lowerUnit A) =
      mapRingHom σ (BlockElementary.lowerUnit B) := by
  apply Units.ext
  simp only [coe_mapRingHom, BlockElementary.coe_lowerUnit,
    Matrix.fromBlocks_map]
  rw [h]

private theorem continuous_upperUnit
    {R : Type uR} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Type uX} [TopologicalSpace X]
    (A : X → Matrix I I R) (hA : Continuous A) :
    Continuous fun x => BlockElementary.upperUnit (A x) := by
  have hval : Continuous fun x =>
      (↑(BlockElementary.upperUnit (A x)) : Matrix (I ⊕ I) (I ⊕ I) R) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [BlockElementary.coe_upperUnit,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
      fun_prop
  have hneg : Continuous fun x =>
      (↑(BlockElementary.upperUnit (-A x)) : Matrix (I ⊕ I) (I ⊕ I) R) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [BlockElementary.coe_upperUnit,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
      fun_prop
  apply Units.continuous_iff.mpr
  refine ⟨hval, ?_⟩
  simpa only [upperUnit_inv] using hneg

private theorem continuous_lowerUnit
    {R : Type uR} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Type uX} [TopologicalSpace X]
    (A : X → Matrix I I R) (hA : Continuous A) :
    Continuous fun x => BlockElementary.lowerUnit (A x) := by
  have hval : Continuous fun x =>
      (↑(BlockElementary.lowerUnit (A x)) : Matrix (I ⊕ I) (I ⊕ I) R) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [BlockElementary.coe_lowerUnit,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
      fun_prop
  have hneg : Continuous fun x =>
      (↑(BlockElementary.lowerUnit (-A x)) : Matrix (I ⊕ I) (I ⊕ I) R) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [BlockElementary.coe_lowerUnit,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
      fun_prop
  apply Units.continuous_iff.mpr
  refine ⟨hval, ?_⟩
  simpa only [lowerUnit_inv] using hneg

private def scalarMatrixPath
    {R : Type uR} [Ring R] [Module ℝ R]
    (t : unitInterval) : Matrix I I R :=
  Matrix.scalar I ((t : ℝ) • (1 : R))

private theorem scalarMatrixPath_zero
    {R : Type uR} [Ring R] [Module ℝ R] :
    scalarMatrixPath (I := I) (R := R) 0 = 0 := by
  ext i j
  simp [scalarMatrixPath, Matrix.scalar_apply]

private theorem scalarMatrixPath_one
    {R : Type uR} [Ring R] [Module ℝ R] :
    scalarMatrixPath (I := I) (R := R) 1 = 1 := by
  ext i j
  simp [scalarMatrixPath, Matrix.scalar_apply]

private theorem continuous_scalarMatrixPath
    {R : Type uR} [Ring R] [TopologicalSpace R]
    [Module ℝ R] [ContinuousSMul ℝ R] :
    Continuous (scalarMatrixPath (I := I) (R := R)) := by
  refine continuous_matrix fun i j => ?_
  simp only [scalarMatrixPath, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private def scaledMatrixPath
    {R : Type uR} [Ring R] [Module ℝ R]
    (q : GL I R) (t : unitInterval) : Matrix I I R :=
  scalarMatrixPath (I := I) t * (q : Matrix I I R)

private theorem continuous_scaledMatrixPath
    {R : Type uR} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    (q : GL I R) : Continuous (scaledMatrixPath q) := by
  exact (continuous_scalarMatrixPath (I := I) (R := R)).matrix_mul
    continuous_const

private theorem scaledMatrixPath_zero
    {R : Type uR} [Ring R] [Module ℝ R] (q : GL I R) :
    scaledMatrixPath q 0 = 0 := by
  simp [scaledMatrixPath, scalarMatrixPath_zero]

private theorem scaledMatrixPath_one
    {R : Type uR} [Ring R] [Module ℝ R] (q : GL I R) :
    scaledMatrixPath q 1 = (q : Matrix I I R) := by
  simp [scaledMatrixPath, scalarMatrixPath_one]

private def whiteheadTriple
    {R : Type uR} [Ring R] [Module ℝ R]
    (q : GL I R) (t : unitInterval) : GL (I ⊕ I) R :=
  BlockElementary.upperUnit (scaledMatrixPath q t) *
    (BlockElementary.lowerUnit (scaledMatrixPath q⁻¹ t))⁻¹ *
    BlockElementary.upperUnit (scaledMatrixPath q t)

private theorem continuous_whiteheadTriple
    {R : Type uR} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    (q : GL I R) : Continuous (whiteheadTriple q) := by
  exact ((continuous_upperUnit _ (continuous_scaledMatrixPath q)).mul
    (continuous_inv.comp
      (continuous_lowerUnit _ (continuous_scaledMatrixPath q⁻¹)))).mul
    (continuous_upperUnit _ (continuous_scaledMatrixPath q))

private theorem whiteheadTriple_zero
    {R : Type uR} [Ring R] [Module ℝ R] (q : GL I R) :
    whiteheadTriple q 0 = 1 := by
  simp [whiteheadTriple, scaledMatrixPath_zero,
    BlockElementary.upperUnit_zero, BlockElementary.lowerUnit_zero]

private theorem whiteheadTriple_one
    {R : Type uR} [Ring R] [Module ℝ R] (q : GL I R) :
    whiteheadTriple q 1 =
      BlockElementary.upperUnit (q : Matrix I I R) *
        BlockElementary.lowerUnit (-(↑(q⁻¹) : Matrix I I R)) *
        BlockElementary.upperUnit (q : Matrix I I R) := by
  simp only [whiteheadTriple, scaledMatrixPath_one, lowerUnit_inv]

private theorem whiteheadTriple_one_inv
    {R : Type uR} [Ring R] [Module ℝ R] :
    (whiteheadTriple (1 : GL I R) 1)⁻¹ =
      BlockElementary.upperUnit (-1 : Matrix I I R) *
        BlockElementary.lowerUnit (1 : Matrix I I R) *
        BlockElementary.upperUnit (-1 : Matrix I I R) := by
  rw [whiteheadTriple_one]
  simp only [inv_one, Units.val_one]
  let U : GL (I ⊕ I) R := BlockElementary.upperUnit (1 : Matrix I I R)
  let L : GL (I ⊕ I) R := BlockElementary.lowerUnit (-1 : Matrix I I R)
  have hfirst : (U * L * U)⁻¹ = U⁻¹ * (U * L)⁻¹ :=
    _root_.mul_inv_rev (U * L) U
  have hsecond : (U * L)⁻¹ = L⁻¹ * U⁻¹ := _root_.mul_inv_rev U L
  change (U * L * U)⁻¹ = _
  rw [hfirst, hsecond]
  dsimp only [U, L]
  simp only [upperUnit_inv, lowerUnit_inv, neg_neg, mul_assoc]

private def whiteheadKernelPath
    {R : Type uR} [Ring R] [Module ℝ R]
    (q : GL I R) (t : unitInterval) : GL (I ⊕ I) R :=
  whiteheadTriple q t * (whiteheadTriple (1 : GL I R) t)⁻¹

private theorem continuous_whiteheadKernelPath
    {R : Type uR} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    (q : GL I R) : Continuous (whiteheadKernelPath q) := by
  exact (continuous_whiteheadTriple q).mul
    (continuous_inv.comp (continuous_whiteheadTriple (1 : GL I R)))

private theorem whiteheadKernelPath_zero
    {R : Type uR} [Ring R] [Module ℝ R] (q : GL I R) :
    whiteheadKernelPath q 0 = 1 := by
  simp [whiteheadKernelPath, whiteheadTriple_zero]

private theorem whiteheadKernelPath_one
    {R : Type uR} [Ring R] [Module ℝ R] (q : GL I R) :
    whiteheadKernelPath q 1 = diagUnit q := by
  rw [whiteheadKernelPath, whiteheadTriple_one,
    whiteheadTriple_one_inv]
  simpa only [mul_assoc] using diagUnit_eq_six_unipotent q

private theorem scaledMatrixPath_map_eq_one
    {R : Type uR} {S : Type uS} [Ring R] [Semiring S]
    [Module ℝ R] (σ : R →+* S) (q : GL I R)
    (hq : mapRingHom σ q = 1) (t : unitInterval) :
    (scaledMatrixPath q t).map σ =
      (scaledMatrixPath (1 : GL I R) t).map σ := by
  have hqval := congrArg Units.val hq
  change (q : Matrix I I R).map σ = 1 at hqval
  simp only [scaledMatrixPath, Matrix.map_mul, hqval,
    Units.val_one, Matrix.mul_one]

private theorem map_whiteheadTriple_eq_one
    {R : Type uR} {S : Type uS} [Ring R] [Semiring S]
    [Module ℝ R] (σ : R →+* S) (q : GL I R)
    (hq : mapRingHom σ q = 1) (t : unitInterval) :
    mapRingHom σ (whiteheadTriple q t) =
      mapRingHom σ (whiteheadTriple (1 : GL I R) t) := by
  have hqinv : mapRingHom σ q⁻¹ = 1 := by
    rw [map_inv, hq, inv_one]
  have hscaled := scaledMatrixPath_map_eq_one σ q hq t
  have hscaledInv := scaledMatrixPath_map_eq_one σ q⁻¹ hqinv t
  simp only [whiteheadTriple, map_mul, map_inv]
  rw [map_upperUnit_eq_of_map_eq σ _ _ hscaled,
    map_lowerUnit_eq_of_map_eq σ _ _ hscaledInv]
  simp only [inv_one]

private theorem map_whiteheadKernelPath
    {R : Type uR} {S : Type uS} [Ring R] [Semiring S]
    [Module ℝ R] (σ : R →+* S) (q : GL I R)
    (hq : mapRingHom σ q = 1) (t : unitInterval) :
    mapRingHom σ (whiteheadKernelPath q t) = 1 := by
  rw [whiteheadKernelPath, map_mul, map_inv,
    map_whiteheadTriple_eq_one σ q hq t]
  exact mul_inv_cancel _

private def whiteheadKernelCurve
    {R : Type uR} {S : Type uS} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    [Semiring S] (σ : R →+* S)
    (q : (mapRingHom (n := I) σ).ker) :
    C(unitInterval, (mapRingHom (n := I ⊕ I) σ).ker) :=
  ⟨fun t => ⟨whiteheadKernelPath q.1 t,
      MonoidHom.mem_ker.mpr
        (map_whiteheadKernelPath σ q.1
          (MonoidHom.mem_ker.mp q.property) t)⟩,
    (continuous_whiteheadKernelPath q.1).subtype_mk _⟩

private theorem whiteheadKernelCurve_zero
    {R : Type uR} {S : Type uS} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    [Semiring S] (σ : R →+* S)
    (q : (mapRingHom (n := I) σ).ker) :
    whiteheadKernelCurve σ q 0 = 1 := by
  apply Subtype.ext
  exact whiteheadKernelPath_zero q.1

private theorem whiteheadKernelCurve_one
    {R : Type uR} {S : Type uS} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    [Semiring S] (σ : R →+* S)
    (q : (mapRingHom (n := I) σ).ker) :
    (whiteheadKernelCurve σ q 1).1 = diagUnit q.1 := by
  exact whiteheadKernelPath_one q.1

open scoped commutatorElement

/-- **Padded coefficient-kernel commutator lies in the identity component.**

Let I be a finite index type, R a topological ring with a continuous real-module scalar
action, S a semiring and σ:R→+*S a coefficient homomorphism. Put K_I=ker(mapRingHom
σ:GL(I,R)→GL(I,S)) and K_(I⊕I)=ker(mapRingHom σ:GL(I⊕I,R)→GL(I⊕I,S)), with their induced
topologies. For g,h∈K_I, there exists z∈K_(I⊕I) whose underlying matrix is
diag(g*h*g⁻¹*h⁻¹,I_I) and which belongs to the connected component of 1 in K_(I⊕I).
-/
theorem paddedCommutator_mem_connectedComponent_ker
    {R : Type uR} {S : Type uS} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [Module ℝ R] [ContinuousSMul ℝ R]
    [Semiring S] (σ : R →+* S)
    (g h : (mapRingHom (n := I) σ).ker) :
    ∃ z : (mapRingHom (n := I ⊕ I) σ).ker,
      z.1 = blockDiagonalOne I I R ⁅g.1, h.1⁆ ∧
        z ∈ connectedComponent
          (1 : (mapRingHom (n := I ⊕ I) σ).ker) := by
  let q : (mapRingHom (n := I) σ).ker := g⁻¹ * h⁻¹
  let Pg := whiteheadKernelCurve σ g
  let Ph := whiteheadKernelCurve σ h
  let Pq := whiteheadKernelCurve σ q
  let P : C(unitInterval, (mapRingHom (n := I ⊕ I) σ).ker) :=
    Pg * Ph * Pq
  have hP0 : P 0 = 1 := by
    simp only [P, Pg, Ph, Pq, ContinuousMap.mul_apply,
      whiteheadKernelCurve_zero, mul_one]
  have hP1 : (P 1).1 = blockDiagonalOne I I R ⁅g.1, h.1⁆ := by
    change (whiteheadKernelCurve σ g 1).1 *
        (whiteheadKernelCurve σ h 1).1 *
          (whiteheadKernelCurve σ q 1).1 = _
    rw [whiteheadKernelCurve_one, whiteheadKernelCurve_one,
      whiteheadKernelCurve_one]
    exact diagUnit_commutator_eq g.1 h.1
  have hjoined : Joined
      (1 : (mapRingHom (n := I ⊕ I) σ).ker) (P 1) :=
    ⟨Path.mk P hP0 rfl⟩
  refine ⟨P 1, hP1, ?_⟩
  exact pathComponent_subset_component
    (1 : (mapRingHom (n := I ⊕ I) σ).ker) hjoined

end KernelPaddedCommutator
end Matrix.GeneralLinearGroup
