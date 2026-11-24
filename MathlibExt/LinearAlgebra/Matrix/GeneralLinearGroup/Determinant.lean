/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementarySubgroup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Determinant for finite `GL`

Determinant compatibility for `mapRingHom`, `reindexMulEquiv`, `blockDiagonalOne`,
successor `stabilization`, elementary matrices, and `elementarySubgroup ≤ ker det`.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup

universe u v w vI

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {R : Type v} [CommRing R]
variable {S : Type w} [CommRing S]

/-- Determinant commutes with `mapRingHom` via `RingHom.map_det`. -/
@[simp]
theorem det_mapRingHom (f : R →+* S) (g : GL n R) :
    det (mapRingHom (n := n) f g) = (det g).map f := by
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply, coe_mapRingHom, Units.coe_map, MonoidHom.coe_ofClass]
  exact (RingHom.map_det f (↑g : Matrix n n R)).symm

section Reindex

variable {m : Type vI} [DecidableEq m] [Fintype m]

/-- Determinant is invariant under `reindexMulEquiv` via `det_reindex_self`. -/
@[simp]
theorem det_reindexMulEquiv (e : n ≃ m) (g : GL n R) :
    det (reindexMulEquiv (A := R) e g) = det g := by
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply, coe_reindexMulEquiv]
  exact det_reindex_self e (↑g : Matrix n n R)

end Reindex

section BlockDiagonal

variable {m : Type vI} [DecidableEq m] [Fintype m]

/-- Determinant of `blockDiagonalOne` is the original determinant,
via `det_fromBlocks_zero₂₁` and `det_one`. -/
@[simp]
theorem det_blockDiagonalOne (g : GL n R) :
    det (blockDiagonalOne n m R g) = det g := by
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply, coe_blockDiagonalOne, det_fromBlocks_zero₂₁,
    det_one, mul_one]

end BlockDiagonal

section Stabilization

/-- Determinant is invariant under successor `stabilization`,
via `blockDiagonalOne` and `reindexMulEquiv`. -/
@[simp]
theorem det_stabilization {k : ℕ} (g : GL (Fin k) R) :
    det (stabilization R (n := k) g) = det g := by
  calc
    det (stabilization R g)
        = det (reindexMulEquiv (finSumFinEquiv (m := k) (n := 1))
            (blockDiagonalOne (Fin k) (Fin 1) R g)) := rfl
    _ = det (blockDiagonalOne (Fin k) (Fin 1) R g) :=
        det_reindexMulEquiv (finSumFinEquiv (m := k) (n := 1))
          (blockDiagonalOne (Fin k) (Fin 1) R g)
    _ = det g := det_blockDiagonalOne g

end Stabilization

section ElementaryDet

variable {R : Type v} [CommRing R] {n : Type u} [DecidableEq n] [Fintype n]

/-- Determinant of an elementary matrix is `1`, via `det_transvection_of_ne`. -/
@[simp]
theorem det_elementary (i j : n) (hij : i ≠ j) (a : R) :
    det (elementary i j hij a) = 1 := by
  apply Units.ext
  -- `elementary` val is `1 + single i j a` = `transvection i j a`
  have h : (↑(elementary i j hij a) : Matrix n n R) = Matrix.transvection i j a := rfl
  simp only [GeneralLinearGroup.val_det_apply, h, det_transvection_of_ne i j hij a,
    Units.val_one]

theorem elementary_mem_ker_det (i j : n) (hij : i ≠ j) (a : R) :
    elementary i j hij a ∈ MonoidHom.ker (det : GL n R →* Rˣ) := by
  rw [MonoidHom.mem_ker]
  exact det_elementary i j hij a

/-- The finite elementary subgroup lies in the kernel of determinant. -/
theorem elementarySubgroup_le_ker_det :
    elementarySubgroup n R ≤ MonoidHom.ker (det : GL n R →* Rˣ) := by
  rw [elementarySubgroup, Subgroup.closure_le]
  intro y hy
  obtain ⟨i, j, hij, a, rfl⟩ := hy
  exact elementary_mem_ker_det i j hij a

/-- Every element of `elementarySubgroup` has determinant `1`. -/
theorem det_of_mem_elementarySubgroup {g : GL n R}
    (hg : g ∈ elementarySubgroup n R) : det g = 1 :=
  MonoidHom.mem_ker.mp (elementarySubgroup_le_ker_det hg)

end ElementaryDet

end GeneralLinearGroup
end Matrix
