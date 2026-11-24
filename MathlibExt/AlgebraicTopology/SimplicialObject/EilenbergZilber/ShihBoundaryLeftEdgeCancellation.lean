/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryLeftEdge

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- The total sign carried by a face of the `p = 0` left-edge family. -/
def leftEdgeCoefficient (N : ℕ) (q : Fin N) (a : Fin 2) : ℤ :=
  (-1 : ℤ) ^ (leftEdgeFace N q a).val * (leftEdgeIndex N q a).sign

@[simp]
theorem leftEdgeCoefficient_zero (N : ℕ) (q : Fin N) :
    leftEdgeCoefficient N q 0 = -1 := by
  unfold leftEdgeCoefficient sign
  rw [leftEdgeFace_zero, leftEdgeIndex_gap]
  simp only [Fin.val_mk, leftEdgeIndex]
  have hs := Shuffle.shuffleSignZ_leftBoundaryShuffle
    (Shuffle.leftUnitShuffle q.val) (0 : Fin 2)
  simp only [Shuffle.leftBoundaryIndex_zero, Fin.val_zero, pow_zero,
    one_mul, Shuffle.leftUnitShuffle_sign] at hs
  rw [show N - q.val + 1 = (N - q.val) + 1 by omega, pow_succ]
  rw [hs]
  have hsquare :
      (-1 : ℤ) ^ (N - q.val) * (-1 : ℤ) ^ (N - q.val) = 1 := by
    rw [← pow_add]
    have heven : N - q.val + (N - q.val) = 2 * (N - q.val) := by omega
    rw [heven, pow_mul]
    norm_num
  calc
    (-1 : ℤ) ^ (N - q.val) *
          ((-1 : ℤ) ^ (N - q.val) * -1 * 1) =
        ((-1 : ℤ) ^ (N - q.val) *
          (-1 : ℤ) ^ (N - q.val)) * -1 := by ring
    _ = -1 := by rw [hsquare]; norm_num

@[simp]
theorem leftEdgeCoefficient_last (N : ℕ) (q : Fin N) :
    leftEdgeCoefficient N q (Fin.last 1) = 1 := by
  unfold leftEdgeCoefficient sign
  rw [leftEdgeFace_last, leftEdgeIndex_gap]
  simp only [Fin.val_last, leftEdgeIndex]
  have hs := Shuffle.shuffleSignZ_leftBoundaryShuffle
    (Shuffle.leftUnitShuffle q.val) (Fin.last 1)
  simp only [Shuffle.leftBoundaryIndex_last, Fin.val_last,
    Shuffle.leftUnitShuffle_sign, zero_add, pow_one] at hs
  have hs' :
      (-1 : ℤ) ^ (q.val + 1) *
          shuffleSignZ
            (Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q.val)
              (Fin.last 1)) = -1 := by
    simpa [Nat.add_comm] using hs
  have hboundarySign :
      shuffleSignZ
          (Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q.val)
            (Fin.last 1)) = (-1 : ℤ) ^ q.val := by
    have hsquare :
        (-1 : ℤ) ^ (q.val + 1) * (-1 : ℤ) ^ (q.val + 1) = 1 := by
      rw [← pow_add]
      have heven : q.val + 1 + (q.val + 1) = 2 * (q.val + 1) := by omega
      rw [heven, pow_mul]
      norm_num
    calc
      _ = ((-1 : ℤ) ^ (q.val + 1) * (-1 : ℤ) ^ (q.val + 1)) * _ := by
        rw [hsquare, one_mul]
      _ = (-1 : ℤ) ^ (q.val + 1) *
          ((-1 : ℤ) ^ (q.val + 1) * _) := by ring
      _ = (-1 : ℤ) ^ (q.val + 1) * -1 := by rw [hs']
      _ = (-1 : ℤ) ^ q.val := by rw [pow_succ]; ring
  rw [hboundarySign]
  rw [show N - q.val + 1 = (N - q.val) + 1 by omega, pow_succ]
  have hsum : N = q.val + (N - q.val) := by
    have hq := q.isLt
    omega
  have hpowN :
      (-1 : ℤ) ^ N = (-1 : ℤ) ^ q.val * (-1 : ℤ) ^ (N - q.val) := by
    calc
      (-1 : ℤ) ^ N = (-1 : ℤ) ^ (q.val + (N - q.val)) :=
        congrArg (fun e : ℕ => (-1 : ℤ) ^ e) hsum
      _ = _ := pow_add _ _ _
  have hpowG :
      (-1 : ℤ) ^ (N - q.val + 1) =
        (-1 : ℤ) ^ (N - q.val) * -1 := by
    rw [show N - q.val + 1 = (N - q.val) + 1 by omega, pow_succ]
  rw [hpowN, hpowG]
  have hsquareQ : (-1 : ℤ) ^ q.val * (-1 : ℤ) ^ q.val = 1 := by
    rw [← pow_add]
    have heven : q.val + q.val = 2 * q.val := by omega
    rw [heven, pow_mul]
    norm_num
  have hsquareG :
      (-1 : ℤ) ^ (N - q.val) * (-1 : ℤ) ^ (N - q.val) = 1 := by
    rw [← pow_add]
    have heven : N - q.val + (N - q.val) = 2 * (N - q.val) := by omega
    rw [heven, pow_mul]
    norm_num
  calc
    ((-1 : ℤ) ^ q.val * (-1 : ℤ) ^ (N - q.val)) * -1 *
          (((-1 : ℤ) ^ (N - q.val) * -1) * (-1 : ℤ) ^ q.val) =
        ((-1 : ℤ) ^ q.val * (-1 : ℤ) ^ q.val) *
          ((-1 : ℤ) ^ (N - q.val) * (-1 : ℤ) ^ (N - q.val)) := by ring
    _ = 1 := by rw [hsquareQ, hsquareG]; norm_num

end ShihIndex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A last-insertion edge term cancels the next zero-insertion edge term. -/
theorem shihLeftEdge_last_add_zeroSucc_eq_zero
    (X Y : SimplicialObject C) (n : ℕ) (q : Fin n) :
    shihUpperBoundaryTerm X Y (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) q.castSucc (Fin.last 1))
        (ShihIndex.leftEdgeFace (n + 1) q.castSucc (Fin.last 1)) +
      shihUpperBoundaryTerm X Y (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) q.succ 0)
        (ShihIndex.leftEdgeFace (n + 1) q.succ 0) = 0 := by
  unfold shihUpperBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleft := congrArg Quiver.Hom.op
    (ShihIndex.delta_leftEdgeLast_comp_leftHom_eq_zeroSucc n q)
  have hright := congrArg Quiver.Hom.op
    (ShihIndex.delta_leftEdgeLast_comp_rightHom_eq_zeroSucc n q)
  simp only [CategoryTheory.op_comp] at hleft hright
  have hleftMap := congrArg (fun f => X.map f) hleft
  have hrightMap := congrArg (fun f => Y.map f) hright
  simp only [Functor.map_comp] at hleftMap hrightMap
  simp only [X.δ_def, Y.δ_def]
  rw [hleftMap, hrightMap]
  simp only [smul_smul]
  change ShihIndex.leftEdgeCoefficient (n + 1) q.castSucc (Fin.last 1) • _ +
    ShihIndex.leftEdgeCoefficient (n + 1) q.succ 0 • _ = 0
  rw [ShihIndex.leftEdgeCoefficient_last, ShihIndex.leftEdgeCoefficient_zero]
  simp

end AlgebraicTopology.EilenbergZilber
