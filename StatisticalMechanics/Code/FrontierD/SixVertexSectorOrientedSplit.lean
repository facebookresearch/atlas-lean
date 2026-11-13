/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexCoordinateBethe









open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexSectorForwardInterlacedDecidable {N : Nat}
    (x y : SixVertexRow N) : Decidable (SixVertexForwardInterlaced x y) :=
  Classical.propDecidable _


noncomputable def sixVertexSectorForwardTransfer
    (N n : Nat) (c : Real) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) Real := by
  classical
  exact fun x y =>
    if SixVertexForwardInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y) then
      c ^ sixVertexRowDistance
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    else 0

theorem sixVertexSector_forwardInterlaced_refl
    {N n : Nat} (x : SixVertexSector N n) :
    SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow x) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · exact fun _ => le_rfl
  · intro k hk
    exact (sixVertexSectorPosition x).monotone (by
      apply Fin.mk_le_mk.mpr
      omega)

theorem sixVertexSector_forwardInterlaced_antisymm
    {N n : Nat} (x y : SixVertexSector N n)
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    x = y := by
  have hpXY := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  have hpYX := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  apply (Set.powersetCard.ofFinEmbEquiv (n := n) (I := Fin N)).symm.injective
  change sixVertexSectorPosition x = sixVertexSectorPosition y
  ext i
  exact le_antisymm (hpXY.1 i) (hpYX.1 i)


theorem sixVertexSectorTransfer_eq_forward_add_transpose
    (N n : Nat) (c : Real) :
    sixVertexSectorTransfer N n c =
      sixVertexSectorForwardTransfer N n c +
        (sixVertexSectorForwardTransfer N n c)ᵀ := by
  classical
  ext x y
  by_cases hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)
  · by_cases hyx : SixVertexForwardInterlaced
        (sixVertexSectorRow y) (sixVertexSectorRow x)
    · have heq := sixVertexSector_forwardInterlaced_antisymm x y hxy hyx
      subst y
      simp [sixVertexSectorTransfer, sixVertexSectorForwardTransfer,
        sixVertexTransfer, sixVertexSector_forwardInterlaced_refl,
        sixVertexRowDistance]
      norm_num
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hyx (sixVertexSector_forwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransfer, sixVertexSectorForwardTransfer,
        sixVertexTransfer, hxy, hyx, hrow, SixVertexInterlaced]
  · by_cases hyx : SixVertexForwardInterlaced
        (sixVertexSectorRow y) (sixVertexSectorRow x)
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hxy (sixVertexSector_forwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransfer, sixVertexSectorForwardTransfer,
        sixVertexTransfer, hxy, hyx, hrow, SixVertexInterlaced,
        sixVertexRowDistance_comm]
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hxy (sixVertexSector_forwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransfer, sixVertexSectorForwardTransfer,
        sixVertexTransfer, hxy, hyx, hrow, SixVertexInterlaced]

theorem sixVertexSectorForwardTransfer_transpose_apply
    (N n : Nat) (c : Real) (x y : SixVertexSector N n) :
    (sixVertexSectorForwardTransfer N n c)ᵀ x y =
      if SixVertexForwardInterlaced
          (sixVertexSectorRow y) (sixVertexSectorRow x) then
        c ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y)
      else 0 := by
  classical
  simp [sixVertexSectorForwardTransfer, sixVertexRowDistance_comm]

end

end StatMech.FrontierD
