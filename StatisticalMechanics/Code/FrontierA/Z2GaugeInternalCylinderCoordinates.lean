/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.Z2GaugeCubicalPlusCorrDecay









namespace StatMech.FrontierA

open StatMech StatMech.Lattice

noncomputable section


abbrev internalCylinderUpperIndex (N : Nat) := Fin N × Fin N



def internalCylinderBoundaryIndices (N : Nat) :
    Finset (CubicalCell N N N) :=
  (Finset.univ : Finset (CubicalCell N N N)).filter fun q =>
    q.x.val = 0 ∨ q.x.val + 1 = N ∨
    q.y.val = 0 ∨ q.y.val + 1 = N ∨
    q.z.val + 1 = N


def internalCylinderUpperCell (N m : Nat) (hNm : N <= m)
    (ij : internalCylinderUpperIndex N) :
    CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) :=
  CubicalCell.mk
    ⟨m + ij.1.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m + ij.2.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m, by dsimp [oddCubeSide]; omega⟩


def internalCylinderBoundaryCell (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (q : CubicalCell N N N) :
    CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) :=
  CubicalCell.mk
    ⟨m + q.x.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m + q.y.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m - 1 - q.z.val, by dsimp [oddCubeSide]; omega⟩


def internalCylinderBoundaryCoordinateVertices
    (N m : Nat) (hN : 0 < N) (hNm : N ≤ m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m)) :=
  (internalCylinderBoundaryIndices N).image fun q =>
    some (internalCylinderBoundaryCell N m hN hNm q)


def internalCylinderUpperSite {N : Nat}
    (ij : internalCylinderUpperIndex N) : Site 3 := fun k =>
  if k = (0 : Fin 3) then ij.1.val
  else if k = (1 : Fin 3) then ij.2.val
  else 0


def internalCylinderBoundarySite {N : Nat}
    (q : CubicalCell N N N) : Site 3 := fun k =>
  if k = (0 : Fin 3) then q.x.val
  else if k = (1 : Fin 3) then q.y.val
  else q.z.val + 1

theorem internalCylinderUpperCell_injective
    (N m : Nat) (hNm : N <= m) :
    Function.Injective (internalCylinderUpperCell N m hNm) := by
  intro ij kl h
  simp only [internalCylinderUpperCell, CubicalCell.mk.injEq] at h
  apply Prod.ext
  · apply Fin.ext
    have hx := congrArg Fin.val h.1
    simp only at hx
    omega
  · apply Fin.ext
    have hy := congrArg Fin.val h.2.1
    simp only at hy
    omega

theorem internalCylinderBoundaryCell_injective
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    Function.Injective (internalCylinderBoundaryCell N m hN hNm) := by
  intro q r h
  simp only [internalCylinderBoundaryCell, CubicalCell.mk.injEq] at h
  rcases q with ⟨qx, qy, qz⟩
  rcases r with ⟨rx, ry, rz⟩
  simp only at h
  rw [CubicalCell.mk.injEq]
  constructor
  · apply Fin.ext
    have hx := congrArg Fin.val h.1
    simp only at hx
    omega
  constructor
  · apply Fin.ext
    have hy := congrArg Fin.val h.2.1
    simp only at hy
    omega
  · apply Fin.ext
    have hz := congrArg Fin.val h.2.2
    simp only at hz
    omega


theorem cubicalInternalCentralUpperVertices_eq_internalCylinderUpperCell
    (N m : Nat) (hN : 0 < N) (hNm : N ≤ m) :
    cubicalInternalCentralUpperVertices N m hNm =
      (Finset.univ : Finset (internalCylinderUpperIndex N)).image
        (fun ij => some (internalCylinderUpperCell N m hNm ij)) := by
  rw [cubicalInternalCentralUpperVertices_eq_coordinate N m hN hNm]
  unfold cubicalInternalCentralUpperCoordinateVertices
  apply Finset.image_congr
  intro ij hij
  congr 1


theorem oddCubicalCenteredSite_internalCylinderUpperCell
    (N m : Nat) (hNm : N <= m)
    (ij : internalCylinderUpperIndex N) :
    oddCubicalCenteredSite m (internalCylinderUpperCell N m hNm ij) =
      internalCylinderUpperSite ij := by
  funext k
  fin_cases k <;>
    simp [internalCylinderUpperCell, internalCylinderUpperSite]


theorem oddCubicalCenteredSite_internalCylinderBoundaryCell
    (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (q : CubicalCell N N N) :
    oddCubicalCenteredSite m
        (internalCylinderBoundaryCell N m hN hNm q) =
      internalCylinderBoundarySite q := by
  funext k
  fin_cases k <;>
    simp [internalCylinderBoundaryCell, internalCylinderBoundarySite] <;>
    omega



theorem cubicalInternalCentralBoundaryVertices_eq_coordinate
    (N m : Nat) (hN : 0 < N) (hNm : N ≤ m) :
    cubicalInternalCentralBoundaryVertices N m =
      internalCylinderBoundaryCoordinateVertices N m hN hNm := by
  ext v
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    rcases q with ⟨qx, qy, qz⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    let qi : CubicalCell N N N := CubicalCell.mk
      ⟨qx.val - m, by omega⟩
      ⟨qy.val - m, by omega⟩
      ⟨m - 1 - qz.val, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨qi, ?_, ?_⟩
    · simp only [internalCylinderBoundaryIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      dsimp [qi]
      omega
    · congr 1
      rw [CubicalCell.mk.injEq]
      simp only [internalCylinderBoundaryCell, qi]
      constructor
      · apply Fin.ext
        simp only
        omega
      constructor
      · apply Fin.ext
        simp only
        omega
      · apply Fin.ext
        simp only
        omega
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    simp only [internalCylinderBoundaryIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq
    apply Finset.mem_image.mpr
    refine ⟨internalCylinderBoundaryCell N m hN hNm q, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      internalCylinderBoundaryCell]
    omega

end

end StatMech.FrontierA
