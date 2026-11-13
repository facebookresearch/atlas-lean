/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry
import Code.Ising.RectangularPrismTransfer

namespace StatMech.FrontierA

open scoped BigOperators
open StatMech StatMech.Ising

noncomputable section


def oddRectangularPrismFaceSum (n : Nat)
    (f : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real) : Real :=
  (∑ y : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1), f ⟨0, y, z⟩) +
  (∑ y : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1),
      f ⟨Fin.last (2 * n), y, z⟩) +
  (∑ x : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1), f ⟨x, 0, z⟩) +
  (∑ x : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1),
      f ⟨x, Fin.last (2 * n), z⟩) +
  (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1), f ⟨x, y, 0⟩) +
  (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1),
      f ⟨x, y, Fin.last (2 * n)⟩)




def oddRectangularPrismFaceInteraction (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  oddRectangularPrismFaceSum n (spin sigma)


theorem sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum
    (n : Nat)
    (f : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real) :
    (∑ v, (rectangularPrismBoundaryDegree v : Real) * f v) =
      oddRectangularPrismFaceSum n f := by
  rw [sum_rectangularPrismSite_eq]
  simp only [rectangularPrismBoundaryDegree, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, add_mul,
    Finset.sum_add_distrib]
  have hlastSucc (x : Fin (2 * n + 1)) :
      x.val + 1 = 2 * n + 1 ↔ x = Fin.last (2 * n) := by
    constructor
    · intro hx
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · intro hx
      simp [hx]
  have hlastSuccEq (x : Fin (2 * n + 1)) :
      (x.val + 1 = 2 * n + 1) = (x = Fin.last (2 * n)) :=
    propext (hlastSucc x)
  simp_rw [hlastSuccEq]
  simp [oddRectangularPrismFaceSum, Fin.last]



theorem rectangularPrismPlusBoundaryInteraction_eq_faces
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismPlusBoundaryInteraction sigma =
      oddRectangularPrismFaceInteraction n sigma := by
  simpa [rectangularPrismPlusBoundaryInteraction,
    oddRectangularPrismFaceInteraction] using
    sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum n (spin sigma)



def oddRectangularPrismDobrushinSign (n : Nat) (z : Fin (2 * n + 1)) : Real :=
  if n < z.val then -1 else 1


def oddRectangularPrismDobrushinFaceInteraction (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  oddRectangularPrismFaceSum n fun v =>
    oddRectangularPrismDobrushinSign n v.z * spin sigma v


theorem rectangularPrismDobrushinBoundaryInteraction_eq_faces
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n,
        oddRectangularPrismDobrushinSign n v.z *
          (rectangularPrismBoundaryDegree v : Real) * spin sigma v) =
      oddRectangularPrismDobrushinFaceInteraction n sigma := by
  simpa [oddRectangularPrismDobrushinFaceInteraction, mul_assoc,
    mul_left_comm, mul_comm] using
    sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum n
      (fun v => oddRectangularPrismDobrushinSign n v.z * spin sigma v)

end

end StatMech.FrontierA
