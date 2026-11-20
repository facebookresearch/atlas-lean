/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry
import Code.FrontierA.IsingSurfaceTensionFiniteVolume
import Code.FrontierA.IsingSurfaceTensionBoundaryBridge

namespace StatMech.FrontierA

open scoped BigOperators
open Filter Topology
open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

theorem spin_glue_rectangularPrismConfigEquiv
    (eta : ConfigSpace (Site 3)) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    spin (glue eta (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (rectangularPrismSiteEquivSctBoxDobrushin n v).1 =
      spin sigma v := by
  unfold spin
  rw [glue_mem _ _
    (rectangularPrismSiteEquivSctBoxDobrushin n v).2]
  exact congrArg (fun b : Bool => if b then (1 : Real) else -1)
    (rectangularPrismConfigEquivSctBoxDobrushin_apply n sigma v)

theorem oddPrism_xZero_exterior_not_mem
    (n : Nat) (y z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1
      0 (-1) ∉ box 3 n := by
  intro h
  have h0 := h 0
  simp [coordShift] at h0
  omega

theorem oddPrism_xLast_exterior_not_mem
    (n : Nat) (y z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n
        ⟨Fin.last (2 * n), y, z⟩).1 0 1 ∉ box 3 n := by
  intro h
  have h0 := h 0
  simp [coordShift, Fin.last] at h0
  omega

theorem oddPrism_yZero_exterior_not_mem
    (n : Nat) (x z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1
      1 (-1) ∉ box 3 n := by
  intro h
  have h1 := h 1
  simp [coordShift] at h1
  omega

theorem oddPrism_yLast_exterior_not_mem
    (n : Nat) (x z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n
        ⟨x, Fin.last (2 * n), z⟩).1 1 1 ∉ box 3 n := by
  intro h
  have h1 := h 1
  simp [coordShift, Fin.last] at h1
  omega

theorem oddPrism_zZero_exterior_not_mem
    (n : Nat) (x y : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
      2 1 ∉ box 3 n := by
  intro h
  have h2 := h 2
  simp [coordShift] at h2
  omega

theorem oddPrism_zLast_exterior_not_mem
    (n : Nat) (x y : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n
        ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1) ∉ box 3 n := by
  intro h
  have h2 := h 2
  simp [coordShift, Fin.last] at h2
  omega

theorem spin_glue_plus_of_not_mem
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    {x : Site 3} (hx : x ∉ box 3 n) :
    spin (glue (plusField 3) tau) x = 1 := by
  unfold spin
  rw [glue_not_mem _ _ hx]
  rfl

@[simp] theorem spin_glue_plus_xZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1
        0 (-1)) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_xZero_exterior_not_mem n y z)

@[simp] theorem spin_glue_plus_xLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨Fin.last (2 * n), y, z⟩).1 0 1) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_xLast_exterior_not_mem n y z)

@[simp] theorem spin_glue_plus_yZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1
        1 (-1)) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_yZero_exterior_not_mem n x z)

@[simp] theorem spin_glue_plus_yLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, Fin.last (2 * n), z⟩).1 1 1) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_yLast_exterior_not_mem n x z)

@[simp] theorem spin_glue_plus_zZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
        2 1) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_zZero_exterior_not_mem n x y)

@[simp] theorem spin_glue_plus_zLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_zLast_exterior_not_mem n x y)



def oddPrismPlusInteractionTerm (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    OddPrismTouchIndex n -> Real
  | .xInternal x y z =>
      rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z *
        rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z
  | .yInternal x y z =>
      rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z *
        rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z
  | .zInternal x y z =>
      rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
        rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩
  | .xZero y z => spin sigma ⟨0, y, z⟩
  | .xLast y z => spin sigma ⟨Fin.last (2 * n), y, z⟩
  | .yZero x z => spin sigma ⟨x, 0, z⟩
  | .yLast x z => spin sigma ⟨x, Fin.last (2 * n), z⟩
  | .zZero x y => spin sigma ⟨x, y, 0⟩
  | .zLast x y => spin sigma ⟨x, y, Fin.last (2 * n)⟩

theorem bond_glue_plus_oddPrismTouchIndex
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n)
    (q : OddPrismTouchIndex n) :
    bond (glue (plusField 3)
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q) =
      oddPrismPlusInteractionTerm n sigma q := by
  cases q <;>
    simp [oddPrismTouchIndexBond, oddPrismPlusInteractionTerm, bond_mk,
      rectangularPrismSpin, spin_glue_rectangularPrismConfigEquiv,
      spin_glue_plus_xZero, spin_glue_plus_xLast, spin_glue_plus_yZero,
      spin_glue_plus_yLast, spin_glue_plus_zZero, spin_glue_plus_zLast]

theorem sum_oddPrismPlusInteractionTerm
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ q, oddPrismPlusInteractionTerm n sigma q) =
      rectangularPrismInternalInteraction sigma +
        oddRectangularPrismFaceInteraction n sigma := by
  have hinternal :
      (∑ x : Fin (2 * n), ∑ y : Fin (2 * n + 1),
          ∑ z : Fin (2 * n + 1),
            rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z *
              rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n),
          ∑ z : Fin (2 * n + 1),
            rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z *
              rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1),
          ∑ z : Fin (2 * n),
            rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩) =
        rectangularPrismInternalInteraction sigma := by
    unfold rectangularPrismInternalInteraction
    rfl
  rw [sum_oddPrismTouchIndex]
  simp only [oddPrismPlusInteractionTerm]
  rw [hinternal]
  unfold oddRectangularPrismFaceInteraction oddRectangularPrismFaceSum
  simp only [Fin.last, Nat.mul_comm]
  ring



theorem fvEnergy_plus_eq_rectangularPrismPlusEnergy
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    fvEnergy (plusField 3) n (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) =
      rectangularPrismPlusEnergy 1 sigma := by
  unfold fvEnergy rectangularPrismPlusEnergy
  simp only [zero_mul, sub_zero, neg_one_mul]
  change -(∑ edge ∈ bondFinsetTouch 3 n,
      bond (glue (plusField 3)
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) edge) =
    -(rectangularPrismInternalInteraction sigma +
      rectangularPrismPlusBoundaryInteraction sigma)
  congr 1
  rw [sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex]
  calc
    (∑ q, bond (glue (plusField 3)
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q)) =
        ∑ q, oddPrismPlusInteractionTerm n sigma q := by
      apply Finset.sum_congr rfl
      intro q _
      exact bond_glue_plus_oddPrismTouchIndex n sigma q
    _ = rectangularPrismInternalInteraction sigma +
        oddRectangularPrismFaceInteraction n sigma :=
      sum_oddPrismPlusInteractionTerm n sigma
    _ = rectangularPrismInternalInteraction sigma +
        rectangularPrismPlusBoundaryInteraction sigma := by
      rw [rectangularPrismPlusBoundaryInteraction_eq_faces]


theorem rectangularPrismPlusEnergy_eq_mul_fvEnergy
    (J : Real) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismPlusEnergy J sigma =
      J * fvEnergy (plusField 3) n (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
  rw [fvEnergy_plus_eq_rectangularPrismPlusEnergy]
  unfold rectangularPrismPlusEnergy
  ring



theorem rectangularPrismPlusPartition_eq_fvZ
    (J beta : Real) (n : Nat) :
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n =
      fvZ (plusField 3) n (bondFinsetTouch 3 n) (beta * J) 0 := by
  unfold rectangularPrismPlusPartition Z fvZ fvWeight
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [rectangularPrismPlusEnergy_eq_mul_fvEnergy]
  congr 1
  ring


def oddRectangularPrismMeanNegEnergy
    (J beta : Real) (n : Nat) : Real :=
  (∑ sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n,
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma) *
        (-rectangularPrismPlusEnergy J sigma)) /
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n



theorem oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy
    (J beta : Real) (n : Nat) :
    oddRectangularPrismMeanNegEnergy J beta n =
      J * fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n)
        (beta * J) 0 := by
  unfold oddRectangularPrismMeanNegEnergy fvMeanNegEnergy
  rw [rectangularPrismPlusPartition_eq_fvZ]
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  rw [← mul_div_assoc]
  apply congrArg (fun x => x / fvZ (plusField 3) n
    (bondFinsetTouch 3 n) (beta * J) 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [rectangularPrismPlusEnergy_eq_mul_fvEnergy]
  unfold fvWeight
  ring_nf


theorem hasDerivAt_log_rectangularPrismPlusPartition
    (J beta : Real) (n : Nat) :
    HasDerivAt
      (fun b => Real.log
        (rectangularPrismPlusPartition J b (2 * n + 1) (2 * n + 1) n))
      (oddRectangularPrismMeanNegEnergy J beta n) beta := by
  have hfun :
      (fun b => Real.log
        (rectangularPrismPlusPartition J b (2 * n + 1) (2 * n + 1) n)) =
      (fun b => Real.log
        (fvZ (plusField 3) n (bondFinsetTouch 3 n) (b * J) 0)) := by
    funext b
    rw [rectangularPrismPlusPartition_eq_fvZ]
  rw [hfun, oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy]
  convert
    (hasDerivAt_log_fvZ_beta (plusField 3) n (bondFinsetTouch 3 n)
      (beta * J) 0).comp beta ((hasDerivAt_id beta).mul_const J) using 1 <;>
    ring



theorem spin_glue_interface_of_not_mem_coord
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    {x : Site 3} (hx : x ∉ box 3 n) (z : Fin (2 * n + 1))
    (hx2 : x 2 = (n : Int) - z.val) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) x =
      oddRectangularPrismDobrushinSign n z := by
  unfold spin oddRectangularPrismDobrushinSign
  rw [glue_not_mem _ _ hx, interfaceField_apply]
  have hx2' : x (⟨2, by omega⟩ : Fin 3) = (n : Int) - z.val := by
    convert hx2
  rw [hx2']
  by_cases hz : n < z.val
  · have hneg : ¬ (0 : Int) ≤ (n : Int) - z.val := by
      rw [not_le]
      exact sub_neg.mpr (by exact_mod_cast hz)
    simp [hz, hneg]
  · have hnonneg : (0 : Int) ≤ (n : Int) - z.val := by
      exact sub_nonneg.mpr (by
        exact_mod_cast (Nat.le_of_not_gt hz))
    simp [hz, hnonneg]



theorem spin_glue_interface_of_not_mem_coord_at
    (n : Nat) (i : Fin 3) (hi : i.val = 2)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    {x : Site 3} (hx : x ∉ box 3 n) (z : Fin (2 * n + 1))
    (hx2 : x 2 = (n : Int) - z.val) :
    spin (glue (interfaceField i) tau) x =
      oddRectangularPrismDobrushinSign n z := by
  have hi' : i = (⟨2, by omega⟩ : Fin 3) := Fin.ext hi
  rw [hi']
  exact spin_glue_interface_of_not_mem_coord n tau hx z hx2

@[simp] theorem spin_glue_interface_xZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1
        0 (-1)) = oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_xZero_exterior_not_mem n y z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_xLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨Fin.last (2 * n), y, z⟩).1 0 1) =
      oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_xLast_exterior_not_mem n y z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_yZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1
        1 (-1)) = oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_yZero_exterior_not_mem n x z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_yLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, Fin.last (2 * n), z⟩).1 1 1) =
      oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_yLast_exterior_not_mem n x z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_zZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
        2 1) = oddRectangularPrismDobrushinSign n 0 := by
  unfold spin oddRectangularPrismDobrushinSign
  rw [glue_not_mem _ _ (oddPrism_zZero_exterior_not_mem n x y),
    interfaceField_apply]
  simp [coordShift]
  omega

@[simp] theorem spin_glue_interface_zLast
    (n : Nat) (hn : 0 < n)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) =
      oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) := by
  unfold spin oddRectangularPrismDobrushinSign
  rw [glue_not_mem _ _ (oddPrism_zLast_exterior_not_mem n x y),
    interfaceField_apply]
  simp [coordShift, Fin.last, hn]
  omega

theorem spin_glue_interface_zZero_at
    (n : Nat) (i : Fin 3) (hi : i.val = 2)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField i) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
        2 1) = oddRectangularPrismDobrushinSign n 0 := by
  have hi' : i = (⟨2, by omega⟩ : Fin 3) := Fin.ext hi
  rw [hi']
  exact spin_glue_interface_zZero n tau x y

theorem spin_glue_interface_zLast_at
    (n : Nat) (hn : 0 < n) (i : Fin 3) (hi : i.val = 2)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField i) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) =
      oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) := by
  have hi' : i = (⟨2, by omega⟩ : Fin 3) := Fin.ext hi
  rw [hi']
  exact spin_glue_interface_zLast n hn tau x y


def oddPrismDobrushinInteractionTerm (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    OddPrismTouchIndex n -> Real
  | .xInternal x y z => oddPrismPlusInteractionTerm n sigma (.xInternal x y z)
  | .yInternal x y z => oddPrismPlusInteractionTerm n sigma (.yInternal x y z)
  | .zInternal x y z => oddPrismPlusInteractionTerm n sigma (.zInternal x y z)
  | .xZero y z => oddRectangularPrismDobrushinSign n z * spin sigma ⟨0, y, z⟩
  | .xLast y z => oddRectangularPrismDobrushinSign n z *
      spin sigma ⟨Fin.last (2 * n), y, z⟩
  | .yZero x z => oddRectangularPrismDobrushinSign n z * spin sigma ⟨x, 0, z⟩
  | .yLast x z => oddRectangularPrismDobrushinSign n z *
      spin sigma ⟨x, Fin.last (2 * n), z⟩
  | .zZero x y => oddRectangularPrismDobrushinSign n 0 * spin sigma ⟨x, y, 0⟩
  | .zLast x y => oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) *
      spin sigma ⟨x, y, Fin.last (2 * n)⟩

theorem bond_glue_interface_oddPrismTouchIndex
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n)
    (q : OddPrismTouchIndex n) :
    bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3))
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q) =
      oddPrismDobrushinInteractionTerm n sigma q := by
  cases q <;>
    simp [oddPrismTouchIndexBond, oddPrismDobrushinInteractionTerm,
      oddPrismPlusInteractionTerm, bond_mk, rectangularPrismSpin,
      spin_glue_rectangularPrismConfigEquiv]
  case xZero y z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_xZero_exterior_not_mem n y z) z (by simp [coordShift])]
    ring
  case xLast y z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_xLast_exterior_not_mem n y z) z (by simp [coordShift])]
    ring
  case yZero x z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_yZero_exterior_not_mem n x z) z (by simp [coordShift])]
    ring
  case yLast x z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_yLast_exterior_not_mem n x z) z (by simp [coordShift])]
    ring
  case zZero x y =>
    rw [spin_glue_interface_zZero_at n _ rfl]
    ring
  case zLast x y =>
    rw [spin_glue_interface_zLast_at n hn _ rfl]
    ring

theorem sum_oddPrismDobrushinInteractionTerm
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ q, oddPrismDobrushinInteractionTerm n sigma q) =
      rectangularPrismInternalInteraction sigma +
        oddRectangularPrismDobrushinFaceInteraction n sigma := by
  have hinternal :
      (∑ x : Fin (2 * n), ∑ y : Fin (2 * n + 1),
          ∑ z : Fin (2 * n + 1),
            rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z *
              rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n),
          ∑ z : Fin (2 * n + 1),
            rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z *
              rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1),
          ∑ z : Fin (2 * n),
            rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩) =
        rectangularPrismInternalInteraction sigma := by
    unfold rectangularPrismInternalInteraction
    rfl
  rw [sum_oddPrismTouchIndex]
  simp only [oddPrismDobrushinInteractionTerm, oddPrismPlusInteractionTerm]
  rw [hinternal]
  unfold oddRectangularPrismDobrushinFaceInteraction
    oddRectangularPrismFaceSum
  simp only [Fin.last, Nat.mul_comm]
  ring


def oddRectangularPrismDobrushinEnergy (J : Real) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  -J * (rectangularPrismInternalInteraction sigma +
    oddRectangularPrismDobrushinFaceInteraction n sigma)

theorem fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    fvEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
        (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) =
      oddRectangularPrismDobrushinEnergy 1 n sigma := by
  unfold fvEnergy oddRectangularPrismDobrushinEnergy
  simp only [zero_mul, sub_zero, neg_one_mul]
  change -(∑ edge ∈ bondFinsetTouch 3 n,
      bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3))
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) edge) = _
  congr 1
  rw [sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex]
  calc
    (∑ q, bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3))
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q)) =
        ∑ q, oddPrismDobrushinInteractionTerm n sigma q := by
      apply Finset.sum_congr rfl
      intro q _
      exact bond_glue_interface_oddPrismTouchIndex n hn sigma q
    _ = _ := sum_oddPrismDobrushinInteractionTerm n sigma

theorem oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy
    (J : Real) (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    oddRectangularPrismDobrushinEnergy J n sigma =
      J * fvEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
        (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
  rw [fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy n hn]
  unfold oddRectangularPrismDobrushinEnergy
  ring



theorem sum_rectangularPrismDobrushinCoupling_eq
    (J beta : Real) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ q : RectangularPrismInteraction (2 * n + 1) (2 * n + 1) n,
        rectangularPrismDobrushinCoupling J beta q *
          rectangularPrismInteractionMonomial q sigma) =
      -beta * oddRectangularPrismDobrushinEnergy J n sigma := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rectangularPrismDobrushinCoupling,
    rectangularPrismInteractionMonomial]
  simp_rw [Fintype.sum_prod_type]
  have hboundary :
      (∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n,
          (if n < v.z.val then (-1 : Real) else 1) *
            (beta * J * rectangularPrismBoundaryDegree v) * spin sigma v) =
        beta * J *
          ∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n,
            oddRectangularPrismDobrushinSign n v.z *
              (rectangularPrismBoundaryDegree v : Real) * spin sigma v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    unfold oddRectangularPrismDobrushinSign
    by_cases hz : n < v.z.val <;> simp [hz] <;> ring
  rw [hboundary,
    rectangularPrismDobrushinBoundaryInteraction_eq_faces]
  unfold oddRectangularPrismDobrushinEnergy
    rectangularPrismInternalInteraction rectangularPrismSpin
  simp_rw [← Finset.mul_sum]
  ring



theorem rectangularPrismDobrushinPartition_eq_fvZ
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    rectangularPrismDobrushinPartition J beta
        (2 * n + 1) (2 * n + 1) n =
      fvZ (interfaceField (⟨2, by omega⟩ : Fin 3)) n
        (bondFinsetTouch 3 n) (beta * J) 0 := by
  unfold rectangularPrismDobrushinPartition monomialInteractionPartition
    fvZ fvWeight
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sum_rectangularPrismDobrushinCoupling_eq,
    oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy J n hn]
  congr 1
  ring



theorem oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    StatMech.Ising.rectangularDobrushinFreeEnergy J beta
        (2 * n + 1) (2 * n + 1) n =
      finiteInterfaceFreeEnergy (⟨2, by omega⟩ : Fin 3) n (beta * J) := by
  rw [StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio]
  unfold finiteInterfaceFreeEnergy
  rw [rectangularPrismPlusPartition_eq_fvZ,
    rectangularPrismDobrushinPartition_eq_fvZ J beta n hn]



theorem standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    (beta : Real) (n : Nat) (hn : 0 < n) :
    standardCubicInterfaceDensity beta n =
      rectangularPrismInterfaceDensity beta n := by
  unfold standardCubicInterfaceDensity rectangularPrismInterfaceDensity
  rw [oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy 1 beta n hn]
  simp



theorem hasStandardPrismSurfaceComparison (beta : Real) :
    HasStandardPrismSurfaceComparison beta := by
  unfold HasStandardPrismSurfaceComparison
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    beta n (by omega), sub_self]



theorem hasDerivAt_oddPrismDobrushinFreeEnergy
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    HasDerivAt
      (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b
        (2 * n + 1) (2 * n + 1) n)
      (J * (fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n)
          (beta * J) 0 -
        fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
          (bondFinsetTouch 3 n) (beta * J) 0)) beta := by
  have hfun :
      (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b
        (2 * n + 1) (2 * n + 1) n) =
      (fun b => finiteInterfaceFreeEnergy
        (⟨2, by omega⟩ : Fin 3) n (b * J)) := by
    funext b
    exact oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy J b n hn
  rw [hfun]
  convert
    (hasDerivAt_finiteInterfaceFreeEnergy
      (⟨2, by omega⟩ : Fin 3) n (beta * J)).comp beta
        ((hasDerivAt_id beta).mul_const J) using 1 <;>
    ring



theorem oddPrismDobrushinFreeEnergy_succ_eq_finiteInterfaceFreeEnergy
    (J beta : Real) (n : Nat) :
    StatMech.Ising.rectangularDobrushinFreeEnergy J beta
        (2 * (n + 1) + 1) (2 * (n + 1) + 1) (n + 1) =
      finiteInterfaceFreeEnergy (⟨2, by omega⟩ : Fin 3) (n + 1) (beta * J) :=
  oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy
    J beta (n + 1) (by omega)


theorem hasDerivAt_oddPrismDobrushinFreeEnergy_succ
    (J beta : Real) (n : Nat) :
    HasDerivAt
      (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b
        (2 * (n + 1) + 1) (2 * (n + 1) + 1) (n + 1))
      (J * (fvMeanNegEnergy (plusField 3) (n + 1)
          (bondFinsetTouch 3 (n + 1)) (beta * J) 0 -
        fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) (n + 1)
          (bondFinsetTouch 3 (n + 1)) (beta * J) 0)) beta :=
  hasDerivAt_oddPrismDobrushinFreeEnergy J beta (n + 1) (by omega)

end

end StatMech.FrontierA
