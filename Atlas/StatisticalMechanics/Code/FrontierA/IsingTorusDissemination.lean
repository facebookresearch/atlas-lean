/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusReflection
import Code.FrontierA.IsingTorusCharacter

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}




def isingTorusTranslateField (a : IsingDyadicTorus d k)
    (u : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => u (x + a)


def isingTorusTranslateConfig (a : IsingDyadicTorus d k)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ConfigSpace (IsingDyadicTorus d k) :=
  fun x => sigma (x + a)


def isingTorusTranslateConfigEquiv (a : IsingDyadicTorus d k) :
    ConfigSpace (IsingDyadicTorus d k) ≃
      ConfigSpace (IsingDyadicTorus d k) where
  toFun := isingTorusTranslateConfig a
  invFun := isingTorusTranslateConfig (-a)
  left_inv sigma := by
    funext x
    simp [isingTorusTranslateConfig, add_assoc]
  right_inv sigma := by
    funext x
    simp [isingTorusTranslateConfig, add_assoc]

@[simp] theorem isingTorusTranslateField_zero
    (u : IsingDyadicTorus d k → Real) :
    isingTorusTranslateField 0 u = u := by
  funext x
  simp [isingTorusTranslateField]

theorem isingTorusTranslateField_add
    (a : IsingDyadicTorus d k)
    (u v : IsingDyadicTorus d k → Real) :
    isingTorusTranslateField a (u + v) =
      isingTorusTranslateField a u + isingTorusTranslateField a v := by
  rfl

theorem isingTorusTranslateField_neg_add
    (a : IsingDyadicTorus d k)
    (u : IsingDyadicTorus d k → Real) :
    isingTorusTranslateField (-a) (isingTorusTranslateField a u) = u := by
  funext x
  simp [isingTorusTranslateField, add_assoc]

theorem isingTorusSpinField_translateConfig
    (a : IsingDyadicTorus d k)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusSpinField (isingTorusTranslateConfig a sigma) =
      isingTorusTranslateField a (isingTorusSpinField sigma) := by
  rfl

theorem isingTorusDirichlet_translateField
    (a : IsingDyadicTorus d k)
    (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (isingTorusTranslateField a u) =
      isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  rw [← (Equiv.addRight a).bijective.sum_comp
    (fun y : IsingDyadicTorus d k ↦
    ∑ i : Fin d, (u y - u (y + isingTorusStep i)) *
      (u y - u (y + isingTorusStep i)))]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  simp only [isingTorusTranslateField, Equiv.coe_addRight]
  congr 2 <;> congr 1
  all_goals abel

theorem isingTorusShiftedPartition_translateField
    (a : IsingDyadicTorus d k) (beta : Real)
    (h : IsingDyadicTorus d k → Real) :
    isingTorusShiftedPartition beta (isingTorusTranslateField a h) =
      isingTorusShiftedPartition beta h := by
  calc
    isingTorusShiftedPartition beta (isingTorusTranslateField a h) =
        ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) * isingTorusDirichlet
            (isingTorusSpinField sigma + isingTorusTranslateField a h)) := rfl
    _ = ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) * isingTorusDirichlet
            (isingTorusSpinField (isingTorusTranslateConfig a sigma) +
              isingTorusTranslateField a h)) := by
        exact ((isingTorusTranslateConfigEquiv a).sum_comp (fun sigma =>
          Real.exp (-(beta / 2) * isingTorusDirichlet
            (isingTorusSpinField sigma +
              isingTorusTranslateField a h)))).symm
    _ = isingTorusShiftedPartition beta h := by
        unfold isingTorusShiftedPartition
        apply Finset.sum_congr rfl
        intro sigma _
        rw [isingTorusSpinField_translateConfig,
          ← isingTorusTranslateField_add,
          isingTorusDirichlet_translateField]





def isingTorusPolarizeLowerAt (i : Fin d)
    (a : IsingDyadicTorus d k) (h : IsingDyadicTorus d k → Real) :
    IsingDyadicTorus d k → Real :=
  isingTorusTranslateField (-a)
    (isingTorusPolarizeLower i (isingTorusTranslateField a h))

def isingTorusPolarizeUpperAt (i : Fin d)
    (a : IsingDyadicTorus d k) (h : IsingDyadicTorus d k → Real) :
    IsingDyadicTorus d k → Real :=
  isingTorusTranslateField (-a)
    (isingTorusPolarizeUpper i (isingTorusTranslateField a h))

theorem isingTorusShiftedPartition_polarization_at
    (i : Fin d) (a : IsingDyadicTorus d k)
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real) :
    2 * isingTorusShiftedPartition beta h ≤
      isingTorusShiftedPartition beta (isingTorusPolarizeLowerAt i a h) +
        isingTorusShiftedPartition beta (isingTorusPolarizeUpperAt i a h) := by
  unfold isingTorusPolarizeLowerAt isingTorusPolarizeUpperAt
  simpa only [isingTorusShiftedPartition_translateField] using
    (isingTorusShiftedPartition_polarization i beta hbeta
      (isingTorusTranslateField a h))




def isingTorusCoordinateShift (i : Fin d) (n : Nat) :
    IsingDyadicTorus d k :=
  Pi.single i (n : ZMod (2 ^ (k + 2)))

@[simp] theorem isingTorusCoordinateShift_apply_same
    (i : Fin d) (n : Nat) :
    isingTorusCoordinateShift (k := k) i n i = n := by
  simp [isingTorusCoordinateShift]

theorem isingTorusCoordinateShift_apply_of_ne
    (i j : Fin d) (hji : j ≠ i) (n : Nat) :
    isingTorusCoordinateShift (k := k) i n j = 0 := by
  simp [isingTorusCoordinateShift, hji]



def IsingTorusDisseminatedBlock (i : Fin d) (s : Nat)
    (h : IsingDyadicTorus d k → Real) : Prop :=
  ∀ x, (x i).val < s →
    h x = h (Function.update x i 0)

theorem isingTorusDisseminatedBlock_one
    (i : Fin d) (h : IsingDyadicTorus d k → Real) :
    IsingTorusDisseminatedBlock i 1 h := by
  intro x hx
  have hxi : x i = 0 := by
    apply (ZMod.val_eq_zero (x i)).mp
    omega
  congr 1
  symm
  simpa [hxi] using (Function.update_eq_self i x)

private theorem isingTorus_side_eq_two_mul_half' :
    2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring



def isingTorusBlockShift (i : Fin d) (s : Nat) :
    IsingDyadicTorus d k :=
  isingTorusCoordinateShift i (2 ^ (k + 1) + s)

private theorem isingTorus_blockShift_sub_val
    (s : Nat) (hs : s ≤ 2 ^ (k + 1))
    (z : ZMod (2 ^ (k + 2))) (hz : z.val < 2 * s) :
    (z - (2 ^ (k + 1) + s : Nat)).val =
      2 ^ (k + 1) - s + z.val := by
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half'
  have hpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  by_cases heq : s = 2 ^ (k + 1)
  · subst s
    have hcast :
        ((2 ^ (k + 1) + 2 ^ (k + 1) : Nat) :
          ZMod (2 ^ (k + 2))) = 0 := by
      rw [← two_mul, ← hside]
      exact ZMod.natCast_self _
    rw [hcast, sub_zero]
    omega
  · have hslt : s < 2 ^ (k + 1) := by omega
    have hnlt : 2 ^ (k + 1) - s + z.val < 2 ^ (k + 2) := by
      omega
    have hnat : z.val + 2 ^ (k + 2) =
        (2 ^ (k + 1) + s) + (2 ^ (k + 1) - s + z.val) := by
      omega
    have hnatcast := congrArg
      (fun n : Nat => (n : ZMod (2 ^ (k + 2)))) hnat
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hnatcast
    have heqmod : z - (2 ^ (k + 1) + s : Nat) =
        ((2 ^ (k + 1) - s + z.val : Nat) :
          ZMod (2 ^ (k + 2))) := by
      rw [← ZMod.natCast_zmod_val z]
      push_cast
      apply sub_eq_iff_eq_add.mpr
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using hnatcast
    rw [heqmod, ZMod.val_natCast_of_lt hnlt]

private theorem isingTorus_blockShift_lower_of_lt
    (i : Fin d) (s : Nat) (hs : s ≤ 2 ^ (k + 1))
    (x : IsingDyadicTorus d k) (hx : (x i).val < s) :
    isingTorusInLowerHalf i (x - isingTorusBlockShift i s) := by
  unfold isingTorusInLowerHalf isingTorusBlockShift
  rw [Pi.sub_apply, isingTorusCoordinateShift_apply_same]
  rw [isingTorus_blockShift_sub_val s hs (x i) (by omega)]
  omega

private theorem isingTorus_blockShift_not_lower_of_mem_second
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (x : IsingDyadicTorus d k)
    (hxs : s ≤ (x i).val) (hx2s : (x i).val < 2 * s) :
    ¬ isingTorusInLowerHalf i (x - isingTorusBlockShift i s) := by
  unfold isingTorusInLowerHalf isingTorusBlockShift
  rw [Pi.sub_apply, isingTorusCoordinateShift_apply_same]
  rw [isingTorus_blockShift_sub_val s hs (x i) hx2s]
  omega

private theorem isingTorus_block_reflected_site
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (x : IsingDyadicTorus d k)
    (hxs : s ≤ (x i).val) (hx2s : (x i).val < 2 * s) :
    isingTorusReflectSite i (x - isingTorusBlockShift i s) +
        isingTorusBlockShift i s =
      Function.update x i
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [Pi.add_apply, isingTorusReflectSite_apply_same,
      isingTorusBlockShift, isingTorusCoordinateShift_apply_same,
      Pi.sub_apply, isingTorusCoordinateShift_apply_same]
    have hu : Function.update x i
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) i =
      ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) := by
      simp
    rw [hu]
    rw [isingTorusReflectCoord_eq_neg_sub_one]
    have hnat : 2 * s - 1 - (x i).val + (x i).val + 1 = 2 * s := by
      omega
    have hnatcast := congrArg
      (fun n : Nat => (n : ZMod (2 ^ (k + 2)))) hnat
    push_cast at hnatcast
    have hxcast : ((x i).val : ZMod (2 ^ (k + 2))) = x i :=
      ZMod.natCast_zmod_val (x i)
    have hrhs :
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) =
          2 * (s : ZMod (2 ^ (k + 2))) - 1 - x i := by
      calc
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2))) =
            2 * (s : ZMod (2 ^ (k + 2))) - 1 -
              ((x i).val : ZMod (2 ^ (k + 2))) := by
                linear_combination hnatcast
        _ = 2 * (s : ZMod (2 ^ (k + 2))) - 1 - x i := by
          rw [hxcast]
    rw [hrhs]
    have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
      isingTorus_side_eq_two_mul_half'
    have hhalf :
        (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1) : Nat) = 0 := by
      calc
        (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1) : Nat) =
            ((2 * 2 ^ (k + 1) : Nat) : ZMod (2 ^ (k + 2))) := by
              push_cast
              rfl
        _ = ((2 ^ (k + 2) : Nat) : ZMod (2 ^ (k + 2))) := by
          rw [hside]
        _ = 0 := ZMod.natCast_self _
    rw [Nat.cast_add]
    linear_combination hhalf
  · rw [Pi.add_apply, isingTorusReflectSite_apply_of_ne i j hji]
    simp [hji, isingTorusBlockShift,
      isingTorusCoordinateShift_apply_of_ne i j hji]

private theorem isingTorus_block_reflected_val_lt
    (s : Nat) (hspos : 0 < s)
    (xval : Nat) (hxs : s ≤ xval) (hx2s : xval < 2 * s) :
    (2 * s - 1 - xval : Nat) < s := by
  omega

private theorem isingTorusPolarizeLowerAt_eq_of_block_lt
    (i : Fin d) (s : Nat) (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (x : IsingDyadicTorus d k) (hx : (x i).val < s) :
    isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h x = h x := by
  unfold isingTorusPolarizeLowerAt isingTorusTranslateField
  rw [show x + -isingTorusBlockShift i s =
    x - isingTorusBlockShift i s by abel]
  simp only [isingTorusPolarizeLower,
    isingTorus_blockShift_lower_of_lt i s hs x hx, if_true]
  congr 1
  abel

private theorem isingTorusPolarizeLowerAt_eq_of_mem_second
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (x : IsingDyadicTorus d k)
    (hxs : s ≤ (x i).val) (hx2s : (x i).val < 2 * s) :
    isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h x =
      h (Function.update x i
        ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2)))) := by
  unfold isingTorusPolarizeLowerAt isingTorusTranslateField
  rw [show x + -isingTorusBlockShift i s =
    x - isingTorusBlockShift i s by abel]
  simp only [isingTorusPolarizeLower,
    isingTorus_blockShift_not_lower_of_mem_second i s hspos hs x hxs hx2s,
    if_false]
  rw [isingTorus_block_reflected_site i s hspos hs x hxs hx2s]


theorem isingTorusDisseminatedBlock_double
    (i : Fin d) (s : Nat) (hspos : 0 < s)
    (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (hblock : IsingTorusDisseminatedBlock i s h) :
    IsingTorusDisseminatedBlock i (2 * s)
      (isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h) := by
  intro x hx
  have hzeroVal : ((Function.update x i 0) i).val < s := by
    simp
    exact hspos
  rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h
    (Function.update x i 0) hzeroVal]
  by_cases hxs : (x i).val < s
  · rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h x hxs]
    exact hblock x hxs
  · have hxs' : s ≤ (x i).val := by omega
    let y := Function.update x i
      ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2)))
    have hyval : (y i).val = 2 * s - 1 - (x i).val := by
      have hylt := isingTorus_block_reflected_val_lt
        s hspos (x i).val hxs' hx
      have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
        isingTorus_side_eq_two_mul_half'
      have hlt : 2 * s - 1 - (x i).val < 2 ^ (k + 2) := by
        omega
      simp [y, ZMod.val_natCast_of_lt hlt]
    have hylt : (y i).val < s := by
      rw [hyval]
      exact isingTorus_block_reflected_val_lt s hspos _ hxs' hx
    rw [isingTorusPolarizeLowerAt_eq_of_mem_second
      i s hspos hs h x hxs' hx]
    simpa [y] using hblock y hylt





def isingTorusIndexedField (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    IsingDyadicTorus d k → Real :=
  fun x => h (g x)

def isingTorusPolarizeLowerIndexAt (i : Fin d)
    (a : IsingDyadicTorus d k)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    IsingDyadicTorus d k → IsingDyadicTorus d k :=
  fun x =>
    if isingTorusInLowerHalf i (x + -a) then
      g ((x + -a) + a)
    else
      g (isingTorusReflectSite i (x + -a) + a)

def isingTorusPolarizeUpperIndexAt (i : Fin d)
    (a : IsingDyadicTorus d k)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    IsingDyadicTorus d k → IsingDyadicTorus d k :=
  fun x =>
    if isingTorusInLowerHalf i (x + -a) then
      g (isingTorusReflectSite i (x + -a) + a)
    else
      g ((x + -a) + a)

theorem isingTorusIndexedField_polarizeLowerIndexAt
    (i : Fin d) (a : IsingDyadicTorus d k)
    (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    isingTorusIndexedField h (isingTorusPolarizeLowerIndexAt i a g) =
      isingTorusPolarizeLowerAt i a (isingTorusIndexedField h g) := by
  funext x
  unfold isingTorusIndexedField isingTorusPolarizeLowerIndexAt
    isingTorusPolarizeLowerAt isingTorusTranslateField
    isingTorusPolarizeLower
  split_ifs <;> rfl

theorem isingTorusIndexedField_polarizeUpperIndexAt
    (i : Fin d) (a : IsingDyadicTorus d k)
    (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    isingTorusIndexedField h (isingTorusPolarizeUpperIndexAt i a g) =
      isingTorusPolarizeUpperAt i a (isingTorusIndexedField h g) := by
  funext x
  unfold isingTorusIndexedField isingTorusPolarizeUpperIndexAt
    isingTorusPolarizeUpperAt isingTorusTranslateField
    isingTorusPolarizeUpper
  split_ifs <;> rfl



theorem isingTorus_polarizeLower_preserves_indexed_max
    (i : Fin d) (a : IsingDyadicTorus d k)
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h g)) :
    isingTorusShiftedPartition beta
        (isingTorusIndexedField h (isingTorusPolarizeLowerIndexAt i a g)) =
      isingTorusShiftedPartition beta (isingTorusIndexedField h g) := by
  let gl := isingTorusPolarizeLowerIndexAt i a g
  let gu := isingTorusPolarizeUpperIndexAt i a g
  have hl := hmax gl
  have hu := hmax gu
  rw [isingTorusIndexedField_polarizeLowerIndexAt] at hl ⊢
  rw [isingTorusIndexedField_polarizeUpperIndexAt] at hu
  have hp := isingTorusShiftedPartition_polarization_at
    i a beta hbeta (isingTorusIndexedField h g)
  linarith



def IsingTorusDisseminatedBox (s : Fin d → Nat)
    (h : IsingDyadicTorus d k → Real) : Prop :=
  ∀ x, (∀ i, (x i).val < s i) → h x = h 0

theorem isingTorusDisseminatedBox_one
    (h : IsingDyadicTorus d k → Real) :
    IsingTorusDisseminatedBox (fun _ : Fin d => 1) h := by
  intro x hx
  have hx0 : x = 0 := by
    funext i
    apply (ZMod.val_eq_zero (x i)).mp
    have hi : (x i).val < 1 := by simpa using hx i
    omega
  rw [hx0]



theorem isingTorusDisseminatedBox_double
    (sizes : Fin d → Nat) (i : Fin d) (s : Nat)
    (hspos : 0 < s) (hs : s ≤ 2 ^ (k + 1))
    (h : IsingDyadicTorus d k → Real)
    (hbox : IsingTorusDisseminatedBox (Function.update sizes i s) h) :
    IsingTorusDisseminatedBox (Function.update sizes i (2 * s))
      (isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h) := by
  intro x hx
  have hzeroVal : ((0 : IsingDyadicTorus d k) i).val < s := by
    simpa using hspos
  rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h 0 hzeroVal]
  by_cases hxi : (x i).val < s
  · rw [isingTorusPolarizeLowerAt_eq_of_block_lt i s hs h x hxi]
    apply hbox x
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hxi
    · simpa [hji] using hx j
  · have hxis : s ≤ (x i).val := by omega
    have hxi2 : (x i).val < 2 * s := by
      simpa using hx i
    let y := Function.update x i
      ((2 * s - 1 - (x i).val : Nat) : ZMod (2 ^ (k + 2)))
    have hylt : (y i).val < s := by
      have hnlt : 2 * s - 1 - (x i).val < 2 ^ (k + 2) := by
        have hsmall := isingTorus_block_reflected_val_lt
          s hspos (x i).val hxis hxi2
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
          isingTorus_side_eq_two_mul_half'
        omega
      simp [y, ZMod.val_natCast_of_lt hnlt,
        isingTorus_block_reflected_val_lt s hspos (x i).val hxis hxi2]
    rw [isingTorusPolarizeLowerAt_eq_of_mem_second
      i s hspos hs h x hxis hxi2]
    apply hbox y
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hylt
    · simpa [y, hji] using hx j

private theorem isingTorus_indexed_max_box_double
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (gmax g : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (hg : isingTorusShiftedPartition beta (isingTorusIndexedField h g) =
      isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (sizes : Fin d → Nat) (i : Fin d) (s : Nat)
    (hspos : 0 < s) (hs : s ≤ 2 ^ (k + 1))
    (hbox : IsingTorusDisseminatedBox (Function.update sizes i s)
      (isingTorusIndexedField h g)) :
    ∃ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') =
          isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) ∧
        IsingTorusDisseminatedBox (Function.update sizes i (2 * s))
          (isingTorusIndexedField h g') := by
  let a := isingTorusBlockShift (k := k) i s
  let g' := isingTorusPolarizeLowerIndexAt i a g
  have hgmax : ∀ q : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h q) ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h g) := by
    intro q
    rw [hg]
    exact hmax q
  have hpres := isingTorus_polarizeLower_preserves_indexed_max
    i a beta hbeta h g hgmax
  refine ⟨g', ?_, ?_⟩
  · simpa [g'] using hpres.trans hg
  · simpa [g', isingTorusIndexedField_polarizeLowerIndexAt] using
      (isingTorusDisseminatedBox_double sizes i s hspos hs
        (isingTorusIndexedField h g) hbox)

private theorem isingTorus_indexed_max_disseminate_coordinate
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (gmax g : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (hg : isingTorusShiftedPartition beta (isingTorusIndexedField h g) =
      isingTorusShiftedPartition beta (isingTorusIndexedField h gmax))
    (sizes : Fin d → Nat) (i : Fin d)
    (hbox : IsingTorusDisseminatedBox (Function.update sizes i 1)
      (isingTorusIndexedField h g)) :
    ∀ r, r ≤ k + 2 →
      ∃ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
        isingTorusShiftedPartition beta (isingTorusIndexedField h g') =
            isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) ∧
          IsingTorusDisseminatedBox (Function.update sizes i (2 ^ r))
            (isingTorusIndexedField h g') := by
  intro r hr
  induction r with
  | zero =>
      refine ⟨g, hg, ?_⟩
      simpa using hbox
  | succ r ihr =>
      have hrle : r ≤ k + 1 := by omega
      obtain ⟨q, hq, hqbox⟩ := ihr (by omega)
      have hpow : 2 ^ r ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by omega) hrle
      obtain ⟨q', hq', hq'box⟩ := isingTorus_indexed_max_box_double
        beta hbeta h gmax q hmax hq sizes i (2 ^ r)
          (pow_pos (by omega) r) hpow hqbox
      refine ⟨q', hq', ?_⟩
      simpa [pow_succ, mul_comm] using hq'box



def isingTorusCompletedBoxSides (k : Nat)
    (S : Finset (Fin d)) (i : Fin d) : Nat :=
  if i ∈ S then 2 ^ (k + 2) else 1

private theorem isingTorus_indexed_max_disseminate_coordinates
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (gmax : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax)) :
    ∀ S : Finset (Fin d),
      ∃ g : IsingDyadicTorus d k → IsingDyadicTorus d k,
        isingTorusShiftedPartition beta (isingTorusIndexedField h g) =
            isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) ∧
          IsingTorusDisseminatedBox (isingTorusCompletedBoxSides k S)
            (isingTorusIndexedField h g) := by
  intro S
  induction S using Finset.induction with
  | empty =>
      refine ⟨gmax, rfl, ?_⟩
      simpa [isingTorusCompletedBoxSides] using
        (isingTorusDisseminatedBox_one (isingTorusIndexedField h gmax))
  | @insert i S hi ih =>
      obtain ⟨g, hg, hbox⟩ := ih
      have hstart : IsingTorusDisseminatedBox
          (Function.update (isingTorusCompletedBoxSides k S) i 1)
          (isingTorusIndexedField h g) := by
        have hsides0 : Function.update (isingTorusCompletedBoxSides k S) i 1 =
            isingTorusCompletedBoxSides k S := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [isingTorusCompletedBoxSides, hi]
          · simp [hji]
        rw [hsides0]
        exact hbox
      obtain ⟨g', hg', hg'box⟩ :=
        isingTorus_indexed_max_disseminate_coordinate beta hbeta h
          gmax g hmax hg (isingTorusCompletedBoxSides k S) i hstart
          (k + 2) (le_refl _)
      refine ⟨g', hg', ?_⟩
      have hsides : Function.update (isingTorusCompletedBoxSides k S) i
          (2 ^ (k + 2)) = isingTorusCompletedBoxSides k (insert i S) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [isingTorusCompletedBoxSides]
        · simp [isingTorusCompletedBoxSides, hji]
      rw [← hsides]
      exact hg'box

theorem isingTorusShiftedPartition_eq_zero_of_constant
    (beta : Real) (h : IsingDyadicTorus d k → Real)
    (hconst : ∀ x, h x = h 0) :
    isingTorusShiftedPartition beta h =
      isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
  unfold isingTorusShiftedPartition
  apply Finset.sum_congr rfl
  intro sigma _
  congr 2
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [hconst x, hconst (x + isingTorusStep i)]
  ring



theorem isingTorus_gaussianDominated
    (beta : Real) (hbeta : 0 ≤ beta) :
    IsingTorusGaussianDominated (d := d) (k := k) beta := by
  intro h
  obtain ⟨gmax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun g : IsingDyadicTorus d k → IsingDyadicTorus d k =>
      isingTorusShiftedPartition beta (isingTorusIndexedField h g))
    Finset.univ_nonempty
  have hmax' : ∀ g : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g) ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h gmax) := by
    intro g
    exact hmax g (by simp)
  obtain ⟨gconst, hgconst, hbox⟩ :=
    isingTorus_indexed_max_disseminate_coordinates beta hbeta h gmax hmax'
      Finset.univ
  have hconst : ∀ x, isingTorusIndexedField h gconst x =
      isingTorusIndexedField h gconst 0 := by
    intro x
    apply hbox x
    intro i
    simpa [isingTorusCompletedBoxSides] using (x i).val_lt
  have hidentity : isingTorusIndexedField h id = h := by rfl
  calc
    isingTorusShiftedPartition beta h =
        isingTorusShiftedPartition beta (isingTorusIndexedField h id) := by
          rw [hidentity]
    _ ≤ isingTorusShiftedPartition beta
        (isingTorusIndexedField h gmax) := hmax' id
    _ = isingTorusShiftedPartition beta
        (isingTorusIndexedField h gconst) := hgconst.symm
    _ = isingTorusShiftedPartition (d := d) (k := k) beta 0 :=
      isingTorusShiftedPartition_eq_zero_of_constant beta _ hconst



theorem isingTorus_addChar_secondMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hdisp : 0 < isingTorusCharacterDispersion chi) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Complex.normSq (∑ x : IsingDyadicTorus d k,
          (isingTorusSpinField sigma x : Complex) * chi x)) ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0 *
        (Fintype.card (IsingDyadicTorus d k) /
          (beta * isingTorusCharacterDispersion chi)) := by
  exact isingTorus_addChar_secondMoment_le beta hbeta
    (isingTorus_gaussianDominated beta hbeta.le) chi hdisp

end StatMech.FrontierA
