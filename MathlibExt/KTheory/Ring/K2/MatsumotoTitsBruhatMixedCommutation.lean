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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiberCentralCoordinate
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootFactorUniqueness
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSpecialLinear
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatLeftTransition
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatRightTransition

/-!
# Mixed commutation in the Tits–Bruhat action

Over a field, proves that left multiplication by upper elementary matrices
commutes with the right adjacent Weyl action on the Tits–Bruhat fibre, and
proves the symmetric left/right statement. Also shows that the central action
commutes with both Weyl actions.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoTitsMonomialExtension
open MatsumotoTitsBruhatFiber
open MatsumotoBruhatLeftTransition
open MatsumotoBruhatRightTransition
open MatsumotoTitsWeylLift

namespace MatsumotoTitsBruhatFiber

section MixedMultiplierInvariance

variable {F : Type u} [Field F] {n : ℕ}

theorem rightWeylMultiplier_leftUpper_invariant
    {k l : Fin n} (hkl : k ⋖ l)
    (u : upperElementarySubgroup (Fin n) F)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    rightWeylMultiplier (F := F) hkl (UpperElementary.toSLHom u * s) =
      rightWeylMultiplier (F := F) hkl s := by
  classical
  have hMidInv : bruhatMiddle (UpperElementary.toSLHom u * s) =
      bruhatMiddle s :=
    bruhatMiddle_upper_left_mul s u
  have hMidEq : (bruhatMiddle (UpperElementary.toSLHom u * s) :
      PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) =
      (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) := by
    exact congrArg (fun t : MonomialSL F (Fin n) =>
        (t : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n))) hMidInv
  by_cases hPos : (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right k <
      (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right l
  · have hPos' : (bruhatMiddle (UpperElementary.toSLHom u * s) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right k <
        (bruhatMiddle (UpperElementary.toSLHom u * s) :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right l := by
      rw [hMidEq]; exact hPos
    by_cases hZs : rightSimpleRootCoeff F n s hkl = 0
    · have hMulS : rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) :=
        rightWeylMultiplier_of_zero hkl s hZs
      by_cases hZt : rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl = 0
      · have hMulT : rightWeylMultiplier hkl (UpperElementary.toSLHom u * s) =
            weylHMTits F n k l hkl.ne (-1) :=
          rightWeylMultiplier_of_zero hkl (UpperElementary.toSLHom u * s) hZt
        rw [hMulS, hMulT]
      · have hMulT : rightWeylMultiplier hkl (UpperElementary.toSLHom u * s) =
            weylHMTits F n k l hkl.ne (-1) :=
          rightWeylMultiplier_of_pos hkl (UpperElementary.toSLHom u * s) hZt hPos'
        rw [hMulS, hMulT]
    · have hMulS : rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) :=
        rightWeylMultiplier_of_pos hkl s hZs hPos
      by_cases hZt : rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl = 0
      · have hMulT : rightWeylMultiplier hkl (UpperElementary.toSLHom u * s) =
            weylHMTits F n k l hkl.ne (-1) :=
          rightWeylMultiplier_of_zero hkl (UpperElementary.toSLHom u * s) hZt
        rw [hMulS, hMulT]
      · have hMulT : rightWeylMultiplier hkl (UpperElementary.toSLHom u * s) =
            weylHMTits F n k l hkl.ne (-1) :=
          rightWeylMultiplier_of_pos hkl (UpperElementary.toSLHom u * s) hZt hPos'
        rw [hMulS, hMulT]
  · have hNeg : (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right l <
        (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right k := by
      have hNe : (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right k ≠
          (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right l := by
        intro heq
        exact hkl.ne
          (Equiv.injective
            (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right
            heq)
      rcases lt_or_gt_of_ne hNe with hLt | hGt
      · exact absurd hLt hPos
      · exact hGt
    have hCoeffEq : rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl =
        rightSimpleRootCoeff F n s hkl := by
      let Ls := Matrix.GeneralLinearGroup.bruhatLeft s
      let Ms := Matrix.GeneralLinearGroup.bruhatMiddle s
      let Rs := Matrix.GeneralLinearGroup.bruhatRight s
      have hFactS : s = UpperElementary.toSLHom Ls *
          monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs :=
        Matrix.GeneralLinearGroup.bruhat_factorizationSL s
      have hFactT : UpperElementary.toSLHom u * s =
          UpperElementary.toSLHom (u * Ls) *
            monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs := by
        calc UpperElementary.toSLHom u * s
            = UpperElementary.toSLHom u *
                (UpperElementary.toSLHom Ls *
                  monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs) := by rw [hFactS]
          _ = UpperElementary.toSLHom u * UpperElementary.toSLHom Ls *
                monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs := by
              simp only [mul_assoc]
          _ = UpperElementary.toSLHom (u * Ls) *
                monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs := by
              rw [← map_mul]
      have hEqT : ((Rs : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l =
          (((Matrix.GeneralLinearGroup.bruhatRight (UpperElementary.toSLHom u * s) :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) :=
        Matrix.GeneralLinearGroup.SL_rightEntry_eq_bruhatRight_of_permNeg hFactT hkl hNeg
      have hEqS : ((Rs : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l =
          (((Matrix.GeneralLinearGroup.bruhatRight s :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) :=
        Matrix.GeneralLinearGroup.SL_rightEntry_eq_bruhatRight_of_permNeg hFactS hkl hNeg
      have hBruhatEq : (((Matrix.GeneralLinearGroup.bruhatRight (UpperElementary.toSLHom u * s) :
          Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) =
          (((Matrix.GeneralLinearGroup.bruhatRight s :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
        calc (((Matrix.GeneralLinearGroup.bruhatRight (UpperElementary.toSLHom u * s) :
            Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)
            = ((Rs : Matrix.GeneralLinearGroup (Fin n) F) :
                Matrix (Fin n) (Fin n) F) k l := hEqT.symm
          _ = (((Matrix.GeneralLinearGroup.bruhatRight s :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := hEqS
      change rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl =
          rightSimpleRootCoeff F n s hkl
      simp only [rightSimpleRootCoeff] at hBruhatEq ⊢
      exact hBruhatEq
    have hNotPos : ¬ (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right k <
        (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right l := hPos
    have hNotPos' : ¬ (bruhatMiddle (UpperElementary.toSLHom u * s) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right k <
        (bruhatMiddle (UpperElementary.toSLHom u * s) :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right l := by
      rw [hMidEq]; exact hPos
    by_cases hZs : rightSimpleRootCoeff F n s hkl = 0
    · have hZt : rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl = 0 := by
        rw [hCoeffEq]; exact hZs
      rw [rightWeylMultiplier_of_zero hkl s hZs,
        rightWeylMultiplier_of_zero hkl (UpperElementary.toSLHom u * s) hZt]
    · have hZtNe : rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl ≠ 0 := by
        rw [hCoeffEq]; exact hZs
      have hMulS : rightWeylMultiplier hkl s =
          hTits F n k l hkl.ne (torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hZs) :=
        rightWeylMultiplier_of_neg hkl s hZs hNotPos
      have hMulT : rightWeylMultiplier hkl (UpperElementary.toSLHom u * s) =
          hTits F n k l hkl.ne
            (torusUnitOfCoeff
              (rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl) hZtNe) :=
        rightWeylMultiplier_of_neg hkl (UpperElementary.toSLHom u * s) hZtNe hNotPos'
      have hUnitsEq :
          torusUnitOfCoeff (rightSimpleRootCoeff F n (UpperElementary.toSLHom u * s) hkl) hZtNe =
          torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hZs := by
        apply Units.ext
        simp only [torusUnitOfCoeff_val]
        rw [hCoeffEq]
      rw [hMulS, hMulT, hUnitsEq]

theorem leftWeylMultiplier_rightUpper_invariant
    {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (u : upperElementarySubgroup (Fin n) F) :
    leftWeylMultiplier (F := F) hij (s * UpperElementary.toSLHom u) =
      leftWeylMultiplier (F := F) hij s := by
  classical
  have hMidInv : bruhatMiddle (s * UpperElementary.toSLHom u) =
      bruhatMiddle s :=
    bruhatMiddle_upper_right_mul s u
  have hMidEq : (bruhatMiddle (s * UpperElementary.toSLHom u) :
      PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) =
      (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) := by
    exact congrArg (fun t : MonomialSL F (Fin n) =>
        (t : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n))) hMidInv
  by_cases hPos :
      (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j
  · have hPos' : (bruhatMiddle (s * UpperElementary.toSLHom u) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (s * UpperElementary.toSLHom u) :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j := by
      rw [hMidEq]; exact hPos
    by_cases hZs : leftSimpleRootCoeff F n s hij = 0
    · have hMulS : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 :=
        leftWeylMultiplier_of_zero hij s hZs
      by_cases hZt : leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij = 0
      · have hMulT : leftWeylMultiplier hij (s * UpperElementary.toSLHom u) =
            weylHMTits F n i j hij.ne 1 :=
          leftWeylMultiplier_of_zero hij (s * UpperElementary.toSLHom u) hZt
        rw [hMulS, hMulT]
      · have hMulT : leftWeylMultiplier hij (s * UpperElementary.toSLHom u) =
            weylHMTits F n i j hij.ne 1 :=
          leftWeylMultiplier_of_pos hij (s * UpperElementary.toSLHom u) hZt hPos'
        rw [hMulS, hMulT]
    · have hMulS : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 :=
        leftWeylMultiplier_of_pos hij s hZs hPos
      by_cases hZt : leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij = 0
      · have hMulT : leftWeylMultiplier hij (s * UpperElementary.toSLHom u) =
            weylHMTits F n i j hij.ne 1 :=
          leftWeylMultiplier_of_zero hij (s * UpperElementary.toSLHom u) hZt
        rw [hMulS, hMulT]
      · have hMulT : leftWeylMultiplier hij (s * UpperElementary.toSLHom u) =
            weylHMTits F n i j hij.ne 1 :=
          leftWeylMultiplier_of_pos hij (s * UpperElementary.toSLHom u) hZt hPos'
        rw [hMulS, hMulT]
  · have hNeg : (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j <
        (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i := by
      have hNe :
          (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i ≠
          (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j := by
        intro heq
        exact hij.ne
          (Equiv.injective
            (bruhatMiddle s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm
            heq)
      rcases lt_or_gt_of_ne hNe with hLt | hGt
      · exact absurd hLt hPos
      · exact hGt
    have hCoeffEq : leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij =
        leftSimpleRootCoeff F n s hij := by
      let Ls := Matrix.GeneralLinearGroup.bruhatLeft s
      let Ms := Matrix.GeneralLinearGroup.bruhatMiddle s
      let Rs := Matrix.GeneralLinearGroup.bruhatRight s
      have hFactS : s = UpperElementary.toSLHom Ls *
          monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs :=
        Matrix.GeneralLinearGroup.bruhat_factorizationSL s
      have hFactT : s * UpperElementary.toSLHom u =
          UpperElementary.toSLHom Ls *
            monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom (Rs * u) := by
        calc s * UpperElementary.toSLHom u
            = (UpperElementary.toSLHom Ls *
                monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom Rs) *
                UpperElementary.toSLHom u := by rw [hFactS]
          _ = UpperElementary.toSLHom Ls *
                monomialSLHom F (Fin n) Ms *
                (UpperElementary.toSLHom Rs * UpperElementary.toSLHom u) := by
              simp only [mul_assoc]
          _ = UpperElementary.toSLHom Ls *
                monomialSLHom F (Fin n) Ms * UpperElementary.toSLHom (Rs * u) := by
              rw [← map_mul]
      have hEqT : ((Ls : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
          (((Matrix.GeneralLinearGroup.bruhatLeft (s * UpperElementary.toSLHom u) :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) :=
        Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg hFactT hij hNeg
      have hEqS : ((Ls : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
          (((Matrix.GeneralLinearGroup.bruhatLeft s :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) :=
        Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg hFactS hij hNeg
      have hBruhatEq : (((Matrix.GeneralLinearGroup.bruhatLeft (s * UpperElementary.toSLHom u) :
          Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) =
          (((Matrix.GeneralLinearGroup.bruhatLeft s :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := by
        calc (((Matrix.GeneralLinearGroup.bruhatLeft (s * UpperElementary.toSLHom u) :
            Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)
            = ((Ls : Matrix.GeneralLinearGroup (Fin n) F) :
                Matrix (Fin n) (Fin n) F) i j := hEqT.symm
          _ = (((Matrix.GeneralLinearGroup.bruhatLeft s :
              Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := hEqS
      change leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij =
          leftSimpleRootCoeff F n s hij
      simp only [leftSimpleRootCoeff] at hBruhatEq ⊢
      exact hBruhatEq
    have hNotPos :
        ¬ (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle s : PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j := hPos
    have hNotPos' : ¬ (bruhatMiddle (s * UpperElementary.toSLHom u) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (s * UpperElementary.toSLHom u) :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j := by
      rw [hMidEq]; exact hPos
    by_cases hZs : leftSimpleRootCoeff F n s hij = 0
    · have hZt : leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij = 0 := by
        rw [hCoeffEq]; exact hZs
      rw [leftWeylMultiplier_of_zero hij s hZs,
        leftWeylMultiplier_of_zero hij (s * UpperElementary.toSLHom u) hZt]
    · have hZtNe : leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij ≠ 0 := by
        rw [hCoeffEq]; exact hZs
      have hMulS : leftWeylMultiplier hij s =
          (hTits F n i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZs))⁻¹ :=
        leftWeylMultiplier_of_neg hij s hZs hNotPos
      have hMulT : leftWeylMultiplier hij (s * UpperElementary.toSLHom u) =
          (hTits F n i j hij.ne
            (torusUnitOfNegCoeff
              (leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij) hZtNe))⁻¹ :=
        leftWeylMultiplier_of_neg hij (s * UpperElementary.toSLHom u) hZtNe hNotPos'
      have hUnitsEq :
          torusUnitOfNegCoeff (leftSimpleRootCoeff F n (s * UpperElementary.toSLHom u) hij) hZtNe =
          torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZs := by
        apply Units.ext
        simp only [torusUnitOfNegCoeff_val]
        rw [hCoeffEq]
      rw [hMulS, hMulT, hUnitsEq]

end MixedMultiplierInvariance

section MixedPermutationCommutation

variable {F : Type u} [Field F] {n : ℕ}

theorem leftUpperPerm_rightWeylPerm_comm
    {k l : Fin n} (hkl : k ⋖ l)
    (u : upperElementarySubgroup (Fin n) F) :
    leftUpperPerm (F := F) u * rightWeylPerm hkl =
      rightWeylPerm hkl * leftUpperPerm (F := F) u := by
  apply Equiv.ext
  intro x
  have hInv := rightWeylMultiplier_leftUpper_invariant (F := F) hkl u (X.fst x)
  have hComm : leftUpper (F := F) u (rightWeylPerm hkl x) =
      rightWeylPerm hkl (leftUpper (F := F) u x) := by
    apply X.ext
    · simp [leftUpper_fst, rightWeylPerm_fst, mul_assoc]
    · simp [leftUpper_snd, rightWeylPerm_snd, hInv]
  simp only [Equiv.Perm.mul_apply, leftUpperPerm_apply, hComm]

theorem leftWeylPerm_rightUpperPerm_comm
    {i j : Fin n} (hij : i ⋖ j)
    (u : upperElementarySubgroup (Fin n) F) :
    leftWeylPerm (F := F) hij * rightUpperPerm (F := F) u =
      rightUpperPerm (F := F) u * leftWeylPerm (F := F) hij := by
  apply Equiv.ext
  intro x
  have hInv := leftWeylMultiplier_rightUpper_invariant (F := F) hij (X.fst x) u
  have hComm : leftWeylPerm (F := F) hij (rightUpper (F := F) u x) =
      rightUpper (F := F) u (leftWeylPerm (F := F) hij x) := by
    apply X.ext
    · simp [rightUpper_fst, leftWeylPerm_fst, mul_assoc]
    · simp [rightUpper_snd, leftWeylPerm_snd, hInv]
  simp only [Equiv.Perm.mul_apply, rightUpperPerm_apply, hComm]

end MixedPermutationCommutation

section CentralWeylCommutation

variable {F : Type u} [Field F] {n : ℕ}

theorem centralPerm_leftWeylPerm_comm
    {i j : Fin n} (hij : i ⋖ j)
    (c : Multiplicative (MilnorK F 2)) :
    centralPerm (F := F) c * leftWeylPerm hij =
      leftWeylPerm hij * centralPerm (F := F) c := by
  apply Equiv.ext
  intro x
  have hComm : central (F := F) c (leftWeylPerm hij x) =
      leftWeylPerm hij (central (F := F) c x) := by
    apply X.ext
    · simp [central_fst, leftWeylPerm_fst]
    · simp [central_snd, leftWeylPerm_snd, mul_assoc, inlHom_central_tits]
  simp only [Equiv.Perm.mul_apply, centralPerm_apply]
  exact hComm

theorem centralPerm_rightWeylPerm_comm
    {i j : Fin n} (hij : i ⋖ j)
    (c : Multiplicative (MilnorK F 2)) :
    centralPerm (F := F) c * rightWeylPerm hij =
      rightWeylPerm hij * centralPerm (F := F) c := by
  apply Equiv.ext
  intro x
  have hComm : central (F := F) c (rightWeylPerm hij x) =
      rightWeylPerm hij (central (F := F) c x) := by
    apply X.ext
    · simp [central_fst, rightWeylPerm_fst]
    · simp [central_snd, rightWeylPerm_snd, mul_assoc]
  simp only [Equiv.Perm.mul_apply, centralPerm_apply]
  exact hComm

end CentralWeylCommutation

end MatsumotoTitsBruhatFiber

end
