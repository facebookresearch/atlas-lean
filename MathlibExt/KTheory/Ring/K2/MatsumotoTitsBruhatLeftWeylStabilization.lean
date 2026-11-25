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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatWeylAction
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsWeylStabilization
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootStabilization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMiddleStabilization

/-!
# Stabilization of left Weyl actions on Bruhat fibers

Successor stabilization of finite permutations preserves the
inverse-permutation comparisons used to choose left Weyl multipliers. These
comparisons identify the stabilized Tits multiplier and show that stabilization
of a Bruhat fiber commutes with its left Weyl permutation for adjacent indices.
-/

@[expose] public section

universe u

open PermutationBilinearTitsStabilization
open PermutationBilinearCocycle
open Matrix.GeneralLinearGroup
open Matrix.SpecialLinearGroup
open MatsumotoTitsMonomialExtension
open MatsumotoTitsBruhatFiber
open MatsumotoBruhatLeftTransition
open MatsumotoTitsWeylLift

namespace MatsumotoTitsBruhatFiber

variable {F : Type u} [Field F] {n : ℕ}

section Helpers

theorem permSuccHom_symm_castSucc {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (permSuccHom (n := n) σ).symm (Fin.castSucc i) =
      Fin.castSucc (σ.symm i) := by
  calc (permSuccHom (n := n) σ).symm (Fin.castSucc i)
      = (permSuccHom (n := n) σ)⁻¹ (Fin.castSucc i) := rfl
    _ = (permSuccHom (n := n) (σ⁻¹)) (Fin.castSucc i) := by
        rw [permSuccHom_inv]
    _ = Fin.castSucc ((σ⁻¹) i) := by
        rw [permSuccHom_apply_castSucc]
    _ = Fin.castSucc (σ.symm i) := rfl

theorem permSuccHom_symm_castSucc_lt_iff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    ((permSuccHom (n := n) σ).symm (Fin.castSucc i) <
      (permSuccHom (n := n) σ).symm (Fin.castSucc j) ↔
      σ.symm i < σ.symm j) := by
  rw [permSuccHom_symm_castSucc, permSuccHom_symm_castSucc,
    Fin.castSucc_lt_castSucc_iff]

theorem monomialSLSuccHom_right_symm_castSucc {R : Type u} [CommRing R] {n : ℕ}
    (M : MonomialSL R (Fin n)) (i : Fin n) :
    (monomialSLSuccHom (R := R) M :
      MonomialBase Rˣ (Fin (n + 1))).right.symm (Fin.castSucc i) =
      Fin.castSucc ((M : MonomialBase Rˣ (Fin n)).right.symm i) := by
  have h_coe :
      (monomialSLSuccHom (R := R) M :
        MonomialBase Rˣ (Fin (n + 1))) =
      monomialSuccHom (n := n) (A := Rˣ)
        (M : MonomialBase Rˣ (Fin n)) :=
    coe_monomialSLSuccHom M
  have h_right :
      (monomialSuccHom (n := n) (A := Rˣ)
        (M : MonomialBase Rˣ (Fin n))).right =
      permSuccHom (n := n) ((M : MonomialBase Rˣ (Fin n)).right) :=
    monomialSuccHom_right _
  calc (monomialSLSuccHom (R := R) M :
        MonomialBase Rˣ (Fin (n + 1))).right.symm (Fin.castSucc i)
      = (monomialSuccHom (n := n) (A := Rˣ)
          (M : MonomialBase Rˣ (Fin n))).right.symm (Fin.castSucc i) := by
          rw [← h_coe]
    _ = (permSuccHom (n := n)
          ((M : MonomialBase Rˣ (Fin n)).right)).symm
          (Fin.castSucc i) := by rw [h_right]
    _ = Fin.castSucc ((M : MonomialBase Rˣ (Fin n)).right.symm i) := by
          rw [permSuccHom_symm_castSucc]

theorem weylMonomialSLUnit_right_perm {R : Type u} [CommRing R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (u : Rˣ) :
    (weylMonomialSLUnit (R := R) i j hij u :
      MonomialBase Rˣ (Fin n)).right = Equiv.swap i j := by
  simp [weylMonomialSLUnit, weylMonomialBaseUnit, weylPerm]

theorem torusMonomialSLUnit_right_perm {R : Type u} [CommRing R] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (u : Rˣ) :
    (torusMonomialSLUnit (R := R) i j hij u :
      MonomialBase Rˣ (Fin n)).right = 1 := by
  simp [torusMonomialSLUnit, torusMonomialBaseUnit, torusPerm]

theorem weyl_swap_ne_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Equiv.swap i j ≠ (1 : Equiv.Perm (Fin n)) := by
  intro h
  have h1 : (Equiv.swap i j) i = (1 : Equiv.Perm (Fin n)) i :=
    congrFun (congrArg Equiv.toFun h) i
  have h_swap : (Equiv.swap i j) i = j :=
    Equiv.swap_apply_left i j
  have h_one : (1 : Equiv.Perm (Fin n)) i = i := rfl
  rw [h_swap, h_one] at h1
  exact hij h1.symm

theorem swap_mul_ne_self
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (σ : Equiv.Perm (Fin n)) :
    Equiv.swap i j * σ ≠ σ := by
  intro h
  have h_eq : Equiv.swap i j = 1 := by
    calc Equiv.swap i j
        = Equiv.swap i j * σ * σ⁻¹ := by simp
      _ = σ * σ⁻¹ := by rw [h]
      _ = 1 := by simp
  exact weyl_swap_ne_one hij h_eq

theorem torusMonomialSLUnit_injective {R : Type u} [CommRing R] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (torusMonomialSLUnit (R := R) i j hij) := by
  intro u v h
  have h_base :
      (torusMonomialSLUnit (R := R) i j hij u :
        MonomialBase Rˣ (Fin n)) =
      (torusMonomialSLUnit (R := R) i j hij v :
        MonomialBase Rˣ (Fin n)) :=
    congrArg Subtype.val h
  have h_left :
      (torusMonomialSLUnit (R := R) i j hij u :
        MonomialBase Rˣ (Fin n)).left =
      (torusMonomialSLUnit (R := R) i j hij v :
        MonomialBase Rˣ (Fin n)).left :=
    congrArg SemidirectProduct.left h_base
  have h_eq_at_i :
      (torusMonomialSLUnit (R := R) i j hij u :
        MonomialBase Rˣ (Fin n)).left i =
      (torusMonomialSLUnit (R := R) i j hij v :
        MonomialBase Rˣ (Fin n)).left i :=
    congrFun h_left i
  simp only [torusMonomialSLUnit, torusMonomialBaseUnit,
    torusWeightUnit] at h_eq_at_i
  exact h_eq_at_i

end Helpers

section Endpoint1

theorem bruhatMiddle_stabilization_right_symm_castSucc_lt_iff
    {i j : Fin n} (_hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    (bruhatMiddle (stabilization F s) :
        MonomialBase Fˣ (Fin (n + 1))).right.symm (Fin.castSucc i) <
      (bruhatMiddle (stabilization F s) :
        MonomialBase Fˣ (Fin (n + 1))).right.symm (Fin.castSucc j) ↔
     (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
       (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
  have h_stab : bruhatMiddle (stabilization F s) =
      monomialSLSuccHom (R := F) (bruhatMiddle s) :=
    bruhatMiddle_stabilization s
  have h_eq :
      (bruhatMiddle (stabilization F s) :
        MonomialBase Fˣ (Fin (n + 1))).right.symm (Fin.castSucc i) =
      Fin.castSucc ((bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm i) := by
    calc (bruhatMiddle (stabilization F s) :
        MonomialBase Fˣ (Fin (n + 1))).right.symm (Fin.castSucc i)
        = (monomialSLSuccHom (R := F) (bruhatMiddle s) :
            MonomialBase Fˣ (Fin (n + 1))).right.symm
            (Fin.castSucc i) := by rw [h_stab]
      _ = Fin.castSucc ((bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm i) :=
          monomialSLSuccHom_right_symm_castSucc
            (M := bruhatMiddle s) i
  have h_eq_j :
      (bruhatMiddle (stabilization F s) :
        MonomialBase Fˣ (Fin (n + 1))).right.symm (Fin.castSucc j) =
      Fin.castSucc ((bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm j) := by
    calc (bruhatMiddle (stabilization F s) :
        MonomialBase Fˣ (Fin (n + 1))).right.symm (Fin.castSucc j)
        = (monomialSLSuccHom (R := F) (bruhatMiddle s) :
            MonomialBase Fˣ (Fin (n + 1))).right.symm
            (Fin.castSucc j) := by rw [h_stab]
      _ = Fin.castSucc ((bruhatMiddle s :
            MonomialBase Fˣ (Fin n)).right.symm j) :=
          monomialSLSuccHom_right_symm_castSucc
            (M := bruhatMiddle s) j
  rw [h_eq, h_eq_j, Fin.castSucc_lt_castSucc_iff]

end Endpoint1

section Endpoint2

private theorem transport_weyl_mid
    {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hMid : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s) :
    bruhatMiddle
        (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne (1 : Fˣ) *
          stabilization F s) =
      weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne (1 : Fˣ) *
        bruhatMiddle (stabilization F s) := by
  let w : Matrix.SpecialLinearGroup (Fin n) F :=
    weylSLUnit i j hij.ne (1 : Fˣ)
  let wSucc : Matrix.SpecialLinearGroup (Fin (n + 1)) F :=
    weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
      (Fin.castSucc_covBy hij).ne (1 : Fˣ)
  let M : MonomialSL F (Fin n) := bruhatMiddle s
  let Ms : MonomialSL F (Fin (n + 1)) :=
    bruhatMiddle (stabilization F s)
  have hMs : Ms = monomialSLSuccHom (R := F) M :=
    bruhatMiddle_stabilization s
  have hwStab : stabilization F w = wSucc :=
    stabilization_weylSLUnit (R := F) hij.ne (1 : Fˣ)
  have hwMulStab :
      stabilization F (w * s) = wSucc * stabilization F s := by
    calc stabilization F (w * s)
        = stabilization F w * stabilization F s := by rw [map_mul]
      _ = wSucc * stabilization F s := by rw [hwStab]
  have hMidStab :
      bruhatMiddle (stabilization F (w * s)) =
      monomialSLSuccHom (R := F) (bruhatMiddle (w * s)) :=
    bruhatMiddle_stabilization (w * s)
  calc bruhatMiddle (wSucc * stabilization F s)
      = bruhatMiddle (stabilization F (w * s)) := by
          rw [← hwMulStab]
    _ = monomialSLSuccHom (R := F) (bruhatMiddle (w * s)) :=
          hMidStab
    _ = monomialSLSuccHom (R := F)
          (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * M) := by
          rw [hMid]
    _ = monomialSLSuccHom (R := F)
          (weylMonomialSLUnit i j hij.ne (1 : Fˣ)) *
          monomialSLSuccHom (R := F) M := by rw [map_mul]
    _ = weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne (1 : Fˣ) * Ms := by
          rw [monomialSLSuccHom_weylMonomialSLUnit hij.ne (1 : Fˣ), hMs]

private theorem transport_torus_mid
    {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) (v : Fˣ)
    (hMid : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      (torusMonomialSLUnit i j hij.ne v)⁻¹ * bruhatMiddle s) :
    bruhatMiddle
        (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne (1 : Fˣ) *
          stabilization F s) =
      (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne v)⁻¹ *
        bruhatMiddle (stabilization F s) := by
  let w : Matrix.SpecialLinearGroup (Fin n) F :=
    weylSLUnit i j hij.ne (1 : Fˣ)
  let wSucc : Matrix.SpecialLinearGroup (Fin (n + 1)) F :=
    weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
      (Fin.castSucc_covBy hij).ne (1 : Fˣ)
  let M : MonomialSL F (Fin n) := bruhatMiddle s
  let Ms : MonomialSL F (Fin (n + 1)) :=
    bruhatMiddle (stabilization F s)
  have hMs : Ms = monomialSLSuccHom (R := F) M :=
    bruhatMiddle_stabilization s
  have hwStab : stabilization F w = wSucc :=
    stabilization_weylSLUnit (R := F) hij.ne (1 : Fˣ)
  have hwMulStab :
      stabilization F (w * s) = wSucc * stabilization F s := by
    calc stabilization F (w * s)
        = stabilization F w * stabilization F s := by rw [map_mul]
      _ = wSucc * stabilization F s := by rw [hwStab]
  have hMidStab :
      bruhatMiddle (stabilization F (w * s)) =
      monomialSLSuccHom (R := F) (bruhatMiddle (w * s)) :=
    bruhatMiddle_stabilization (w * s)
  calc bruhatMiddle (wSucc * stabilization F s)
      = bruhatMiddle (stabilization F (w * s)) := by
          rw [← hwMulStab]
    _ = monomialSLSuccHom (R := F) (bruhatMiddle (w * s)) :=
          hMidStab
    _ = monomialSLSuccHom (R := F)
          ((torusMonomialSLUnit i j hij.ne v)⁻¹ * M) := by
          rw [hMid]
    _ = (monomialSLSuccHom (R := F)
          (torusMonomialSLUnit i j hij.ne v))⁻¹ *
          monomialSLSuccHom (R := F) M := by
          rw [map_mul, map_inv]
    _ = (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne v)⁻¹ * Ms := by
          rw [monomialSLSuccHom_torusMonomialSLUnit hij.ne v, hMs]

private theorem right_eq_weyl_vs_torus_contradiction
    {n' : ℕ} {i' j' : Fin n'} (hij' : i' ≠ j')
    (M : MonomialSL F (Fin n')) (v : Fˣ)
    (hEq : weylMonomialSLUnit i' j' hij' (1 : Fˣ) * M =
      (torusMonomialSLUnit i' j' hij' v)⁻¹ * M) : False := by
  have h_right_eq :
      ((weylMonomialSLUnit i' j' hij' (1 : Fˣ) * M :
        MonomialSL F (Fin n')) :
      MonomialBase Fˣ (Fin n')).right =
      (((torusMonomialSLUnit i' j' hij' v)⁻¹ * M :
        MonomialSL F (Fin n')) :
      MonomialBase Fˣ (Fin n')).right :=
    congrArg
      (fun x : MonomialSL F (Fin n') =>
        (x : MonomialBase Fˣ (Fin n')).right) hEq
  have h_weyl_right :
      (weylMonomialSLUnit i' j' hij' (1 : Fˣ) :
        MonomialBase Fˣ (Fin n')).right = Equiv.swap i' j' :=
    weylMonomialSLUnit_right_perm i' j' hij' (1 : Fˣ)
  have h_torus_right :
      (torusMonomialSLUnit i' j' hij' v :
        MonomialBase Fˣ (Fin n')).right = 1 :=
    torusMonomialSLUnit_right_perm i' j' hij' v
  have h_torus_inv_right :
      ((torusMonomialSLUnit i' j' hij' v :
        MonomialSL F (Fin n'))⁻¹ :
      MonomialBase Fˣ (Fin n')).right = 1 := by
    have h_inv :
        ((torusMonomialSLUnit i' j' hij' v :
          MonomialSL F (Fin n'))⁻¹ :
        MonomialBase Fˣ (Fin n')).right =
        ((torusMonomialSLUnit i' j' hij' v :
          MonomialBase Fˣ (Fin n')).right)⁻¹ := rfl
    rw [h_inv, h_torus_right, inv_one]
  have h_mul_weyl :
      ((weylMonomialSLUnit i' j' hij' (1 : Fˣ) * M :
        MonomialSL F (Fin n')) :
      MonomialBase Fˣ (Fin n')).right =
      Equiv.swap i' j' * (M : MonomialBase Fˣ (Fin n')).right := by
    calc ((weylMonomialSLUnit i' j' hij' (1 : Fˣ) * M :
        MonomialSL F (Fin n')) :
        MonomialBase Fˣ (Fin n')).right
        = (weylMonomialSLUnit i' j' hij' (1 : Fˣ) :
            MonomialBase Fˣ (Fin n')).right *
          (M : MonomialBase Fˣ (Fin n')).right := rfl
      _ = Equiv.swap i' j' * (M : MonomialBase Fˣ (Fin n')).right := by
          rw [h_weyl_right]
  have h_mul_torus :
      (((torusMonomialSLUnit i' j' hij' v)⁻¹ * M :
        MonomialSL F (Fin n')) :
      MonomialBase Fˣ (Fin n')).right =
      (M : MonomialBase Fˣ (Fin n')).right := by
    calc (((torusMonomialSLUnit i' j' hij' v)⁻¹ * M :
        MonomialSL F (Fin n')) :
        MonomialBase Fˣ (Fin n')).right
        = ((torusMonomialSLUnit i' j' hij' v :
            MonomialSL F (Fin n'))⁻¹ :
            MonomialBase Fˣ (Fin n')).right *
          (M : MonomialBase Fˣ (Fin n')).right := rfl
      _ = (1 : Equiv.Perm (Fin n')) *
          (M : MonomialBase Fˣ (Fin n')).right := by
          rw [h_torus_inv_right]
      _ = (M : MonomialBase Fˣ (Fin n')).right := by simp
  rw [h_mul_weyl, h_mul_torus] at h_right_eq
  exact swap_mul_ne_self hij' _ h_right_eq

theorem leftWeylMultiplier_stabilization
    {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    HMTitsSuccHom F n (leftWeylMultiplier hij s) =
      leftWeylMultiplier (Fin.castSucc_covBy hij)
        (stabilization F s) := by
  classical
  let hijSucc := Fin.castSucc_covBy hij
  let sSucc := stabilization F s
  have hSource := bruhatLeftTransition_cases hij s
  have hTarget := bruhatLeftTransition_cases hijSucc sSucc
  rcases hSource with hZero | hPos | hNeg
  · obtain ⟨hZeroCoeff, hMidWeyl⟩ := hZero
    have hMidSuccWeyl :
        bruhatMiddle (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          hijSucc.ne (1 : Fˣ) * sSucc) =
        weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc :=
      transport_weyl_mid hij s hMidWeyl
    have hLeftZero :
        leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 :=
      leftWeylMultiplier_of_zero hij s hZeroCoeff
    have hTargetNotNeg : ∀ w : Fˣ,
        bruhatMiddle
            (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
              hijSucc.ne (1 : Fˣ) * sSucc) ≠
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w)⁻¹ * bruhatMiddle sSucc := by
      intro w hEq
      have hEq' :
          weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc =
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w)⁻¹ * bruhatMiddle sSucc := by
        rw [← hMidSuccWeyl, hEq]
      exact right_eq_weyl_vs_torus_contradiction
        hijSucc.ne _ w hEq'
    rcases hTarget with hZeroT | hPosT | hNegT
    · obtain ⟨hZeroTCoeff, _⟩ := hZeroT
      have hLeftSucc :
          leftWeylMultiplier hijSucc sSucc =
          weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne 1 :=
        leftWeylMultiplier_of_zero hijSucc sSucc hZeroTCoeff
      rw [hLeftZero, hLeftSucc, HMTitsSuccHom_weylHMTits]
    · obtain ⟨hPosPerm, _⟩ := hPosT
      have hLeftSucc :
          leftWeylMultiplier hijSucc sSucc =
          weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne 1 := by
        by_cases hZeroT :
            leftSimpleRootCoeff F (n + 1) sSucc hijSucc = 0
        · exact leftWeylMultiplier_of_zero hijSucc sSucc hZeroT
        · exact leftWeylMultiplier_of_pos hijSucc sSucc hZeroT hPosPerm
      rw [hLeftZero, hLeftSucc, HMTitsSuccHom_weylHMTits]
    · obtain ⟨w, hw, _, hMidNegT⟩ := hNegT
      exfalso; exact hTargetNotNeg w hMidNegT
  · obtain ⟨hPosPerm, hMidWeyl⟩ := hPos
    have hMidSuccWeyl :
        bruhatMiddle (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          hijSucc.ne (1 : Fˣ) * sSucc) =
        weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc :=
      transport_weyl_mid hij s hMidWeyl
    have hTargetNotNeg : ∀ w : Fˣ,
        bruhatMiddle
            (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
              hijSucc.ne (1 : Fˣ) * sSucc) ≠
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w)⁻¹ * bruhatMiddle sSucc := by
      intro w hEq
      have hEq' :
          weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc =
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w)⁻¹ * bruhatMiddle sSucc := by
        rw [← hMidSuccWeyl, hEq]
      exact right_eq_weyl_vs_torus_contradiction
        hijSucc.ne _ w hEq'
    have hLeftPos :
        leftWeylMultiplier hij s =
        weylHMTits F n i j hij.ne 1 := by
      by_cases hZero : leftSimpleRootCoeff F n s hij = 0
      · exact leftWeylMultiplier_of_zero hij s hZero
      · exact leftWeylMultiplier_of_pos hij s hZero hPosPerm
    rcases hTarget with hZeroT | hPosT | hNegT
    · obtain ⟨hZeroTCoeff, _⟩ := hZeroT
      have hLeftSucc :
          leftWeylMultiplier hijSucc sSucc =
          weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne 1 :=
        leftWeylMultiplier_of_zero hijSucc sSucc hZeroTCoeff
      rw [hLeftPos, hLeftSucc, HMTitsSuccHom_weylHMTits]
    · obtain ⟨hPosPermT, _⟩ := hPosT
      have hLeftSucc :
          leftWeylMultiplier hijSucc sSucc =
          weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne 1 := by
        by_cases hZeroT :
            leftSimpleRootCoeff F (n + 1) sSucc hijSucc = 0
        · exact leftWeylMultiplier_of_zero hijSucc sSucc hZeroT
        · exact leftWeylMultiplier_of_pos hijSucc sSucc hZeroT hPosPermT
      rw [hLeftPos, hLeftSucc, HMTitsSuccHom_weylHMTits]
    · obtain ⟨w, hw, _, hMidNegT⟩ := hNegT
      exfalso; exact hTargetNotNeg w hMidNegT
  · obtain ⟨v, hv, hNegPerm, hMidNeg⟩ := hNeg
    have hMidSuccTorus :
        bruhatMiddle (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          hijSucc.ne (1 : Fˣ) * sSucc) =
        (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
          hijSucc.ne v)⁻¹ * bruhatMiddle sSucc :=
      transport_torus_mid hij s v hMidNeg
    have hZeroNe : leftSimpleRootCoeff F n s hij ≠ 0 := by
      intro hZeroEq; rw [hZeroEq] at hv; simp at hv
    have hLeftNeg :
        leftWeylMultiplier hij s =
        (hTits F n i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZeroNe))⁻¹ := by
      have hNotPos :
          ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
            (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
        intro hPos
        have hNeg' :
            (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
            (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i :=
          hNegPerm
        exact absurd hPos (not_lt.mpr (le_of_lt hNeg'))
      exact leftWeylMultiplier_of_neg hij s hZeroNe hNotPos
    have hvEq :
        v = torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZeroNe :=
      torusUnitOfNegCoeff_unique _ hZeroNe v hv
    have hTargetNotWeyl :
        ∀ hMidWeylT :
          bruhatMiddle
              (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
                hijSucc.ne (1 : Fˣ) * sSucc) =
          weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc, False := by
      intro hMidWeylT
      have hEq :
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne v)⁻¹ * bruhatMiddle sSucc =
          weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc := by
        rw [← hMidSuccTorus, hMidWeylT]
      have hEq' :
          weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * bruhatMiddle sSucc =
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne v)⁻¹ * bruhatMiddle sSucc :=
        hEq.symm
      exact right_eq_weyl_vs_torus_contradiction hijSucc.ne _ v hEq'
    rcases hTarget with hZeroT | hPosT | hNegT
    · obtain ⟨_, hMidWeylT⟩ := hZeroT
      exfalso; exact hTargetNotWeyl hMidWeylT
    · obtain ⟨_, hMidWeylT⟩ := hPosT
      exfalso; exact hTargetNotWeyl hMidWeylT
    · obtain ⟨w, hw, hNegPermT, hMidNegT⟩ := hNegT
      have hZeroNeT :
          leftSimpleRootCoeff F (n + 1) sSucc hijSucc ≠ 0 := by
        intro hZeroEq; rw [hZeroEq] at hw; simp at hw
      have hLeftNegT :
          leftWeylMultiplier hijSucc sSucc =
          (hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne
            (torusUnitOfNegCoeff
              (leftSimpleRootCoeff F (n + 1) sSucc hijSucc) hZeroNeT))⁻¹ := by
        have hNotPosT :
            ¬ (bruhatMiddle sSucc :
                MonomialBase Fˣ (Fin (n + 1))).right.symm
                (Fin.castSucc i) <
              (bruhatMiddle sSucc :
                MonomialBase Fˣ (Fin (n + 1))).right.symm
                (Fin.castSucc j) := by
          intro hPosT
          have hNeg' :
              (bruhatMiddle sSucc :
                MonomialBase Fˣ (Fin (n + 1))).right.symm
                (Fin.castSucc j) <
              (bruhatMiddle sSucc :
                MonomialBase Fˣ (Fin (n + 1))).right.symm
                (Fin.castSucc i) :=
            hNegPermT
          exact absurd hPosT (not_lt.mpr (le_of_lt hNeg'))
        exact leftWeylMultiplier_of_neg hijSucc sSucc hZeroNeT hNotPosT
      have hwEq :
          w = torusUnitOfNegCoeff
            (leftSimpleRootCoeff F (n + 1) sSucc hijSucc) hZeroNeT :=
        torusUnitOfNegCoeff_unique _ hZeroNeT w hw
      have hEqM :
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne v)⁻¹ * bruhatMiddle sSucc =
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w)⁻¹ * bruhatMiddle sSucc := by
        rw [← hMidSuccTorus, hMidNegT]
      have hCancel :
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne v)⁻¹ =
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w)⁻¹ :=
        mul_right_cancel hEqM
      have hTorusEq :
          torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne v =
          torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne w :=
        inv_injective hCancel
      have hvw : v = w :=
        torusMonomialSLUnit_injective hijSucc.ne hTorusEq
      rw [hvEq] at hvw
      rw [hwEq] at hvw
      have hHMTits :
          HMTitsSuccHom F n
            (hTits F n i j hij.ne
              (torusUnitOfNegCoeff
                (leftSimpleRootCoeff F n s hij) hZeroNe)) =
          hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne
            (torusUnitOfNegCoeff
              (leftSimpleRootCoeff F n s hij) hZeroNe) :=
        HMTitsSuccHom_hTits_adjacent
          (F := F) (n := n) (i := i) (j := j) (hij := hij)
          (u := torusUnitOfNegCoeff
            (leftSimpleRootCoeff F n s hij) hZeroNe)
      have hMapInv :
          HMTitsSuccHom F n
            ((hTits F n i j hij.ne
              (torusUnitOfNegCoeff
                (leftSimpleRootCoeff F n s hij) hZeroNe))⁻¹) =
          ((hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne
            (torusUnitOfNegCoeff
              (leftSimpleRootCoeff F n s hij) hZeroNe))⁻¹) := by
        rw [map_inv, hHMTits]
      calc HMTitsSuccHom F n (leftWeylMultiplier hij s)
          = HMTitsSuccHom F n
              ((hTits F n i j hij.ne
                (torusUnitOfNegCoeff
                  (leftSimpleRootCoeff F n s hij) hZeroNe))⁻¹) := by
            rw [hLeftNeg]
        _ = ((hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
              hijSucc.ne
              (torusUnitOfNegCoeff
                (leftSimpleRootCoeff F n s hij) hZeroNe))⁻¹) :=
            hMapInv
        _ = ((hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
              hijSucc.ne
              (torusUnitOfNegCoeff
                (leftSimpleRootCoeff F (n + 1) sSucc hijSucc)
                hZeroNeT))⁻¹) := by rw [hvw]
        _ = leftWeylMultiplier hijSucc sSucc := by
            rw [← hLeftNegT]

end Endpoint2

section Endpoint3

theorem leftWeylPerm_stabilization
    {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    XSucc F n (leftWeylPerm hij x) =
      leftWeylPerm (Fin.castSucc_covBy hij) (XSucc F n x) := by
  let hijSucc := Fin.castSucc_covBy hij
  have hFst :
      X.fst (XSucc F n (leftWeylPerm hij x)) =
      X.fst (leftWeylPerm hijSucc (XSucc F n x)) := by
    calc X.fst (XSucc F n (leftWeylPerm hij x))
        = stabilization F (X.fst (leftWeylPerm hij x)) := by
            rw [XSucc_fst]
      _ = stabilization F
            (weylSLUnit i j hij.ne (1 : Fˣ) * X.fst x) := by
            rw [leftWeylPerm_fst]
      _ = stabilization F (weylSLUnit i j hij.ne (1 : Fˣ)) *
          stabilization F (X.fst x) := by rw [map_mul]
      _ = weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * stabilization F (X.fst x) := by
            rw [stabilization_weylSLUnit]
      _ = weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
            hijSucc.ne (1 : Fˣ) * X.fst (XSucc F n x) := by
            rw [XSucc_fst]
      _ = X.fst (leftWeylPerm hijSucc (XSucc F n x)) := by
            rw [leftWeylPerm_fst]
  have hSnd :
      X.snd (XSucc F n (leftWeylPerm hij x)) =
      X.snd (leftWeylPerm hijSucc (XSucc F n x)) := by
    calc X.snd (XSucc F n (leftWeylPerm hij x))
        = HMTitsSuccHom F n (X.snd (leftWeylPerm hij x)) := by
            rw [XSucc_snd]
      _ = HMTitsSuccHom F n
            (leftWeylMultiplier hij (X.fst x) * X.snd x) := by
            rw [leftWeylPerm_snd]
      _ = HMTitsSuccHom F n (leftWeylMultiplier hij (X.fst x)) *
          HMTitsSuccHom F n (X.snd x) := by rw [map_mul]
      _ = leftWeylMultiplier hijSucc
            (stabilization F (X.fst x)) *
          HMTitsSuccHom F n (X.snd x) := by
            rw [leftWeylMultiplier_stabilization hij (X.fst x)]
      _ = leftWeylMultiplier hijSucc (X.fst (XSucc F n x)) *
          X.snd (XSucc F n x) := by
            rw [XSucc_fst, XSucc_snd]
      _ = X.snd (leftWeylPerm hijSucc (XSucc F n x)) := by
            rw [leftWeylPerm_snd]
  exact X.ext hFst hSnd

end Endpoint3

end MatsumotoTitsBruhatFiber
end
