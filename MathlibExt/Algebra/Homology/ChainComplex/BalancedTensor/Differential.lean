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

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.DifferentialCoordinates

/-!
# Differential compatibility of the actual signed tensor–Hom currying

The proof compares the three original differential terms. The triangular
unit supplies exactly the change in the two inner-Hom terms, in all integer
degrees. No differential square or comparison map is supplied as input.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

private theorem sign_pre (a b m : ℤ) (h : a + m = b) :
    Int.triangularSign b * (-a).negOnePow =
      m.negOnePow * Int.triangularSign (b - 1) := by
  have he : Int.triangularSign b =
      Int.triangularSign (b - 1) * b.negOnePow := by
    simpa only [sub_add_cancel] using Int.triangularSign_succ (b - 1)
  rw [he, mul_assoc, ← Int.negOnePow_add]
  have hb : b + -a = m := by omega
  rw [hb, mul_comm]

private theorem sign_post (b m : ℤ) :
    Int.triangularSign b * m.negOnePow =
      m.negOnePow * b.negOnePow * Int.triangularSign (b - 1) := by
  have he : Int.triangularSign b =
      Int.triangularSign (b - 1) * b.negOnePow := by
    simpa only [sub_add_cancel] using Int.triangularSign_succ (b - 1)
  rw [he]
  ac_rfl

universe u v

variable (R : Type u) [Ring R]
  (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)
  (I : CochainComplex AddCommGrpCat.{v} ℤ)

local notation "HI" => moduleHomCochainComplex R Q I

/-- The earned signed currying commutes with the two original total-Hom differentials. -/
theorem curryCochain_d (n : ℤ) (f : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n) :
    curryCochain R P Q I (n + 1)
        (((homCochainComplex (complex R P Q) I).d n (n + 1)).hom f) =
      ((homCochainComplex P HI).d n (n + 1)).hom (curryCochain R P Q I n f) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply CochainComplex.HomComplex.Cochain.ext
  intro c d hcd
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  let A : I.X d := (f.v (a + c + 1) d (by omega)).hom
    (mk R P Q (-(a + 1)) (-c) (-(a + c + 1)) (by omega)
      ((P.d (-a) (-(a + 1))).hom x) y)
  let B : I.X d := (f.v (a + c + 1) d (by omega)).hom
    (mk R P Q (-a) (-(c + 1)) (-(a + c + 1)) (by omega) x
      ((Q.d (-c) (-(c + 1))).hom y))
  let C : I.X d := (I.d (d - 1) d).hom
    ((f.v (a + c) (d - 1) (by omega)).hom
      (mk R P Q (-a) (-c) (-(a + c)) (by omega) x y))
  have hleft := curryCochain_v R P Q I (n + 1)
    (((homCochainComplex (complex R P Q) I).d n (n + 1)).hom f)
    a b hab c d hcd x y
  have hdelta := tensorHom_d_mk R P Q I n f a c d (by omega) x y
  have hleft' :
      ((((curryCochain R P Q I (n + 1)
        (((homCochainComplex (complex R P Q) I).d n (n + 1)).hom f)).v
          a b hab).hom x).v c d hcd).hom y =
      Int.triangularSign b • (A + (-a).negOnePow • B + (n + 1).negOnePow • C) :=
    hleft.trans (congrArg (fun w : I.X d => Int.triangularSign b • w) hdelta)
  have hA0 := curryCochain_v R P Q I n f (a + 1) b (by omega) c d hcd
    ((P.d (-a) (-(a + 1))).hom x) y
  have hAv := tensor_v_of_eq R P Q I n f (a + c + 1) d (by omega)
    (-(a + 1)) (-c) (by omega) (-(a + 1)) (-c) (a + 1 + c)
    rfl rfl (by omega) ((P.d (-a) (-(a + 1))).hom x) y
  have hAvalue : (f.v (a + 1 + c) d (by omega)).hom
      (mk R P Q (-(a + 1)) (-c) (-(a + 1 + c)) (by omega)
        ((P.d (-a) (-(a + 1))).hom x) y) = A := by
    have hx : ((P.XIsoOfEq (rfl : -(a + 1) = -(a + 1))).hom).hom
        ((P.d (-a) (-(a + 1))).hom x) = ((P.d (-a) (-(a + 1))).hom x) := rfl
    have hy : ((Q.XIsoOfEq (rfl : -c = -c)).hom).hom y = y := rfl
    have hPoint := congrArg₂
      (fun xp : P.X (-(a + 1)) => fun yq : Q.X (-c) =>
        (f.v (a + 1 + c) d (by omega)).hom
          (mk R P Q (-(a + 1)) (-c) (-(a + 1 + c)) (by omega) xp yq)) hx hy
    exact hPoint.symm.trans hAv
  have hA : ((((curryCochain R P Q I n f).v (a + 1) b (by omega)).hom
      ((P.d (-a) (-(a + 1))).hom x)).v c d hcd).hom y =
      Int.triangularSign b • A :=
    hA0.trans (congrArg (fun w : I.X d => Int.triangularSign b • w) hAvalue)
  have hB0 := curryCochain_v R P Q I n f a (b - 1) (by omega) (c + 1) d
    (by omega) x ((Q.d (-c) (-(c + 1))).hom y)
  have hBv := tensor_v_of_eq R P Q I n f (a + c + 1) d (by omega)
    (-a) (-(c + 1)) (by omega) (-a) (-(c + 1)) (a + (c + 1))
    rfl rfl (by omega) x ((Q.d (-c) (-(c + 1))).hom y)
  have hBvalue : (f.v (a + (c + 1)) d (by omega)).hom
      (mk R P Q (-a) (-(c + 1)) (-(a + (c + 1))) (by omega) x
        ((Q.d (-c) (-(c + 1))).hom y)) = B := by
    have hx : ((P.XIsoOfEq (rfl : -a = -a)).hom).hom x = x := rfl
    have hy : ((Q.XIsoOfEq (rfl : -(c + 1) = -(c + 1))).hom).hom
        ((Q.d (-c) (-(c + 1))).hom y) = ((Q.d (-c) (-(c + 1))).hom y) := rfl
    have hPoint := congrArg₂
      (fun xp : P.X (-a) => fun yq : Q.X (-(c + 1)) =>
        (f.v (a + (c + 1)) d (by omega)).hom
          (mk R P Q (-a) (-(c + 1)) (-(a + (c + 1))) (by omega) xp yq)) hx hy
    exact hPoint.symm.trans hBv
  have hB : ((((curryCochain R P Q I n f).v a (b - 1) (by omega)).hom x).v
      (c + 1) d (by omega)).hom ((Q.d (-c) (-(c + 1))).hom y) =
      Int.triangularSign (b - 1) • B :=
    hB0.trans (congrArg (fun w : I.X d => Int.triangularSign (b - 1) • w) hBvalue)
  have hC0 := curryCochain_v R P Q I n f a (b - 1) (by omega) c (d - 1)
    (by omega) x y
  have hC : (I.d (d - 1) d).hom
      (((((curryCochain R P Q I n f).v a (b - 1) (by omega)).hom x).v
        c (d - 1) (by omega)).hom y) = Int.triangularSign (b - 1) • C := by
    have hc := congrArg (I.d (d - 1) d).hom hC0
    simpa only [map_zsmul_unit, C] using hc
  have hright := nestedHom_d_v R P Q I n (curryCochain R P Q I n f)
    a b hab c d hcd x y
  have hright' :
      ((((((homCochainComplex P HI).d n (n + 1)).hom
        (curryCochain R P Q I n f)).v a b hab).hom x).v c d hcd).hom y =
      Int.triangularSign b • A + (n + 1).negOnePow •
        (Int.triangularSign (b - 1) • B +
          b.negOnePow • (Int.triangularSign (b - 1) • C)) := by
    exact hright.trans (congrArg₂ (fun v w : I.X d => v + (n + 1).negOnePow • w)
      hA (congrArg₂ (fun v w : I.X d => v + b.negOnePow • w) hB hC))
  have hsign : Int.triangularSign b •
      (A + (-a).negOnePow • B + (n + 1).negOnePow • C) =
      Int.triangularSign b • A + (n + 1).negOnePow •
        (Int.triangularSign (b - 1) • B +
          b.negOnePow • (Int.triangularSign (b - 1) • C)) := by
    simp only [smul_add, smul_smul]
    rw [sign_pre a b (n + 1) hab, sign_post b (n + 1)]
    simp only [add_assoc, mul_assoc]
  exact hleft'.trans (hsign.trans hright'.symm)

end ChainComplex.BalancedTensor
