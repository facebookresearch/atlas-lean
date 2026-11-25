/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RelativePDerivation
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

open MetaMathlibExt

-- Tests for C_p at p=2 and p=3, and end-to-end RelativePDerivation into ZMod 1.

-- The integer coefficient really is the quotient claimed in the source formula.
example (p i : ℕ) [Fact p.Prime] (hi : i ≠ 0) (hip : i < p) :
    (p : ℤ) * pDerivationCorrectionCoeff p i = -(Nat.choose p i : ℤ) := by
  unfold pDerivationCorrectionCoeff
  have hq : (p : ℤ) * ((Nat.choose p i : ℤ) / (p : ℤ)) = (Nat.choose p i : ℤ) :=
    Int.mul_ediv_cancel'
      (Int.ofNat_dvd.mpr ((Fact.out : p.Prime).dvd_choose_self hi hip))
  calc
    (p : ℤ) * -((Nat.choose p i : ℤ) / (p : ℤ)) =
        -((p : ℤ) * ((Nat.choose p i : ℤ) / (p : ℤ))) := Int.mul_neg _ _
    _ = -(Nat.choose p i : ℤ) := congrArg Neg.neg hq

-- p = 2 : C_2(x,y) = - x*y  because (x^2+y^2-(x+y)^2)/2 = -xy
-- choose 2 1 = 2, coefficient -1.
example {B : Type*} [CommRing B] (x y : B) : pDerivationCorrection 2 x y = -x * y := by
  have hI : Finset.Ico 1 2 = {1} := by decide
  simp [pDerivationCorrection, hI, pDerivationCorrectionCoeff]

-- p = 3 : C_3(x,y) = - x^2*y - x*y^2 = -x*y*(x+y)
-- choose 3 1 = 3, choose 3 2 = 3, both coefficients -1.
example {B : Type*} [CommRing B] (x y : B) :
    pDerivationCorrection 3 x y = -x ^ 2 * y - x * y ^ 2 := by
  have hI : Finset.Ico 1 3 = {1, 2} := by decide
  simp [pDerivationCorrection, hI, pDerivationCorrectionCoeff]
  ring

-- Alternative form for p=3.
example {B : Type*} [CommRing B] (x y : B) : pDerivationCorrection 3 x y = -x * y * (x + y) := by
  have hI : Finset.Ico 1 3 = {1, 2} := by decide
  simp [pDerivationCorrection, hI, pDerivationCorrectionCoeff]
  ring

-- Zero ring is terminal: the unique ring hom to ZMod 1.
def uZero (A : Type*) [CommRing A] : A →+* ZMod 1 where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

-- Real RelativePDerivation into the zero ring ZMod 1.
-- All laws hold because ZMod 1 is subsingleton (0 = 1).
def zeroDerivation (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] :
    RelativePDerivation p (uZero A) where
  toFun _ := 0
  map_one := rfl
  map_add _ _ := Subsingleton.elim _ _
  map_mul _ _ := Subsingleton.elim _ _

-- Exercise the bundled structure end-to-end.
example (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] :
    let d := zeroDerivation A p
    (d : A → ZMod 1) 1 = 0 ∧
    (∀ x y : A, (d : A → ZMod 1) (x + y) =
      (d : A → ZMod 1) x + (d : A → ZMod 1) y + pDerivationCorrection p (uZero A x) (uZero A y)) ∧
    (∀ x y : A, (d : A → ZMod 1) (x * y) =
      (uZero A x) ^ p * (d : A → ZMod 1) y +
      (uZero A y) ^ p * (d : A → ZMod 1) x +
      (p : ZMod 1) * (d : A → ZMod 1) x * (d : A → ZMod 1) y) := by
  refine ⟨rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

-- CoeFun works.
example (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] (x : A) :
    (zeroDerivation A p : A → ZMod 1) x = 0 := rfl
