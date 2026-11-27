/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.RegularElementTor
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega

/-!
# A noncentral regular matrix with torsion coefficients

In R=M₂(ℤ), let a=[[2,1],[0,2]]. Left multiplication by a is injective,
but a does not commute with the matrix unit e₂₁. The ring R itself has
zero divisors. Coefficients are (ℤ/2)², with the matrix action reduced
modulo two, lifted first to universe one and then to universe two.

The first basis vector is nonzero and killed by a. The computed first Tor
of R/aR therefore contains a nonzero class whose annihilator coordinate
is that vector. Multiplying the vector by e₂₁ leaves the a-annihilator,
so the computed kernel is an additive group rather than an R-submodule.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory ModuleCat.RegularElement

namespace MathlibExtTest.RegularElementTor

private abbrev R := Matrix (Fin 2) (Fin 2) ℤ

private def a : R :=
  fun i j => if i = 0 then (if j = 0 then 2 else 1) else (if j = 0 then 0 else 2)

private def e₂₁ : R := fun i j => if i = 1 ∧ j = 0 then 1 else 0

private lemma a_mul_entries (X : R) (j : Fin 2) :
    (a * X) 0 j = 2 * X 0 j + X 1 j ∧ (a * X) 1 j = 2 * X 1 j := by
  constructor <;> simp [a, Matrix.mul_apply, Fin.sum_univ_two]

private lemma a_leftRegular : IsLeftRegular a := by
  intro X Y h
  have h₁ (j : Fin 2) : X 1 j = Y 1 j := by
    have hj := congrArg (fun B : R => B 1 j) h
    rw [(a_mul_entries X j).2, (a_mul_entries Y j).2] at hj
    omega
  ext i j
  fin_cases i
  · have hj := congrArg (fun B : R => B 0 j) h
    rw [(a_mul_entries X j).1, (a_mul_entries Y j).1] at hj
    have hk := h₁ j
    omega
  · exact h₁ j

private lemma a_noncentral : a * e₂₁ ≠ e₂₁ * a := by
  intro h
  have h₀₀ := congrArg (fun B : R => B 0 0) h
  norm_num [a, e₂₁, Matrix.mul_apply, Fin.sum_univ_two] at h₀₀

private abbrev S := Matrix (Fin 2) (Fin 2) (ZMod 2)

private def reduce : R →+* S := (Int.castRingHom (ZMod 2)).mapMatrix

private instance : Module R (Fin 2 → ZMod 2) :=
  Module.compHom (Fin 2 → ZMod 2) reduce

private abbrev N₀ : ModuleCat.{0} R := ModuleCat.of R (Fin 2 → ZMod 2)
private abbrev N₁ : ModuleCat.{1} R := (ModuleCat.uliftFunctor.{1, 0} R).obj N₀
private abbrev N₂ : ModuleCat.{2} R := (ModuleCat.uliftFunctor.{2, 1} R).obj N₁

private def z₀ : N₀ := fun i => if i = 0 then 1 else 0
private def z : N₂ := ULift.up (ULift.up z₀)

private lemma z_ne_zero : z ≠ 0 := by
  intro h
  have h₀ := congrArg (fun n : N₂ => n.down.down 0) h
  change (1 : ZMod 2) = 0 at h₀
  exact (by decide : (1 : ZMod 2) ≠ 0) h₀

private lemma a_kills_z : a • z = 0 := by
  apply ULift.ext
  apply ULift.ext
  change (reduce a).mulVec z₀ = 0
  ext i
  fin_cases i <;>
    norm_num [reduce, a, z₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma action_leaves_annihilator : a • (e₂₁ • z) ≠ 0 := by
  intro h
  have h₀ := congrArg (fun n : N₂ => n.down.down 0) h
  change ((reduce a).mulVec ((reduce e₂₁).mulVec z₀)) 0 = 0 at h₀
  norm_num [reduce, a, e₂₁, z₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₀

private def annihilatorVector : annihilatorGroup R a N₂ := ⟨z, a_kills_z⟩

private abbrev torGroup :=
  ((ModuleCat.BalancedTensor.torFirst R 1).obj (quotient.{0, 2} R a)).obj N₂

private abbrev comparison := quotientTorOneIsoAt.{0, 1, 2} R a a_leftRegular N₁

private def torClass : torGroup := comparison.inv.hom annihilatorVector

private lemma torClass_coordinate :
    (comparison.hom.hom torClass).val.down.down 0 = (1 : ZMod 2) :=
  congrArg (fun n : annihilatorGroup R a N₂ => n.val.down.down 0)
    (ConcreteCategory.congr_hom comparison.inv_hom_id annihilatorVector)

example : a * e₂₁ ≠ e₂₁ * a := a_noncentral

example : e₂₁ ≠ 0 ∧ e₂₁ * e₂₁ = 0 := by
  constructor
  · intro h
    have h₂₁ := congrArg (fun B : R => B 1 0) h
    norm_num [e₂₁] at h₂₁
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e₂₁, Matrix.mul_apply, Fin.sum_univ_two]

example : IsLeftRegular a := a_leftRegular

example : (sequence.{0, 2} R a).ShortExact := sequence_shortExact.{0, 2} R a a_leftRegular

example :
    (((projectiveResolution.{0, 2} R a a_leftRegular).complex.d 1 0).hom
      (ULift.up (MulOpposite.op (1 : R)))).down.unop = a := by
  rw [projectiveResolution_d_one_zero, leftMultiplication_unop_apply, mul_one]

example :
    (((projectiveResolution.{0, 2} R a a_leftRegular).complex.d 1 0).hom
      (ULift.up (MulOpposite.op e₂₁))).down.unop ≠ e₂₁ * a := by
  rw [projectiveResolution_d_one_zero, leftMultiplication_unop_apply]
  exact a_noncentral

example : IsZero ((projectiveResolution.{0, 2} R a a_leftRegular).complex.X 3) :=
  projectiveResolution_isZero_above.{0, 2} R a a_leftRegular 3 (by decide)

example : z ≠ 0 ∧ a • z = 0 := ⟨z_ne_zero, a_kills_z⟩

example : a • (e₂₁ • z) ≠ 0 := action_leaves_annihilator

example : (comparison.hom.hom torClass).val.down.down 0 = (1 : ZMod 2) :=
  torClass_coordinate

example : torClass ≠ 0 := by
  intro h
  have hc := torClass_coordinate
  rw [h, map_zero] at hc
  change (0 : ZMod 2) = 1 at hc
  exact (by decide : (0 : ZMod 2) ≠ 1) hc

end MathlibExtTest.RegularElementTor
