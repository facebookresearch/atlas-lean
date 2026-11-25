/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCupRestriction
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCupCons
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupOneAnyProjection

/-!
# Corestriction of positive iterated cups

This file packages iterated cups whose initial entries are restrictions of
ambient degree-one classes and whose final entry is a subgroup class.  The
coefficient is normalized into the restriction of the ambient positive
tensor power.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

/-- The normalized iterated cup of restricted ambient classes followed by
one subgroup degree-one class. -/
noncomputable def restrictedIteratedCupClassSuccLast
    (A : Rep k G) (n : ℕ)
    (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    groupCohomology
      (Rep.res H.subtype
        (TensorPower.tensorPowObj A (n + 1))) (n + 1) :=
  restrictedIteratedCupClassSuccLastOfHom H.subtype A n x y

omit [H.FiniteIndex] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- In weight one, the normalized restricted iterated cup is restriction of
the ambient weight-one coefficient applied to the subgroup class. -/
theorem restrictedIteratedCupClassSuccLast_zero
    (A : Rep k G)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    restrictedIteratedCupClassSuccLast H A 0
        (fun i => Fin.elim0 i) y =
      groupCohomology.map (MonoidHom.id H)
        ((Rep.resFunctor H.subtype).map
          (TensorPower.tensorPowObjOneIso A).inv) 1 y := by
  exact restrictedIteratedCupClassSuccLastOfHom_zero
    H.subtype A (fun i => Fin.elim0 i) y

omit [H.FiniteIndex] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- At successor weight, the normalized restricted iterated cup exposes the
first restricted ambient class and the normalized mixed tail. -/
theorem restrictedIteratedCupClassSuccLast_succ_headTail
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso H.subtype A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSuccLast H A (n + 1) x y) =
      cupOneAny (Rep.res H.subtype A)
        (Rep.res H.subtype
          (TensorPower.tensorPowObj A (n + 1))) (n + 1)
        (groupCohomology.map H.subtype
            (𝟙 (Rep.res H.subtype A)) 1 (x 0) ⊗ₜ[k]
          restrictedIteratedCupClassSuccLast H A n
            (fun i => x i.succ) y) := by
  exact restrictedIteratedCupClassSuccLastOfHom_succ_headTail
    H.subtype A n x y

set_option backward.isDefEq.respectTransparency.types false in
/-- Weight-one base case of the iterated-cup corestriction formula. -/
theorem schreierCorestriction_restrictedIteratedCupClassSuccLast_zero
    (A : Rep k G)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    schreierCorestriction H (TensorPower.tensorPowObj A 1) 1
        (restrictedIteratedCupClassSuccLast H A 0
          (fun i => Fin.elim0 i) y) =
      iteratedCupClassSucc A 0
        ![groupCohomology.corestrictionH1 A y] := by
  rw [restrictedIteratedCupClassSuccLast_zero]
  rw [iteratedCupClassSucc_zero]
  have hnat := ConcreteCategory.congr_hom
    (schreierCorestriction_naturality H
      (TensorPower.tensorPowObjOneIso A).inv 1) y
  simp only [ConcreteCategory.comp_apply] at hnat
  have hone : (schreierCorestriction H A 1).hom y =
      groupCohomology.corestrictionH1 A y :=
    congrArg (fun f => f y) (schreierCorestriction_one_eq (H := H) A)
  rw [hone] at hnat
  exact hnat.symm

/-- Head-recursive mixed iterated cup over a subgroup.  Its coefficient is
the restriction of the ambient right-associated positive tensor power. -/
noncomputable def restrictedIteratedCupClassConsLast
    (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin n → groupCohomology.H1 A)
      (_y : groupCohomology.H1 (Rep.res H.subtype A)),
      groupCohomology
        (Rep.res H.subtype
          (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
  | n, x, y =>
      restrictedIteratedCupClassConsLastOfHom H.subtype A n x y

omit [H.FiniteIndex] in
@[simp]
theorem restrictedIteratedCupClassConsLast_zero
    (A : Rep k G) (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    restrictedIteratedCupClassConsLast H A 0 x y = y :=
  restrictedIteratedCupClassConsLastOfHom_zero H.subtype A x y

omit [H.FiniteIndex] in
@[simp]
theorem restrictedIteratedCupClassConsLast_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    restrictedIteratedCupClassConsLast H A (n + 1) x y =
      groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A
          (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
        (cupOneAny (Rep.res H.subtype A)
          (Rep.res H.subtype
            (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
          (groupCohomology.map H.subtype
              (𝟙 (Rep.res H.subtype A)) 1 (x 0) ⊗ₜ[k]
            restrictedIteratedCupClassConsLast H A n
              (fun i => x i.succ) y)) :=
  restrictedIteratedCupClassConsLastOfHom_succ H.subtype A n x y

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical Schreier corestriction carries a mixed head-recursive cup to
the ambient head-recursive cup ending in degree-one corestriction. -/
theorem schreierCorestriction_restrictedIteratedCupClassConsLast
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin n → groupCohomology.H1 A)
      (y : groupCohomology.H1 (Rep.res H.subtype A)),
      schreierCorestriction H
          (TensorPower.tensorPowObjRightSucc A n) (n + 1)
          (restrictedIteratedCupClassConsLast H A n x y) =
        iteratedCupClassConsLast A n x
          (groupCohomology.corestrictionH1 A y)
  | 0, x, y => by
      rw [restrictedIteratedCupClassConsLast_zero,
        iteratedCupClassConsLast_zero]
      exact congrArg (fun f => f y)
        (schreierCorestriction_one_eq (H := H) A)
  | n + 1, x, y => by
      rw [restrictedIteratedCupClassConsLast_succ,
        iteratedCupClassConsLast_succ]
      change schreierCorestriction H
          (A ⊗ TensorPower.tensorPowObjRightSucc A n) (n + 2)
          (groupCohomology.map (MonoidHom.id H)
            (Rep.resTensorIso H.subtype A
              (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
            (cupOneAny (Rep.res H.subtype A)
              (Rep.res H.subtype
                (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
              (groupCohomology.map H.subtype
                  (𝟙 (Rep.res H.subtype A)) 1 (x 0) ⊗ₜ[k]
                restrictedIteratedCupClassConsLast H A n
                  (fun i => x i.succ) y))) = _
      rw [schreierCorestriction_cup_one_any]
      rw [schreierCorestriction_restrictedIteratedCupClassConsLast]

end groupCohomology
