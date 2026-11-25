/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.Sequence.TensorPower
import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation
import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluationRelabeling

/-!
# Tests for the ordered tensor-power sequence module

This owner pins the nine-name public surface, the ordered Day multiplication,
the explicit unregistered monoid value, the self-action module alias, and the
one-step module structure map.  The negative checks exclude commutativity,
pointwise multiplication, reversed transports, and the former malformed
`Mod` alias.
-/

set_option autoImplicit false

noncomputable section

universe vV uV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct MonoidalCategory

namespace MathlibExtTest.CategoryTheory.Monoidal.Sequence.TensorPowerTests

#check @CategoryTheory.Sequence.tensorPowerSequence
#check @CategoryTheory.Sequence.tensorPowerSequence_obj
#check @CategoryTheory.Sequence.tensorPowerSequenceMonObj
#check @CategoryTheory.Sequence.tensorPowerSequenceOne_ν
#check @CategoryTheory.Sequence.tensorPowerSequenceMul_η
#check @CategoryTheory.Sequence.TensorPowerModule
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_eq
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_naturality

#check @CategoryTheory.Sequence.TensorPowerModule.{0, 0}
#check @CategoryTheory.Sequence.TensorPowerModule.{1, 1}
#check @CategoryTheory.Sequence.TensorPowerModule.{0, 1}
#check @CategoryTheory.Sequence.TensorPowerModule.{1, 0}
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap.{0, 0}
#check @CategoryTheory.Sequence.tensorPowerSequenceOne_ν.{0, 0}
#check @CategoryTheory.Sequence.tensorPowerSequenceOne_ν.{1, 1}
#check @CategoryTheory.Sequence.tensorPowerSequenceOne_ν.{0, 1}
#check @CategoryTheory.Sequence.tensorPowerSequenceOne_ν.{1, 0}
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_eq.{0, 0}
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_eq.{1, 1}
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_eq.{0, 1}
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_eq.{1, 0}
#check @CategoryTheory.Sequence.TensorPowerModule.structureMap_naturality.{0, 0}

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
variable
  [∀ (F G : CategoryTheory.Sequence.Index ⥤ V),
    (tensor CategoryTheory.Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ CategoryTheory.Sequence.Index)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (d : CategoryTheory.Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor CategoryTheory.Sequence.Index) d) (tensorLeft W)]
  [∀ (W : V) (d : CategoryTheory.Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor CategoryTheory.Sequence.Index) d) (tensorRight W)]
  [∀ (W : V) (d : CategoryTheory.Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ CategoryTheory.Sequence.Index)) d) (tensorLeft W)]
  [∀ (W : V) (d : CategoryTheory.Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ CategoryTheory.Sequence.Index)) d) (tensorRight W)]
  [∀ (W : V) (d : CategoryTheory.Sequence.Index × CategoryTheory.Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((𝟭 CategoryTheory.Sequence.Index).prod
          (Functor.fromPUnit.{0} (𝟙_ CategoryTheory.Sequence.Index))) d)
      (tensorRight W)]
  [∀ (W : V) (d : CategoryTheory.Sequence.Index × CategoryTheory.Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((tensor CategoryTheory.Sequence.Index).prod
          (𝟭 CategoryTheory.Sequence.Index)) d)
      (tensorRight W)]
  [∀ i j : CategoryTheory.Sequence.Index,
    HasCoproductsOfShape (i ⟶ j) V]

open CategoryTheory.Sequence

section Levels

variable (K : V)

example : (tensorPowerSequence K).functor.obj (index 0) =
    TensorPower.tensorPowObj K 0 :=
  tensorPowerSequence_obj K 0

example : (tensorPowerSequence K).functor.obj (index 1) =
    TensorPower.tensorPowObj K 1 :=
  tensorPowerSequence_obj K 1

example : (tensorPowerSequence K).functor.obj (index 2) =
    TensorPower.tensorPowObj K 2 :=
  tensorPowerSequence_obj K 2

example : (tensorPowerSequence K).functor.obj (index 0) = 𝟙_ V :=
  rfl

example : (tensorPowerSequence K).functor.obj (index 1) =
    𝟙_ V ⊗ K :=
  rfl

example : (tensorPowerSequence K).functor.obj (index 2) =
    (𝟙_ V ⊗ K) ⊗ K :=
  rfl

end Levels

section OrderedMultiplication

variable (K : V) (n : ℕ)

example := tensorPowerSequenceMul_η K 0 n
example := tensorPowerSequenceMul_η K n 0
example := tensorPowerSequenceMul_η K 1 1

example :
    DayFunctor.ν Index V ≫
        (tensorPowerSequenceMonObj K).one.natTrans.app (index 0) =
      TensorPower.laxTensorPowerUnit (𝟭 V) K :=
  tensorPowerSequenceOne_ν K

example := (tensorPowerSequenceMonObj K).one_mul
example := (tensorPowerSequenceMonObj K).mul_one
example := (tensorPowerSequenceMonObj K).mul_assoc

end OrderedMultiplication

section Modules

example (K : V) : True := by
  let _ : MonObj (tensorPowerSequence K) :=
    tensorPowerSequenceMonObj K
  have h0 (M : TensorPowerModule K) :
      K ⊗ M.X.functor.obj (index 0) ⟶
        M.X.functor.obj (index 1) :=
    TensorPowerModule.structureMap M 0
  have h1 (M : TensorPowerModule K) :
      K ⊗ M.X.functor.obj (index 1) ⟶
        M.X.functor.obj (index 2) :=
    TensorPowerModule.structureMap M 1
  have h2 (M : TensorPowerModule K) :
      K ⊗ M.X.functor.obj (index 2) ⟶
        M.X.functor.obj (index 3) :=
    TensorPowerModule.structureMap M 2
  have hFormula (M : TensorPowerModule K) (n : ℕ) :
      TensorPowerModule.structureMap M n =
        ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
          (DayFunctor.η (tensorPowerSequence K) M.X).app
            (index 1, index n) ≫
          M.mod.smul.natTrans.app (index 1 ⊗ index n) ≫
          M.X.functor.map
            (eqToHom ((tensorObj_index 1 n).trans
              (congrArg index (Nat.one_add n)))) :=
    TensorPowerModule.structureMap_eq M n
  have hn (M N : TensorPowerModule K) (f : M ⟶ N) (n : ℕ) :
      TensorPowerModule.structureMap M n ≫
          f.hom.natTrans.app (index (n + 1)) =
        (𝟙 K ⊗ₘ f.hom.natTrans.app (index n)) ≫
          TensorPowerModule.structureMap N n :=
    TensorPowerModule.structureMap_naturality f n
  trivial

end Modules

section GenericClients

example (K : V) : True := by
  fail_if_success
    let _ : MonObj (tensorPowerSequence K) := inferInstance
  let _ : MonObj (tensorPowerSequence K) :=
    tensorPowerSequenceMonObj K
  let _ := CategoryTheory.Mod.dayEvaluation
    (tensorPowerSequence K) (index 0)
  let _ := CategoryTheory.Mod.dayFreeAt
    (tensorPowerSequence K) (index 0)
  let _ := CategoryTheory.Mod.dayFreeAtEvaluationAdjunction
    (tensorPowerSequence K) (index 0)
  let _ := CategoryTheory.Mod.dayFreeAtFunctor
    (tensorPowerSequence K)
  fail_if_success
    let _ : CommMonObj (tensorPowerSequence K) := inferInstance
  trivial

example (_K : V) : True := by
  fail_if_success
    let _ := @CategoryTheory.Mod (CategoryTheory.Sequence V) _ _
      (tensorPowerSequence _K)
      (tensorPowerSequenceMonObj _K)
  trivial

end GenericClients

section Falsifiers

example (K : V) (_n : ℕ) : True := by
  let _ : MonObj (tensorPowerSequence K) :=
    tensorPowerSequenceMonObj K
  fail_if_success
    let _bad :
        (tensorPowerSequence K).functor.obj (index _n) ⊗
            (tensorPowerSequence K).functor.obj (index _n) ⟶
          (tensorPowerSequence K).functor.obj (index _n) :=
      (tensorPowerSequenceMonObj K).mul.natTrans.app (index _n)
  trivial

example (_K : V) (_n : ℕ) : True := by
  fail_if_success
    exact (tensorPowerSequence_obj _K _n :
      (tensorPowerSequence _K).functor.obj (index _n) =
        TensorPower.tensorPowObj _K (_n + 1))
  trivial

example (_K : V) (_p _q : ℕ) : True := by
  fail_if_success
    exact (show
      (DayFunctor.η (tensorPowerSequence _K)
          (tensorPowerSequence _K)).app (index _p, index _q) ≫
          (tensorPowerSequenceMonObj _K).mul.natTrans.app
            (index _p ⊗ index _q) =
        TensorPower.laxTensorPowerPairing (𝟭 V) _K _p _q from
      tensorPowerSequenceMul_η _K _p _q)
  fail_if_success
    let _ :=
      (DayFunctor.η (tensorPowerSequence _K)
          (tensorPowerSequence _K)).app (index _p, index _q) ≫
        (tensorPowerSequence _K).functor.map
          (eqToHom (tensorObj_index _p _q)) ≫
        (tensorPowerSequenceMonObj _K).mul.natTrans.app
          (index _p ⊗ index _q)
  fail_if_success
    exact (show
      (DayFunctor.η (tensorPowerSequence _K)
          (tensorPowerSequence _K)).app (index _q, index _p) ≫
          (tensorPowerSequenceMonObj _K).mul.natTrans.app
            (index _q ⊗ index _p) ≫
          (tensorPowerSequence _K).functor.map
            (eqToHom (tensorObj_index _q _p)) =
        TensorPower.laxTensorPowerPairing (𝟭 V) _K _p _q from
      tensorPowerSequenceMul_η _K _p _q)
  trivial

example (K : V) : True := by
  let _ : MonObj (tensorPowerSequence K) :=
    tensorPowerSequenceMonObj K
  fail_if_success
    let _bad (M : TensorPowerModule K) (n : ℕ) :
        K ⊗ M.X.functor.obj (index n) ⟶
          M.X.functor.obj (index (n + 1)) :=
      ((λ_ K).hom ⊗ₘ 𝟙 _) ≫
        (DayFunctor.η (tensorPowerSequence K) M.X).app
          (index 1, index n) ≫
        M.mod.smul.natTrans.app (index 1 ⊗ index n) ≫
        M.X.functor.map
          (eqToHom ((tensorObj_index 1 n).trans
            (congrArg index (Nat.one_add n))))
  fail_if_success
    let _bad (M : TensorPowerModule K) (n : ℕ) :
        K ⊗ M.X.functor.obj (index n) ⟶
          M.X.functor.obj (index (n + 1)) :=
      ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
        (DayFunctor.η (tensorPowerSequence K) M.X).app
          (index n, index 1) ≫
        M.mod.smul.natTrans.app (index n ⊗ index 1) ≫
        M.X.functor.map
          (eqToHom ((tensorObj_index 1 n).trans
            (congrArg index (Nat.one_add n))))
  fail_if_success
    let _bad (M : TensorPowerModule K) (n : ℕ) :
        K ⊗ M.X.functor.obj (index n) ⟶
          M.X.functor.obj (index (n + 1)) :=
      ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
        M.mod.smul.natTrans.app (index 1 ⊗ index n) ≫
        (DayFunctor.η (tensorPowerSequence K) M.X).app
          (index 1, index n) ≫
        M.X.functor.map
          (eqToHom ((tensorObj_index 1 n).trans
            (congrArg index (Nat.one_add n))))
  fail_if_success
    let _bad (M : TensorPowerModule K) (n : ℕ) :
        K ⊗ M.X.functor.obj (index n) ⟶
          M.X.functor.obj (index (n + 1)) :=
      ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
        (DayFunctor.η (tensorPowerSequence K) M.X).app
          (index 1, index n) ≫
        M.mod.smul.natTrans.app (index 1 ⊗ index n)
  fail_if_success
    let _bad (M : TensorPowerModule K) (n : ℕ) :
        K ⊗ M.X.functor.obj (index n) ⟶
          M.X.functor.obj (index (n + 1)) :=
      ((λ_ K).inv ⊗ₘ 𝟙 _) ≫
        (DayFunctor.η (tensorPowerSequence K) M.X).app
          (index 1, index n) ≫
        M.mod.smul.natTrans.app (index 1 ⊗ index n) ≫
        M.X.functor.map
          (eqToHom ((tensorObj_index 1 n).trans
            (congrArg index (Nat.one_add n))).symm)
  trivial

example (K : V) : True := by
  let _ : MonObj (tensorPowerSequence K) :=
    tensorPowerSequenceMonObj K
  fail_if_success
    let _bad (M N : TensorPowerModule K) (f : M ⟶ N) (n : ℕ) :=
      f.hom.natTrans.app (index (n + 1)) ≫
        TensorPowerModule.structureMap N n
  fail_if_success
    let _bad (M N : TensorPowerModule K) (f : M ⟶ N) (n : ℕ) :
        TensorPowerModule.structureMap M n ≫
            f.hom.natTrans.app (index (n + 1)) =
          (f.hom.natTrans.app (index n) ▷ K) ≫
            TensorPowerModule.structureMap N n := by
      exact TensorPowerModule.structureMap_naturality f n
  fail_if_success
    let _bad (M N : TensorPowerModule K) (f : M ⟶ N) (n : ℕ) :
        TensorPowerModule.structureMap M n ≫
            f.hom.natTrans.app (index (n + 1)) =
          (𝟙 K ⊗ₘ f.hom.natTrans.app (index (n + 1))) ≫
            TensorPowerModule.structureMap N n := by
      exact TensorPowerModule.structureMap_naturality f n
  fail_if_success
    let _bad (M N : TensorPowerModule K) (f : M ⟶ N) (n : ℕ) :=
      TensorPowerModule.structureMap_naturality n f
  trivial

end Falsifiers

/-- error: Unknown constant `CategoryTheory.Sequence.TensorPowerModule.dayEvaluation` -/
#guard_msgs in
#check CategoryTheory.Sequence.TensorPowerModule.dayEvaluation

/-- error: Unknown constant `CategoryTheory.Sequence.TensorPowerModule.dayFreeAt` -/
#guard_msgs in
#check CategoryTheory.Sequence.TensorPowerModule.dayFreeAt

/-- error: Unknown constant `CategoryTheory.Sequence.TensorPowerModule.stableEquivalence` -/
#guard_msgs in
#check CategoryTheory.Sequence.TensorPowerModule.stableEquivalence

/-- error: Unknown constant `CategoryTheory.Sequence.tensorPowerSequenceMulDesc` -/
#guard_msgs in
#check CategoryTheory.Sequence.tensorPowerSequenceMulDesc

/-- error: Unknown constant `CategoryTheory.Sequence.tensorPowerSequenceOne` -/
#guard_msgs in
#check CategoryTheory.Sequence.tensorPowerSequenceOne

/-- error: Unknown constant `CategoryTheory.Sequence.tensorPowerSequenceMul` -/
#guard_msgs in
#check CategoryTheory.Sequence.tensorPowerSequenceMul

/-- error: Unknown constant `CategoryTheory.Sequence.tensorPowerSequenceMul_fac` -/
#guard_msgs in
#check CategoryTheory.Sequence.tensorPowerSequenceMul_fac

/-- error: Unknown constant `CategoryTheory.Sequence.tensorPowerSequenceMul_fac_tensorObj` -/
#guard_msgs in
#check CategoryTheory.Sequence.tensorPowerSequenceMul_fac_tensorObj

#print axioms CategoryTheory.Sequence.tensorPowerSequence
#print axioms CategoryTheory.Sequence.tensorPowerSequence_obj
#print axioms CategoryTheory.Sequence.tensorPowerSequenceMonObj
#print axioms CategoryTheory.Sequence.tensorPowerSequenceOne_ν
#print axioms CategoryTheory.Sequence.tensorPowerSequenceMul_η
#print axioms CategoryTheory.Sequence.TensorPowerModule
#print axioms CategoryTheory.Sequence.TensorPowerModule.structureMap
#print axioms CategoryTheory.Sequence.TensorPowerModule.structureMap_eq
#print axioms CategoryTheory.Sequence.TensorPowerModule.structureMap_naturality

end MathlibExtTest.CategoryTheory.Monoidal.Sequence.TensorPowerTests
