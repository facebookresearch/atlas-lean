/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

import MathlibExt.RingTheory.Bialgebra.BaseChange
import MathlibExt.RingTheory.HopfAlgebra.Hom
import MathlibExt.Algebra.Lie.UniversalEnveloping.HopfAlgebra
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.Group.ULift
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Reindex
meta import Mathlib.Tactic.NormNum

/-!
# Noncommutative bialgebra base change through two quotient rings

The scalar tower is `ℤ → ZMod 12 → ZMod 6`. Its first scalar extension is
not flat. The right bialgebra is the enveloping algebra of integral
two-by-two matrices, evaluated after scalar extension in matrices over
`ZMod 6`. Matrix units give nonzero tensor images, distinguish the two
product orders, and detect a nonzero coproduct cross coefficient.
Two nonzero scalar coefficients can multiply to zero in the final quotient.

The antipode reverses the product order. Simultaneous exchange of the
two matrix indices gives a nonidentity naturality square whose two
images have coefficient one.
-/

noncomputable section

open scoped TensorProduct

namespace MathlibExtTest.BialgebraBaseChange

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev S := ZMod 12
private abbrev T := ZMod 6

private def quotient : S →+* T := ZMod.castHom (by decide : 6 ∣ 12) T

private instance : Algebra S T := quotient.toAlgebra

private instance : IsScalarTower ℤ S T :=
  IsScalarTower.of_algebraMap_eq (fun z => by
    change (z : T) = quotient (z : S)
    exact (map_intCast quotient z).symm)

private abbrev M := Matrix (Fin 2) (Fin 2) ℤ
private abbrev MT := Matrix (Fin 2) (Fin 2) T
private abbrev A := UniversalEnvelopingAlgebra ℤ M
private abbrev X := T ⊗[S] (S ⊗[ℤ] A)
private abbrev Y := T ⊗[ℤ] A

private abbrev K : X ≃ₐc[T] Y := Bialgebra.TensorProduct.cancelBaseChange ℤ S T A

private def e01 : M := Matrix.single 0 1 1
private def e10 : M := Matrix.single 1 0 1

private abbrev y01 : Y := (1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e01
private abbrev y10 : Y := (1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e10
private abbrev x01 : X :=
  (1 : T) ⊗ₜ[S] ((7 : S) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e01)
private abbrev x10 : X :=
  (1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e10)

private def reduce : M →ₐ[ℤ] MT := (Algebra.ofId ℤ T).mapMatrix

private def evaluate : A →ₐ[ℤ] MT :=
  UniversalEnvelopingAlgebra.lift ℤ (reduce : M →ₗ⁅ℤ⁆ MT)

private def evaluateBase : Y →ₐ[T] MT := AlgHom.liftEquiv ℤ T A MT evaluate

private lemma evaluateBase_generator (m : M) :
    evaluateBase ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) =
      m.map (algebraMap ℤ T) := by
  change (AlgHom.liftEquiv ℤ T A MT evaluate)
    ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) = m.map (algebraMap ℤ T)
  rw [AlgHom.liftEquiv_tmul, one_smul]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ (reduce : M →ₗ⁅ℤ⁆ MT) m

private lemma evaluateBase_y01 : evaluateBase y01 = Matrix.single 0 1 (1 : T) := by
  rw [evaluateBase_generator]
  ext i j
  simp only [e01, Matrix.map_apply, Matrix.single_apply, apply_ite, map_one, map_zero]

private lemma evaluateBase_y10 : evaluateBase y10 = Matrix.single 1 0 (1 : T) := by
  rw [evaluateBase_generator]
  ext i j
  simp only [e10, Matrix.map_apply, Matrix.single_apply, apply_ite, map_one, map_zero]

private lemma seven_action : (7 : S) • (1 : T) = 1 := by
  change quotient (7 : S) * (1 : T) = 1
  rw [map_natCast, mul_one]
  norm_num

private lemma K_x01 : K x01 = y01 := by
  rw [Bialgebra.TensorProduct.cancelBaseChange_tmul, seven_action]

private lemma K_x10 : K x10 = y10 := by
  rw [Bialgebra.TensorProduct.cancelBaseChange_tmul, one_smul]

private lemma product_entry : evaluateBase (y01 * y10) 0 0 = 1 := by
  rw [map_mul, evaluateBase_y01, evaluateBase_y10, Matrix.single_mul_single_same]
  norm_num [Matrix.single_apply]

private lemma reverse_entry : evaluateBase (y10 * y01) 0 0 = 0 := by
  rw [map_mul, evaluateBase_y10, evaluateBase_y01, Matrix.single_mul_single_same]
  norm_num [Matrix.single_apply]

private def entry (i j : Fin 2) : Y →ₗ[T] T :=
  (LinearMap.proj j).comp ((LinearMap.proj i).comp evaluateBase.toLinearMap)

private def crossCoefficient : Y ⊗[T] Y →ₗ[T] T :=
  (LinearMap.mul' T T).comp (TensorProduct.map (entry 0 1) (entry 1 0))

private lemma crossCoefficient_tmul (a b : Y) :
    crossCoefficient (a ⊗ₜ[T] b) = evaluateBase a 0 1 * evaluateBase b 1 0 := by
  simp only [crossCoefficient, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, entry, LinearMap.proj_apply, AlgHom.toLinearMap_apply]

private lemma comul_generator (m : M) :
    Coalgebra.comul (R := T) ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) =
      (1 : Y) ⊗ₜ[T] ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) +
        ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) ⊗ₜ[T] (1 : Y) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, UniversalEnvelopingAlgebra.comul_ι]
  simp only [TensorProduct.tmul_add, map_add,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.one_def]

private lemma product_crossCoefficient :
    crossCoefficient (Coalgebra.comul (R := T) (y01 * y10)) = 1 := by
  have h01 : Coalgebra.comul (R := T) y01 = (1 : Y) ⊗ₜ[T] y01 + y01 ⊗ₜ[T] (1 : Y) :=
    comul_generator e01
  have h10 : Coalgebra.comul (R := T) y10 = (1 : Y) ⊗ₜ[T] y10 + y10 ⊗ₜ[T] (1 : Y) :=
    comul_generator e10
  rw [Bialgebra.comul_mul, h01, h10]
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    map_add, crossCoefficient_tmul, map_one, evaluateBase_y01, evaluateBase_y10]
  norm_num [Matrix.one_apply, Matrix.single_apply]

private lemma antipode_generator (m : M) :
    HopfAlgebra.antipode T ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) =
      -((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ m) := by
  simp only [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
    CommSemiring.antipode_eq_id, LinearMap.id_apply,
    UniversalEnvelopingAlgebra.antipode_ι, TensorProduct.tmul_neg]

private def flip : M →ₗ⁅ℤ⁆ M :=
  ((Matrix.reindexAlgEquiv ℤ ℤ (Equiv.swap (0 : Fin 2) 1)).toAlgHom : M →ₗ⁅ℤ⁆ M)

private lemma flip_e01 : flip e01 = e10 := by
  change Matrix.reindex (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) e01 = e10
  decide

private def F : A →ₐc[ℤ] A := UniversalEnvelopingAlgebra.mapBialgHom ℤ flip

private lemma F_generator :
    F (UniversalEnvelopingAlgebra.ι ℤ e01) = UniversalEnvelopingAlgebra.ι ℤ e10 := by
  simp only [F, UniversalEnvelopingAlgebra.mapBialgHom_apply,
    UniversalEnvelopingAlgebra.map_ι, flip_e01]

private def FT : Y →ₐc[T] Y := Bialgebra.TensorProduct.map (BialgHom.id T T) F

private def FST : X →ₐc[T] X :=
  Bialgebra.TensorProduct.map (BialgHom.id T T)
    (Bialgebra.TensorProduct.map (BialgHom.id S S) F)

example : ¬ Module.Flat ℤ S := by
  intro h
  letI : Module.Flat ℤ S := h
  have hinj : Function.Injective (algebraMap ℤ S) := FaithfulSMul.algebraMap_injective ℤ S
  have hzero : algebraMap ℤ S (12 : ℤ) = algebraMap ℤ S 0 := by norm_num
  have hbad : (12 : ℤ) = 0 := hinj hzero
  norm_num at hbad

example : K x01 = y01 := K_x01

example : K ((2 : T) ⊗ₜ[S]
    ((3 : S) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e01)) = 0 ∧
    (2 : T) ≠ 0 ∧ (3 : T) ≠ 0 := by
  have hscalar : (3 : S) • (2 : T) = 0 := by
    change quotient (3 : S) * (2 : T) = 0
    rw [map_natCast]
    norm_num
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [Bialgebra.TensorProduct.cancelBaseChange_tmul, hscalar, TensorProduct.zero_tmul]

example : K.symm y01 =
    (1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e01) :=
  Bialgebra.TensorProduct.cancelBaseChange_symm_tmul ℤ S T A 1 _

example : evaluateBase (K x01) 0 1 = 1 := by
  rw [K_x01, evaluateBase_y01]
  norm_num [Matrix.single_apply]

example : x01 ≠ 0 := by
  intro h
  have hv := congrArg (fun x : X => evaluateBase (K x) 0 1) h
  rw [K_x01, evaluateBase_y01, map_zero, map_zero] at hv
  norm_num [Matrix.single_apply] at hv

example : evaluateBase (K (x01 * x10)) 0 0 = 1 := by
  rw [map_mul, K_x01, K_x10]
  exact product_entry

example : evaluateBase (K (x10 * x01)) 0 0 = 0 := by
  rw [map_mul, K_x10, K_x01]
  exact reverse_entry

example : x01 * x10 ≠ x10 * x01 := by
  intro h
  have hv := congrArg (fun x : X => evaluateBase (K x) 0 0) h
  rw [map_mul, map_mul, K_x01, K_x10, product_entry, reverse_entry] at hv
  exact (by decide : (1 : T) ≠ 0) hv

example : Coalgebra.counit (R := T) (K x01) = 0 := by
  rw [K_x01]
  simp only [TensorProduct.counit_tmul, UniversalEnvelopingAlgebra.counit_ι, zero_smul]

example : crossCoefficient
    (TensorProduct.map K.toBialgHom.toLinearMap K.toBialgHom.toLinearMap
      (Coalgebra.comul (R := T) (x01 * x10))) = 1 := by
  have h : TensorProduct.map K.toBialgHom.toLinearMap K.toBialgHom.toLinearMap
      (Coalgebra.comul (R := T) (x01 * x10)) =
        Coalgebra.comul (R := T) (K (x01 * x10)) :=
    LinearMap.congr_fun K.toBialgHom.map_comp_comul (x01 * x10)
  rw [h, map_mul, K_x01, K_x10]
  exact product_crossCoefficient

example : evaluateBase (K (HopfAlgebra.antipode T x01)) 0 1 = 5 := by
  rw [K.toBialgHom.map_antipode, K_x01, antipode_generator, map_neg, evaluateBase_y01]
  norm_num [Matrix.neg_apply, Matrix.single_apply]

example : evaluateBase (K (HopfAlgebra.antipode T (x01 * x10))) 1 1 = 1 := by
  rw [K.toBialgHom.map_antipode, map_mul, K_x01, K_x10,
    HopfAlgebra.antipode_mul_antidistrib, antipode_generator, antipode_generator, neg_mul_neg,
    map_mul, evaluateBase_y10, evaluateBase_y01, Matrix.single_mul_single_same]
  norm_num [Matrix.single_apply]

example : evaluateBase (FT (K x01)) 1 0 = 1 ∧ evaluateBase (K (FST x01)) 1 0 = 1 := by
  have hsquare : FT (K x01) = K (FST x01) :=
    DFunLike.congr_fun (Bialgebra.TensorProduct.cancelBaseChange_naturality ℤ S T A F) x01
  have hvalue : evaluateBase (FT (K x01)) 1 0 = 1 := by
    rw [K_x01]
    change evaluateBase
      (Bialgebra.TensorProduct.map (BialgHom.id T T) F
        ((1 : T) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ e01)) 1 0 = 1
    rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, F_generator]
    rw [evaluateBase_y10]
    norm_num [Matrix.single_apply]
  exact ⟨hvalue, by rw [← hsquare]; exact hvalue⟩

/-!
## Group-algebra scalar extension with a larger carrier

The group-algebra carrier lies in `Type 1`, while the three scalar rings
lie in `Type 0`. Cancellation sends the coefficient seven to one, and the
counit detects the nonzero image of an integer-exponent basis element.
-/

namespace LiftedGroup

private abbrev G : Type 1 := ULift.{1} (Multiplicative ℤ)
private abbrev A₁ : Type 1 := MonoidAlgebra ℤ G
private abbrev X₁ : Type 1 := T ⊗[S] (S ⊗[ℤ] A₁)
private abbrev Y₁ : Type 1 := T ⊗[ℤ] A₁

private abbrev comparison : X₁ ≃ₐc[T] Y₁ :=
  Bialgebra.TensorProduct.cancelBaseChange ℤ S T A₁

private def basis : A₁ :=
  MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd 1)) 1

private abbrev source : X₁ := (1 : T) ⊗ₜ[S] ((7 : S) ⊗ₜ[ℤ] basis)
private abbrev target : Y₁ := (1 : T) ⊗ₜ[ℤ] basis

/-- Cancellation of a lifted group basis element preserves a counit of one. -/
example : comparison source = target ∧
    Coalgebra.counit (R := T) (comparison source) = 1 ∧
    source ≠ 0 ∧ target ≠ 0 := by
  have hcomparison : comparison source = target := by
    change Bialgebra.TensorProduct.cancelBaseChange ℤ S T A₁
      ((1 : T) ⊗ₜ[S] ((7 : S) ⊗ₜ[ℤ] basis)) = (1 : T) ⊗ₜ[ℤ] basis
    rw [Bialgebra.TensorProduct.cancelBaseChange_tmul, seven_action]
  have hbasis : Coalgebra.counit (R := ℤ) basis = 1 := by
    simp only [basis, MonoidAlgebra.counit_single, Bialgebra.counit_one]
  have htarget : Coalgebra.counit (R := T) target = 1 := by
    change Coalgebra.counit (R := T) ((1 : T) ⊗ₜ[ℤ] basis) = 1
    rw [TensorProduct.counit_tmul, hbasis, Bialgebra.counit_one, one_smul]
  refine ⟨hcomparison, by rw [hcomparison, htarget], ?_, ?_⟩
  · intro h
    have hv := congrArg
      (fun x : X₁ => Coalgebra.counit (R := T) (comparison x)) h
    rw [hcomparison, htarget, map_zero, map_zero] at hv
    exact (by decide : (1 : T) ≠ 0) hv
  · intro h
    have hv := congrArg (Coalgebra.counit (R := T) : Y₁ →ₗ[T] T) h
    rw [htarget, map_zero] at hv
    exact (by decide : (1 : T) ≠ 0) hv

end LiftedGroup

end MathlibExtTest.BialgebraBaseChange
