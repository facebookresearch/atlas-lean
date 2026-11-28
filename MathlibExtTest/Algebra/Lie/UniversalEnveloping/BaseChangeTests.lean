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

import MathlibExt.Algebra.Lie.UniversalEnveloping.BaseChange
import MathlibExt.RingTheory.HopfAlgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Algebra.Lie.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis
meta import Mathlib.Tactic.NormNum

/-!
# Enveloping scalar extension for torsion and matrix Lie algebras

The scalar ring is `ZMod 6` over `ℤ`. The Lie algebra `ZMod 3`, with its
abelian commutator bracket, is not projective over `ℤ`. A coefficient-five
generator has nonzero evaluation two, and its antipode has evaluation
one. The diagonal Lie morphism and first projection give a nonidentity
scalar-extension naturality square.

Integral matrix Lie generators provide a second model. A linear matrix
coefficient detects a nonzero commutator after the inverse comparison.
The original integral matrix module carries only its `ℤ`-action.
-/

noncomputable section

open scoped TensorProduct

namespace MathlibExtTest.UniversalEnvelopingBaseChange

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev S := ZMod 6
private abbrev L := ZMod 3
private abbrev T := ZMod 3

private def quotient : S →+* T := ZMod.castHom (by decide : 3 ∣ 6) T

private instance : Algebra S T := quotient.toAlgebra

private instance : IsScalarTower ℤ S T :=
  IsScalarTower.of_algebraMap_eq (fun z => by
    change (z : T) = quotient (z : S)
    exact (map_intCast quotient z).symm)

private abbrev U := UniversalEnvelopingAlgebra ℤ L
private abbrev SL := S ⊗[ℤ] L
private abbrev V := UniversalEnvelopingAlgebra S SL
private abbrev B := S ⊗[ℤ] U

private abbrev K : B ≃ₐc[S] V := UniversalEnvelopingAlgebra.baseChangeEquiv ℤ S L
private abbrev b : B := (5 : S) ⊗ₜ[ℤ] UniversalEnvelopingAlgebra.ι ℤ (1 : L)
private abbrev g : V := UniversalEnvelopingAlgebra.ι S ((5 : S) ⊗ₜ[ℤ] (1 : L))

private lemma bracket_SL_zero (x y : SL) : ⁅x, y⁆ = 0 := by
  refine x.inductionOn ?_ ?_
  · intro s x
    refine y.inductionOn ?_ ?_
    · intro t y
      simp only [LieAlgebra.ExtendScalars.bracket_tmul,
        LieRing.of_associative_ring_bracket, mul_comm x y, sub_self,
        TensorProduct.tmul_zero]
    · intro y y' hy hy'
      simp only [lie_add, hy, hy', add_zero]
  · intro x x' hx hx'
    simp only [add_lie, hx, hx', add_zero]

private def evaluateLie : SL →ₗ⁅S⁆ T where
  toLinearMap := (LinearMap.id : L →ₗ[ℤ] T).liftBaseChange S
  map_lie' := by
    intro x y
    rw [bracket_SL_zero, map_zero]
    simp only [LieRing.of_associative_ring_bracket, mul_comm, sub_self]

private def evaluate : V →ₐ[S] T := UniversalEnvelopingAlgebra.lift S evaluateLie

private lemma evaluate_generator : evaluate g = 2 := by
  change UniversalEnvelopingAlgebra.lift S evaluateLie
    (UniversalEnvelopingAlgebra.ι S ((5 : S) ⊗ₜ[ℤ] (1 : L))) = 2
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change quotient (5 : S) * (1 : T) = 2
  rw [map_natCast, mul_one]
  norm_num

private lemma K_b : K b = g :=
  UniversalEnvelopingAlgebra.baseChangeEquiv_tmul_ι ℤ S L 5 1

private def diagonal : L →ₗ⁅ℤ⁆ L × L :=
  (LieHom.id : L →ₗ⁅ℤ⁆ L).prod LieHom.id

private def first : L × L →ₗ⁅ℤ⁆ L := LieHom.fst ℤ L L

private lemma first_diagonal (x : L) : first (diagonal x) = x := rfl

private abbrev V₂ := UniversalEnvelopingAlgebra S (S ⊗[ℤ] (L × L))

private def evaluate₂ : V₂ →ₐ[S] T :=
  evaluate.comp (UniversalEnvelopingAlgebra.mapBialgHom S
    (LieHom.baseChange ℤ S first)).toAlgHom

example : ¬ Module.Flat ℤ S := by
  intro h
  letI : Module.Flat ℤ S := h
  have hinj : Function.Injective (algebraMap ℤ S) := FaithfulSMul.algebraMap_injective ℤ S
  have hzero : algebraMap ℤ S (6 : ℤ) = algebraMap ℤ S 0 := by norm_num
  have hbad : (6 : ℤ) = 0 := hinj hzero
  norm_num at hbad

example : ¬ Module.Projective ℤ L := by
  intro h
  letI : Module.Projective ℤ L := h
  letI : Module.Flat ℤ L := inferInstance
  have hinj : Function.Injective (algebraMap ℤ L) := FaithfulSMul.algebraMap_injective ℤ L
  have hzero : algebraMap ℤ L (3 : ℤ) = algebraMap ℤ L 0 := by norm_num
  have hbad : (3 : ℤ) = 0 := hinj hzero
  norm_num at hbad

example : K b = g := K_b

example : K.symm g = b :=
  UniversalEnvelopingAlgebra.baseChangeEquiv_symm_ι_tmul ℤ S L 5 1

example : evaluate (K b) = 2 := by rw [K_b, evaluate_generator]

example : g ≠ 0 := by
  intro h
  have hv := congrArg evaluate h
  rw [evaluate_generator, map_zero] at hv
  exact (by decide : (2 : T) ≠ 0) hv

example : b ≠ 0 := by
  intro h
  have hv := congrArg (fun x : B => evaluate (K x)) h
  rw [K_b, evaluate_generator] at hv
  simp only [map_zero] at hv
  exact (by decide : (2 : T) ≠ 0) hv

example : evaluate (K (HopfAlgebra.antipode S b)) = 1 := by
  rw [K.toBialgHom.map_antipode, K_b, UniversalEnvelopingAlgebra.antipode_ι,
    map_neg, evaluate_generator]
  norm_num

example : (LieHom.baseChange ℤ S first).comp (LieHom.baseChange ℤ S diagonal) =
    (LieHom.id : SL →ₗ⁅S⁆ SL) := by
  rw [← LieHom.baseChange_comp]
  have h : first.comp diagonal = (LieHom.id : L →ₗ⁅ℤ⁆ L) := by
    apply LieHom.ext
    intro x
    rfl
  rw [h, LieHom.baseChange_id]

example : evaluate₂
    (UniversalEnvelopingAlgebra.mapBialgHom S (LieHom.baseChange ℤ S diagonal) (K b)) = 2 ∧
    evaluate₂ (UniversalEnvelopingAlgebra.baseChangeEquiv ℤ S (L × L)
      (Bialgebra.TensorProduct.map (BialgHom.id S S)
        (UniversalEnvelopingAlgebra.mapBialgHom ℤ diagonal) b)) = 2 := by
  have hsquare := DFunLike.congr_fun
    (UniversalEnvelopingAlgebra.baseChangeEquiv_naturality ℤ S L diagonal) b
  have hvalue : evaluate₂
      (UniversalEnvelopingAlgebra.mapBialgHom S (LieHom.baseChange ℤ S diagonal) (K b)) = 2 := by
    rw [K_b, UniversalEnvelopingAlgebra.mapBialgHom_apply,
      UniversalEnvelopingAlgebra.map_ι, LieHom.baseChange_tmul]
    change evaluate
      (UniversalEnvelopingAlgebra.mapBialgHom S (LieHom.baseChange ℤ S first)
        (UniversalEnvelopingAlgebra.ι S ((5 : S) ⊗ₜ[ℤ] diagonal (1 : L)))) = 2
    rw [UniversalEnvelopingAlgebra.mapBialgHom_apply, UniversalEnvelopingAlgebra.map_ι,
      LieHom.baseChange_tmul, first_diagonal]
    exact evaluate_generator
  exact ⟨hvalue, by rw [← hsquare]; exact hvalue⟩

private abbrev M := Matrix (Fin 2) (Fin 2) ℤ
private abbrev UM := UniversalEnvelopingAlgebra ℤ M
private abbrev VSM := UniversalEnvelopingAlgebra S (S ⊗[ℤ] M)

private abbrev KM : S ⊗[ℤ] UM ≃ₐc[S] VSM :=
  UniversalEnvelopingAlgebra.baseChangeEquiv ℤ S M

private def e01 : M := Matrix.single 0 1 1
private def e10 : M := Matrix.single 1 0 1

private abbrev m01 : VSM := UniversalEnvelopingAlgebra.ι S ((1 : S) ⊗ₜ[ℤ] e01)
private abbrev m10 : VSM := UniversalEnvelopingAlgebra.ι S ((1 : S) ⊗ₜ[ℤ] e10)

private def matrixEvaluate : UM →ₐ[ℤ] M :=
  UniversalEnvelopingAlgebra.lift ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M)

private def matrixEntry : UM →ₗ[ℤ] ℤ :=
  (LinearMap.proj (0 : Fin 2)).comp
    ((LinearMap.proj (0 : Fin 2)).comp matrixEvaluate.toLinearMap)

private def matrixCoefficient : S ⊗[ℤ] UM →ₗ[S] S :=
  ((Algebra.ofId ℤ S).toLinearMap.comp matrixEntry).liftBaseChange S

private lemma matrixCoefficient_tmul (s : S) (a : UM) :
    matrixCoefficient (s ⊗ₜ[ℤ] a) = s • algebraMap ℤ S (matrixEvaluate a 0 0) := by
  simp only [matrixCoefficient, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, matrixEntry, LinearMap.proj_apply]

private lemma matrixEvaluate_generator (m : M) :
    matrixEvaluate (UniversalEnvelopingAlgebra.ι ℤ m) = m :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M) m

private lemma matrix_commutator_value :
    matrixCoefficient (KM.symm (m01 * m10 - m10 * m01)) = 1 := by
  simp only [map_sub, map_mul, UniversalEnvelopingAlgebra.baseChangeEquiv_symm_ι_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub]
  rw [matrixCoefficient_tmul, one_smul]
  simp only [map_sub, map_mul, matrixEvaluate_generator]
  norm_num [e01, e10, Matrix.single_mul_single_same, Matrix.single_apply]

example : matrixCoefficient (KM.symm (m01 * m10 - m10 * m01)) = 1 := matrix_commutator_value

example : m01 * m10 - m10 * m01 ≠ 0 := by
  intro h
  have hv := congrArg (fun x : VSM => matrixCoefficient (KM.symm x)) h
  rw [matrix_commutator_value] at hv
  simp only [map_zero] at hv
  exact (by decide : (1 : S) ≠ 0) hv

end MathlibExtTest.UniversalEnvelopingBaseChange
