/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.ExactLimits
import MathlibExt.Algebra.Homology.BifunctorBraiding
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Data.ZMod.Basic

/-!
# Exact finite limits and braiding on different complex axes

Finite products of integer modules are exact, so homology preserves their
limits by instance resolution from the actual module-category AB4* structure.
A chain direction indexed by natural numbers and a cyclic cochain direction
indexed by ZMod2 both have nonzero integer coefficients. The native bicomplex
braiding swaps the factors of the pure tensor 2 ⊗ 3 in cell (2,1), and its
inverse recovers the original factors. The two axes retain their shapes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace MathlibExtTest.ExactLimitsBraiding

private abbrev C := ModuleCat.{0} ℤ

example : PreservesLimitsOfShape (Discrete (Fin 2))
    (homologyFunctor C (ComplexShape.down ℕ) 0) := inferInstance

private def integerComplex {ι : Type} (c : ComplexShape ι) : HomologicalComplex C c where
  X _ := ModuleCat.of ℤ ℤ
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private abbrev K : ChainComplex C ℕ := integerComplex (ComplexShape.down ℕ)
private abbrev L : CochainComplex C (ZMod 2) := integerComplex (ComplexShape.up (ZMod 2))

example :
    (((((mapBifunctorBraidingNatIso (c₁ := ComplexShape.down ℕ)
      (c₂ := ComplexShape.up (ZMod 2))).hom.app K).app L).f 2).f 1).hom
        ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ)) = (3 : ℤ) ⊗ₜ[ℤ] (2 : ℤ) := by
  have h := congrArg (fun f => (f.f 2).f 1)
    (mapBifunctorBraidingNatIso_hom_app_app K L)
  have hc := h.trans (mapBifunctorBraidingIso_hom_f_f K L 2 1)
  exact (congrArg (fun f => f.hom ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ))) hc).trans
    (ModuleCat.MonoidalCategory.braiding_hom_apply (2 : ℤ) (3 : ℤ))

example :
    (((((mapBifunctorBraidingNatIso (c₁ := ComplexShape.down ℕ)
      (c₂ := ComplexShape.up (ZMod 2))).inv.app K).app L).f 2).f 1).hom
        ((3 : ℤ) ⊗ₜ[ℤ] (2 : ℤ)) = (2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ) := by
  have h := congrArg (fun f => (f.f 2).f 1)
    (mapBifunctorBraidingNatIso_inv_app_app K L)
  have hc := h.trans (mapBifunctorBraidingIso_inv_f_f K L 2 1)
  exact (congrArg (fun f => f.hom ((3 : ℤ) ⊗ₜ[ℤ] (2 : ℤ))) hc).trans
    (ModuleCat.MonoidalCategory.braiding_inv_apply (2 : ℤ) (3 : ℤ))

/-! ### Rank-two integer coefficient coordinates -/

private abbrev V := Fin 2 → ℤ

private def vectorComplex {ι : Type} (c : ComplexShape ι) : HomologicalComplex C c where
  X _ := ModuleCat.of ℤ V
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private abbrev vectorK : ChainComplex C ℕ := vectorComplex (ComplexShape.down ℕ)
private abbrev vectorL : CochainComplex C (ZMod 2) :=
  vectorComplex (ComplexShape.up (ZMod 2))

private def firstVector : V := Pi.single 0 1
private def secondVector : V := Pi.single 1 1
private def orderedBasisTensor : V ⊗[ℤ] V := firstVector ⊗ₜ[ℤ] secondVector

private def tensorCoordinate (i j : Fin 2) : V ⊗[ℤ] V →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp
    (TensorProduct.map (LinearMap.proj i : V →ₗ[ℤ] ℤ)
      (LinearMap.proj j : V →ₗ[ℤ] ℤ))

private lemma tensorCoordinate_tmul (i j : Fin 2) (x y : V) :
    tensorCoordinate i j (x ⊗ₜ[ℤ] y) = x i * y j := by
  change (TensorProduct.lid ℤ ℤ)
    (TensorProduct.map (LinearMap.proj i : V →ₗ[ℤ] ℤ)
      (LinearMap.proj j : V →ₗ[ℤ] ℤ) (x ⊗ₜ[ℤ] y)) = x i * y j
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

private def rankTwoBraiding : V ⊗[ℤ] V →ₗ[ℤ] V ⊗[ℤ] V :=
  (((((mapBifunctorBraidingNatIso (c₁ := ComplexShape.down ℕ)
    (c₂ := ComplexShape.up (ZMod 2))).hom.app vectorK).app vectorL).f 2).f 1).hom

private lemma rankTwoBraiding_tmul (x y : V) :
    rankTwoBraiding (x ⊗ₜ[ℤ] y) = y ⊗ₜ[ℤ] x := by
  have h := congrArg (fun f => (f.f 2).f 1)
    (mapBifunctorBraidingNatIso_hom_app_app vectorK vectorL)
  have hc := h.trans (mapBifunctorBraidingIso_hom_f_f vectorK vectorL 2 1)
  exact (congrArg (fun f => f.hom (x ⊗ₜ[ℤ] y)) hc).trans
    (ModuleCat.MonoidalCategory.braiding_hom_apply x y)

-- The off-diagonal coordinates interchange under the actual cell (2,1) braiding.
example :
    tensorCoordinate 0 1 orderedBasisTensor = 1 ∧
      tensorCoordinate 1 0 orderedBasisTensor = 0 ∧
      tensorCoordinate 0 1 (rankTwoBraiding orderedBasisTensor) = 0 ∧
      tensorCoordinate 1 0 (rankTwoBraiding orderedBasisTensor) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [orderedBasisTensor, tensorCoordinate_tmul, firstVector, secondVector]
  · simp [orderedBasisTensor, tensorCoordinate_tmul, firstVector, secondVector]
  · rw [orderedBasisTensor, rankTwoBraiding_tmul, tensorCoordinate_tmul]
    simp [firstVector, secondVector]
  · rw [orderedBasisTensor, rankTwoBraiding_tmul, tensorCoordinate_tmul]
    simp [firstVector, secondVector]

end MathlibExtTest.ExactLimitsBraiding
