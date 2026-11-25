/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DerivedOrientationModels
import MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
import MathlibExt.Algebra.Homology.ShiftedTensorUnits
import Mathlib.Algebra.TrivSqZeroExt.Basic

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.ShiftedTensorUnits
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
open CochainComplex.HomComplex
open scoped Simplicial

noncomputable section

-- A genuine nilpotent coefficient is retained, with no reduction to field-valued points.
abbrev Dual := TrivSqZeroExt ℚ ℚ
def epsilon : Dual := TrivSqZeroExt.inr 1

example : epsilon ≠ 0 := by
  intro h
  have h' := congrArg TrivSqZeroExt.snd h
  norm_num [epsilon] at h'

example : epsilon * epsilon = 0 := by simp [epsilon]

def scalarAlgebra : SAlg ℚ :=
  (SimplicialObject.const (CommAlgCat ℚ)).obj (CommAlgCat.of ℚ ℚ)

def nilpotentAlgebra : SAlg ℚ :=
  (SimplicialObject.const (CommAlgCat ℚ)).obj (CommAlgCat.of ℚ Dual)

example (M : SimplicialDRModel scalarAlgebra)
    (P : SimplicialDRModel (productAlgebra scalarAlgebra nilpotentAlgebra))
    (F : ProjectionModel scalarAlgebra nilpotentAlgebra M P) :
    (((P.termIso 0 (op ⦋0⦌)).inv ≫ (F.map 0).app (op ⦋0⦌) ≫
      ((M.termIso 0 (op ⦋0⦌)).hom ⊗ₘ 𝟙 ((coefficients nilpotentAlgebra).obj (op ⦋0⦌)))).hom
      (formGenerator (productAlgebra scalarAlgebra nilpotentAlgebra) 0 (op ⦋0⦌)
        (fun _ => TensorProduct.tmul ℚ (1 : ℚ) epsilon))) =
      TensorProduct.tmul ℚ (formGenerator scalarAlgebra 0 (op ⦋0⦌) (fun _ => 1)) epsilon := by
  have h := F.generator 0 (op ⦋0⦌) (fun _ => 1) (fun _ => epsilon)
  have hp : (∏ _i : Fin 1, (epsilon : nilpotentAlgebra.obj (op ⦋0⦌))) = epsilon := by
    rw [Fin.prod_univ_succ]
    simp
  exact h.trans (congrArg (TensorProduct.tmul ℚ
    (formGenerator scalarAlgebra 0 (op ⦋0⦌) (fun _ => 1))) hp)

-- A trace degree -1 places the target in shift[-1], with the native tensor sign.
example (X : Cochains ℚ) (U : UnitTensorModel X (-1)) (x : X.X 1) :
    (((HomologicalComplex.ιTensorObj X ((𝟙_ (Cochains ℚ))⟦(-1 : ℤ)⟧)
      1 1 2 (by omega)) ≫ (U.comparison.hom.f 2) ≫
        (CochainComplex.shiftFunctorObjXIso X (-1) 2 1 (by omega)).hom).hom
      (TensorProduct.tmul ℚ x (shiftedUnit (-1) (1 : ℚ)))) = -x := by
  simpa using U.normalized 1 x (1 : ℚ)
