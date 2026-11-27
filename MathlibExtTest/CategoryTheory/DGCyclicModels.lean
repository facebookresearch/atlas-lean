/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.DGAlgebraCategoryModels
import MathlibExt.Algebra.Homology.DGCyclicMixedModels
import MathlibExt.CategoryTheory.DGMoritaClosedModels

/-!
# DG algebra and quasi-functor consumers

An honest cochain complex has a nonzero degree-one endomorphism. Its
native enriched product with itself acts as -1 in degree two, detecting
the actual Koszul factor-order sign. The remaining consumers use the
source right-adjoint and higher-Hom outputs without assuming the theorem
in its input constructor.
-/

noncomputable section

namespace DGCyclicModelsTest

open CategoryTheory MonoidalCategory CochainComplex.HomComplex
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.CategoryTheory.DGMoritaClosedModels

abbrev flat : Cochains ℚ where
  X _ := ModuleCat.of ℚ ℚ
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

abbrev odd : DGHom ℚ 1 flat flat :=
  Cochain.mk (fun _ _ _ => ModuleCat.ofHom (LinearMap.id))

example :
    ((multiplyHomogeneous (endomorphismAlgebra flat) odd odd (show (1 : ℤ) + 1 = 2 from rfl) :
      Cochain flat flat 2).v 0 2 (by omega)).hom (1 : ℚ) = -1 := by
  rw [endomorphism_multiply,
    dgComp_v ℚ odd odd (show (1 : ℤ) + 1 = 2 from rfl) 0 1 2 (by omega) (by omega)]
  norm_num [odd, flat, Cochain.v, Cochain.mk]

example (Q : ReplacementFunctor ℚ) (C : DGCat ℚ) (T : LocalizedTensorModel Q C)
    (M : MoritaClosedModel Q C T) (A D : DGCat ℚ)
    (f : T.functor.obj ((toHo ℚ).obj A) ⟶ (toHo ℚ).obj D) :
    (toHo ℚ).obj A ⟶ M.rightAdjoint.obj ((toHo ℚ).obj D) :=
  M.adjunction.homEquiv _ _ f

example (Q : ReplacementFunctor ℚ) (C : DGCat ℚ) (T : LocalizedTensorModel Q C)
    (M : MoritaClosedModel Q C T) (D : DGCat ℚ)
    (x y : (M.quasiFunctorModel D).category) (n : ℤ) (a : DGHom ℚ n x y) :
    DGHom ℚ n ((M.quasiFunctorModel D).realization.obj x)
      ((M.quasiFunctorModel D).realization.obj y) :=
  (M.quasiFunctorModel D).realization.dgMap n a

end DGCyclicModelsTest
