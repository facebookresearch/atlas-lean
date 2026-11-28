/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.TensorCochainCoherence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Addition of degree-one co-Leibniz cochains

In a preadditive monoidal category with bilinear graded tensor products,
let Δ:K → K⊗K be a chain map on an integer-indexed cochain complex.
If degree-one cochains F_i and F_e each satisfy
Δ∘F=(F⊗1)∘Δ+(1⊗F)∘Δ,
their sum satisfies the same co-Leibniz equation.
Tensor products of cochains retain the Koszul signs and the two
terms occur in left-leg, right-leg order.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
variable {K : CochainComplex C ℤ}

variable [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]

/-- Let C be preadditive monoidal with bilinear tensor and all
integer-graded tensor objects available. Let K be an integer-indexed
cochain complex and 1 its identity cochain.
Let Δ:K → K⊗K be a chain map and F_i,F_e degree-one cochains.
If Δ∘F=(F⊗1)∘Δ+(1⊗F)∘Δ for each F=F_i,F_e, then
Δ∘(F_i+F_e)=((F_i+F_e)⊗1)∘Δ+(1⊗(F_i+F_e))∘Δ,
using the graded tensor signs. -/
theorem dgTotal_coLeibniz_combination
    (D : K ⟶ HomologicalComplex.tensorObj K K)
    (Fi FE : HomComplex.Cochain K K 1)
    (hFi : Fi.comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor Fi (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) Fi)
          (show (0 : ℤ) + (0 + 1) = 1 by omega))
    (hFE : FE.comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor FE (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) FE)
          (show (0 : ℤ) + (0 + 1) = 1 by omega)) :
    (Fi + FE).comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (Fi + FE) (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) (Fi + FE))
          (show (0 : ℤ) + (0 + 1) = 1 by omega) := by
  rw [HomComplex.Cochain.add_comp, hFi, hFE,
    HomComplex.Cochain.tensor_add_left, HomComplex.Cochain.tensor_add_right]
  simp only [HomComplex.Cochain.comp_add]
  apply add_add_add_comm

end CochainComplex
