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
# Addition of degree-one Leibniz cochains

In a preadditive monoidal category with bilinear graded tensor products,
let μ:K⊗K → K be a chain map on an integer-indexed cochain complex.
If degree-one cochains F_i and F_e each satisfy
F∘μ=μ∘(F⊗1)+μ∘(1⊗F),
their sum satisfies the same Leibniz equation.
The graded tensor products retain the Koszul signs, with the
left-leg term before the right-leg term.
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
Let μ:K⊗K → K be a chain map and F_i,F_e degree-one cochains.
If F∘μ=μ∘(F⊗1)+μ∘(1⊗F) for each F=F_i,F_e, then
(F_i+F_e)∘μ=μ∘((F_i+F_e)⊗1)+μ∘(1⊗(F_i+F_e)),
using the graded tensor signs. -/
theorem dgTotal_leibniz_combination
    (μ : HomologicalComplex.tensorObj K K ⟶ K)
    (Fi FE : HomComplex.Cochain K K 1)
    (hFi : (HomComplex.Cochain.ofHom μ).comp Fi (zero_add 1) =
      (HomComplex.Cochain.tensor Fi (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) Fi).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1))
    (hFE : (HomComplex.Cochain.ofHom μ).comp FE (zero_add 1) =
      (HomComplex.Cochain.tensor FE (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) FE).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)) :
    (HomComplex.Cochain.ofHom μ).comp (Fi + FE) (zero_add 1) =
      (HomComplex.Cochain.tensor (Fi + FE)
          (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
          (Fi + FE)).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := by
  rw [HomComplex.Cochain.comp_add, hFi, hFE,
    HomComplex.Cochain.tensor_add_left, HomComplex.Cochain.tensor_add_right]
  simp only [HomComplex.Cochain.add_comp]
  apply add_add_add_comm

end CochainComplex
