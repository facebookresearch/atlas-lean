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

public import MathlibExt.Algebra.Homology.TensorDifferentialUpInt
public import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexCochainSquare

/-!
# Differential Leibniz laws for chain-map tensors

Let C be a preadditive monoidal category whose tensor is additive in
both variables and whose integer-graded tensor products exist.
For a cochain complex K with differential d, a chain map
Δ:K → K⊗K satisfies Δ∘d=(d⊗1)∘Δ+(1⊗d)∘Δ.
A chain map μ:K⊗K → K satisfies
d∘μ=μ∘(d⊗1)+μ∘(1⊗d).
The graded tensor products use their Koszul signs, with the
left-differentiated term first.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]
variable {K : CochainComplex C ℤ}

variable [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]

/-- Let C be preadditive monoidal, with tensor additive in both variables
and all integer-graded tensor objects available. Let K be an
integer-indexed cochain complex, d its degree-one differential, and
1 its identity cochain. Tensor products of cochains use Koszul signs.

For any chain map Δ:K → K⊗K, the co-Leibniz equation is Δ∘d=(d⊗1)∘Δ+(1⊗d)∘Δ. -/
theorem dgInternal_coLeibniz_carrier
    (D : K ⟶ HomologicalComplex.tensorObj K K) :
    (HomComplex.Cochain.diff K).comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
            (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
            (HomComplex.Cochain.diff K))
          (show (0 : ℤ) + (0 + 1) = 1 by omega) := by
  have hchain := HomComplex.Cochain.ofHom_comp_diff D
  have hdecomp := diff_tensorObj K K
  calc (HomComplex.Cochain.diff K).comp (HomComplex.Cochain.ofHom D)
          (add_zero 1)
      = (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.diff (HomologicalComplex.tensorObj K K))
          (zero_add 1) := hchain.symm
    _ = (HomComplex.Cochain.ofHom D).comp
          (Add.add (α := HomComplex.Cochain (HomologicalComplex.tensorObj K K)
              (HomologicalComplex.tensorObj K K) 1)
            (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K)))
            (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K))) (zero_add 1) := by rw [hdecomp]
    _ = (HomComplex.Cochain.ofHom D).comp
            (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K))) (zero_add 1) +
          (HomComplex.Cochain.ofHom D).comp
            (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K)) (zero_add 1) :=
        HomComplex.Cochain.comp_add _ _ _ _
    _ = _ := rfl

/-- Let C be preadditive monoidal, with tensor additive in both variables
and all integer-graded tensor objects available. Let K be an
integer-indexed cochain complex, d its degree-one differential, and
1 its identity cochain. Tensor products of cochains use Koszul signs.

For any chain map μ:K⊗K → K, the Leibniz equation is d∘μ=μ∘(d⊗1)+μ∘(1⊗d). -/
theorem dgInternal_leibniz_carrier
    (μ : HomologicalComplex.tensorObj K K ⟶ K) :
    (HomComplex.Cochain.ofHom μ).comp (HomComplex.Cochain.diff K) (zero_add 1) =
      (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
          (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
          (HomComplex.Cochain.diff K)).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := by
  have hchain := HomComplex.Cochain.ofHom_comp_diff μ
  have hdecomp := diff_tensorObj K K
  calc (HomComplex.Cochain.ofHom μ).comp (HomComplex.Cochain.diff K)
          (zero_add 1)
      = (HomComplex.Cochain.diff (HomologicalComplex.tensorObj K K)).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := hchain
    _ = (Add.add (α := HomComplex.Cochain (HomologicalComplex.tensorObj K K)
              (HomologicalComplex.tensorObj K K) 1)
            (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K)))
            (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := by rw [hdecomp]
    _ = (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K))).comp
            (HomComplex.Cochain.ofHom μ) (add_zero 1) +
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K)).comp
            (HomComplex.Cochain.ofHom μ) (add_zero 1) :=
        HomComplex.Cochain.add_comp _ _ _ _
    _ = _ := rfl

end CochainComplex
