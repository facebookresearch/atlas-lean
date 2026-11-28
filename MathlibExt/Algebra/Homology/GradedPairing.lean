/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Signed pairings of nonnegative cochain complexes

A pairing has components `K₁ᵖ ⊗ K₂^q → K₃^{p+q}` satisfying the Koszul Leibniz rule
`d P(x,y) = P(dx,y) + (-1)^p P(x,dy)`. It transports contravariantly in the first two
complexes and covariantly in the target. When tensoring is additive in both variables,
restriction to cycles gives a pairing whenever the three homology objects exist.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A pairing of nonnegative cochain complexes in a preadditive monoidal category,
with components `P_{p,q} : K₁.X p ⊗ K₂.X q → K₃.X (p+q)` and differential rule
`d P(x,y) = P(dx,y) + (-1)^p P(x,dy)`, using the canonical degree identifications. -/
structure CochainGradedPairing (K₁ K₂ K₃ : CochainComplex C ℕ) where
  /-- The component pairing in degrees `p,q`, taking values in degree `p+q`. -/
  pair : ∀ p q, K₁.X p ⊗ K₂.X q ⟶ K₃.X (p + q)
  /-- Compatibility with the two differentials, with sign `(-1)^p` on the second factor. -/
  leibniz : ∀ p q,
    pair p q ≫ K₃.d (p + q) (p + q + 1) =
      (K₁.d p (p + 1) ⊗ₘ 𝟙 (K₂.X q)) ≫ pair (p + 1) q ≫
          (K₃.XIsoOfEq (show (p + 1) + q = p + q + 1 by omega)).hom +
        ((-1 : ℤ) ^ p) •
          ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q + 1)) ≫ pair p (q + 1) ≫
            (K₃.XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)).hom)

namespace CochainGradedPairing

section Whisker

variable {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex C ℕ}

/-- Let C be a preadditive monoidal category and P a pairing of nonnegative cochain complexes
K₁,K₂,K₃ with components P_{p,q} : K₁,p ⊗ K₂,q → K₃,p+q satisfying dP(x,y) = P(dx,y) + (−1)^p
P(x,dy). For cochain maps f₁ : L₁ → K₁, f₂ : L₂ → K₂ and f₃ : K₃ → L₃, whisker P f₁ f₂ f₃ is the
pairing of L₁,L₂,L₃ with component (f₁,p ⊗ f₂,q) ≫ P_{p,q} ≫ f₃,p+q. -/
noncomputable def whisker (P : CochainGradedPairing K₁ K₂ K₃)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : K₃ ⟶ L₃) :
    CochainGradedPairing L₁ L₂ L₃ where
  pair p q := (f₁.f p ⊗ₘ f₂.f q) ≫ P.pair p q ≫ f₃.f (p + q)
  leibniz p q := by
    simp only [Category.assoc, f₃.comm]
    rw [← Category.assoc (P.pair p q), P.leibniz]
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, Category.id_comp]
    rw [f₁.comm, f₂.comm]
    rw [← XIsoOfEq_hom_naturality, ← XIsoOfEq_hom_naturality]

@[simp]
lemma whisker_pair (P : CochainGradedPairing K₁ K₂ K₃)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : K₃ ⟶ L₃)
    (p q : ℕ) :
    (P.whisker f₁ f₂ f₃).pair p q =
      (f₁.f p ⊗ₘ f₂.f q) ≫ P.pair p q ≫ f₃.f (p + q) :=
  rfl

@[simp]
lemma whisker_id (P : CochainGradedPairing K₁ K₂ K₃) :
    P.whisker (𝟙 K₁) (𝟙 K₂) (𝟙 K₃) = P := by
  cases P
  simp [whisker]

lemma whisker_whisker
    {M₁ M₂ M₃ : CochainComplex C ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : K₃ ⟶ L₃)
    (g₁ : M₁ ⟶ L₁) (g₂ : M₂ ⟶ L₂) (g₃ : L₃ ⟶ M₃) :
    (P.whisker f₁ f₂ f₃).whisker g₁ g₂ g₃ =
      P.whisker (g₁ ≫ f₁) (g₂ ≫ f₂) (f₃ ≫ g₃) := by
  cases P
  simp [whisker, Category.assoc]

end Whisker

variable [MonoidalPreadditive C] {K₁ K₂ K₃ : CochainComplex C ℕ}

lemma pairCycles_d (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] :
    ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
        K₃.d (p + q) (p + q + 1) = 0 := by
  rw [Category.assoc, P.leibniz]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul]
  have h₁ :
      (K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫
          (K₁.d p (p + 1) ⊗ₘ 𝟙 (K₂.X q)) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, K₁.iCycles_d p (p + 1)]
    simp
  have h₂ :
      (K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫
          (𝟙 (K₁.X p) ⊗ₘ K₂.d q (q + 1)) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, K₂.iCycles_d q (q + 1)]
    simp
  simp only [← Category.assoc]
  rw [h₁, h₂]
  simp

/-- In a monoidal preadditive category, restrict a signed pairing to its two cycle objects.
The Leibniz rule makes
its image a cycle in degree `p+q`. Only existence of the three homology objects is
needed; no tensor-cokernel preservation hypothesis is used here. -/
noncomputable def pairCycles (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    K₁.cycles p ⊗ K₂.cycles q ⟶ K₃.cycles (p + q) :=
  K₃.liftCycles
    ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q)
    (p + q + 1) (by simp) (pairCycles_d P p q)

@[reassoc (attr := simp)]
lemma pairCycles_i (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] [K₃.HasHomology (p + q)] :
    P.pairCycles p q ≫ K₃.iCycles (p + q) =
      (K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q :=
  K₃.liftCycles_i _ _ (by simp) _

end CochainGradedPairing

end HomologicalComplex
