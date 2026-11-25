/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantAbutmentImage
public import MathlibExt.Algebra.Homology.SpectralObjectCokernelENaturality

/-! # Tests for fixed-E cokernel-sequence naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ComposableArrows

universe v u vι uι

namespace MathlibExtTest.SpectralObjectCokernelENaturality

open CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y : CategoryTheory.Abelian.SpectralObject C ι}

#check Hom.cokernelSequenceE_toCycles_cyclesMap
#check Hom.cokernelSequenceE_g_EMap

example (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (X.cokernelSequenceE
          f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g ≫
        Hom.EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      (φ.hom n₁).app (mk₁ f₁₂) ≫
        (Y.cokernelSequenceE
          f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g :=
  Hom.cokernelSequenceE_g_EMap
    φ f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

-- Identity spectral-object morphism.
example (X : CategoryTheory.Abelian.SpectralObject C ι) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :=
  Hom.cokernelSequenceE_g_EMap
    (𝟙 X) f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

-- Arbitrary composable index arrows with their literal composite.
example (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (n : ℤ) :
    (X.cokernelSequenceE
          f₁ f₂ f₃ (f₁ ≫ f₂) rfl
          (n - 1) n (n + 1) (by omega) (by omega)).g ≫
        Hom.EMap φ f₁ f₂ f₃
          (n - 1) n (n + 1) (by omega) (by omega) =
      (φ.hom n).app (mk₁ (f₁ ≫ f₂)) ≫
        (Y.cokernelSequenceE
          f₁ f₂ f₃ (f₁ ≫ f₂) rfl
          (n - 1) n (n + 1) (by omega) (by omega)).g := by
  simpa using Hom.cokernelSequenceE_g_EMap
    φ f₁ f₂ f₃ (f₁ ≫ f₂) rfl
      (n - 1) n (n + 1) (by omega) (by omega)

-- Identity index arrows remain a separate boundary case.
example (φ : X ⟶ Y) (i : ι) (n : ℤ) :
    (X.cokernelSequenceE
          (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
          (n - 1) n (n + 1) (by omega) (by omega)).g ≫
        Hom.EMap φ (𝟙 i) (𝟙 i) (𝟙 i)
          (n - 1) n (n + 1) (by omega) (by omega) =
      (φ.hom n).app (mk₁ (𝟙 i)) ≫
        (Y.cokernelSequenceE
          (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
          (n - 1) n (n + 1) (by omega) (by omega)).g := by
  simpa using Hom.cokernelSequenceE_g_EMap
    φ (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
      (n - 1) n (n + 1) (by omega) (by omega)

-- Arbitrary negative consecutive degrees.
example (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (n : ℤ) :=
  Hom.cokernelSequenceE_g_EMap φ f₁ f₂ f₃ f₁₂ h₁₂
    (-n - 1) (-n) (-n + 1) (by omega) (by omega)

section CanonicalShape

variable {XE YE : CategoryTheory.Abelian.SpectralObject C EInt} (φ : XE ⟶ YE)

example (p q : ℕ) :
    (XE.cokernelSequenceE
          (HomologicalComplex₂.horizontalCanonicalAbutmentLowerMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentMiddleMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentUpperMap p q)
          (HomologicalComplex₂.horizontalCanonicalAbutmentLowerCompositeMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentLower_comp_middle p)
          (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
          (-((p + q : ℕ) : ℤ) + 1)).g ≫
        Hom.EMap φ
          (HomologicalComplex₂.horizontalCanonicalAbutmentLowerMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentMiddleMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentUpperMap p q)
          (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
          (-((p + q : ℕ) : ℤ) + 1) =
      (φ.hom (-((p + q : ℕ) : ℤ))).app
          (mk₁
            (HomologicalComplex₂.horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        (YE.cokernelSequenceE
          (HomologicalComplex₂.horizontalCanonicalAbutmentLowerMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentMiddleMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentUpperMap p q)
          (HomologicalComplex₂.horizontalCanonicalAbutmentLowerCompositeMap p)
          (HomologicalComplex₂.horizontalCanonicalAbutmentLower_comp_middle p)
          (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
          (-((p + q : ℕ) : ℤ) + 1)).g := by
  exact Hom.cokernelSequenceE_g_EMap φ
    (HomologicalComplex₂.horizontalCanonicalAbutmentLowerMap p)
    (HomologicalComplex₂.horizontalCanonicalAbutmentMiddleMap p)
    (HomologicalComplex₂.horizontalCanonicalAbutmentUpperMap p q)
    (HomologicalComplex₂.horizontalCanonicalAbutmentLowerCompositeMap p)
    (HomologicalComplex₂.horizontalCanonicalAbutmentLower_comp_middle p)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
    (-((p + q : ℕ) : ℤ) + 1)

end CanonicalShape

#print axioms Hom.cokernelSequenceE_toCycles_cyclesMap
#print axioms Hom.cokernelSequenceE_g_EMap

end MathlibExtTest.SpectralObjectCokernelENaturality

end
