/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectMap

/-!
# Naturality of the fixed-E cokernel sequence

For a morphism of abelian spectral objects, the canonical epimorphism into a
fixed `E` object commutes with the induced `EMap`.  The proof first compares
the public cycles presentations by cancelling the target `iCycles`, then uses
naturality of the homology projection of the defining short complex.

This file uses no successor-page selected homology data.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ComposableArrows

universe v u vι uι

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y : SpectralObject C ι}

namespace Hom

/-- The cycles presentation used by `cokernelSequenceE.g` commutes with a
morphism of spectral objects. -/
theorem cokernelSequenceE_toCycles_cyclesMap
    (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫
          (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
          ShortComplex.cyclesMap
            (shortComplexMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
      (φ.hom n₁).app (mk₁ f₁₂) ≫
        Y.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫
        (Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
  rw [← cancel_mono
    (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles]
  simpa only [Category.assoc, ShortComplex.cyclesMap_i,
    shortComplexMap_τ₂,
    SpectralObject.cyclesIso_inv_i,
    SpectralObject.cyclesIso_inv_i_assoc,
    SpectralObject.toCycles_i,
    SpectralObject.toCycles_i_assoc] using
    (φ.hom n₁).naturality (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂)

/-- The canonical epimorphism in the fixed-`E` cokernel sequence is natural
under a morphism of spectral objects. -/
@[reassoc]
theorem cokernelSequenceE_g_EMap
    (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceE
          f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g ≫
        EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      (φ.hom n₁).app (mk₁ f₁₂) ≫
        (Y.cokernelSequenceE
          f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  have hCycles := cokernelSequenceE_toCycles_cyclesMap
    φ f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂
  dsimp only [SpectralObject.cokernelSequenceE, SpectralObject.πE, EMap]
  simp only [Category.assoc, ShortComplex.homologyπ_naturality]
  simpa only [Category.assoc] using
    congrArg
      (fun z => z ≫
        (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyπ)
      hCycles

end Hom

end CategoryTheory.Abelian.SpectralObject

end
