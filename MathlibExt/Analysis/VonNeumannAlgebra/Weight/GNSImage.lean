/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSNormalHom
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSInjective
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.ImageEquiv

/-!
# The original NSF weight's actual normal GNS image and equivalence

The original normal GNS map has the same computed coefficient operators.
Source semifiniteness and faithfulness prove its injectivity. The generic
proved image construction and bilateral normal equivalence then give its
literal von Neumann operator range and actual normal equivalence. Every
operator value is the original weight GNS value; no alternate Hilbert
model, range, inverse or source existence output is selected.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Original semifiniteness and faithfulness give injectivity of the same computed normal GNS map. -/
theorem normalSemifiniteFaithfulWeightGNSStarAlgHom_injective
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) :
    Function.Injective (normalWeightGNSStarAlgHom M φ.val φ.property.1) := by
  intro a b h
  apply φ.val.gnsLeftStarAlgHom_injective M φ.property.2.1 φ.property.2.2
  have hvalue := congrArg
    (fun T : (⊤ : VonNeumannAlgebra φ.val.GNS) => (T : φ.val.GNS →L[ℂ] φ.val.GNS)) h
  rw [normalWeightGNSStarAlgHom_apply, normalWeightGNSStarAlgHom_apply] at hvalue
  exact hvalue

/-- The original NSF weight's computed GNS representation has its literal VN operator image. -/
def normalSemifiniteFaithfulWeightGNSImage
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) : VonNeumannAlgebra φ.val.GNS :=
  (normalWeightGNSStarAlgHom M φ.val φ.property.1).imageVonNeumannAlgebra
    (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ)

/-- The actual normal equivalence identifies the original algebra with its literal computed GNS image. -/
def normalSemifiniteFaithfulWeightGNSImageEquiv
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) :
    NormalStarAlgEquiv M (normalSemifiniteFaithfulWeightGNSImage M φ) :=
  (normalWeightGNSStarAlgHom M φ.val φ.property.1).imageEquiv
    (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ)

/-- The actual NSF GNS image carrier consists exactly of the original computed GNS operators. -/
theorem coe_normalSemifiniteFaithfulWeightGNSImage
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) :
    (normalSemifiniteFaithfulWeightGNSImage M φ : Set (φ.val.GNS →L[ℂ] φ.val.GNS)) =
      Set.range φ.val.gnsLeftStarAlgHom := by
  let f := normalWeightGNSStarAlgHom M φ.val φ.property.1
  change (f.imageVonNeumannAlgebra (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ) :
    Set (φ.val.GNS →L[ℂ] φ.val.GNS)) = Set.range φ.val.gnsLeftStarAlgHom
  rw [f.coe_imageVonNeumannAlgebra]
  simp only [f, normalWeightGNSStarAlgHom_apply]

/-- The actual normal NSF GNS equivalence keeps every original computed coefficient operator. -/
theorem normalSemifiniteFaithfulWeightGNSImageEquiv_apply
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) (a : M) :
    (normalSemifiniteFaithfulWeightGNSImageEquiv M φ a : φ.val.GNS →L[ℂ] φ.val.GNS) =
      φ.val.gnsLeftStarAlgHom a := by
  let f := normalWeightGNSStarAlgHom M φ.val φ.property.1
  have h := f.imageEquiv_apply (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ) a
  exact h.trans (normalWeightGNSStarAlgHom_apply M φ.val φ.property.1 a)

end

end VonNeumannAlgebra
