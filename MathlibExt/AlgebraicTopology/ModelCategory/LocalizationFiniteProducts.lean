/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationFibrantProducts
import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationTerminal
import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Genuine finite products in the original model localization

Fibrant derivability covers every localized object. The proved full
original product cones and their actual representative isomorphisms
therefore give binary products. The actual projected terminal cone and
the ordinary finite-product construction give all finite products.
This is a property of the homotopy category; a raw Cartesian model
axiom or raw higher internal-power fibrancy is not asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v uH vH
open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.ModelLocalization
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]

/-- Genuine original fibrant derivability supplies a fibrant representative of every localized
object. -/
def fibrantRepresentative (K : H) : FibrantObject C :=
  let Φ := FibrantObject.localizerMorphism C
  let _ : (Φ.functor ⋙ Q).EssSurj := Φ.essSurj_of_hasRightResolutions Q
  (Φ.functor ⋙ Q).objPreimage K

/-- The actual complete localization isomorphism from the SAME original fibrant representative. -/
def fibrantRepresentativeIso (K : H) : Q.obj (fibrantRepresentative Q K).obj ≅ K :=
  let Φ := FibrantObject.localizerMorphism C
  let _ : (Φ.functor ⋙ Q).EssSurj := Φ.essSurj_of_hasRightResolutions Q
  (Φ.functor ⋙ Q).objObjPreimageIso K

include Q in
/-- Both genuine fibrant representatives and the SAME original product cone supply every localized
binary product. -/
theorem hasBinaryProduct (A B : H) : HasBinaryProduct A B := by
  let a := fibrantRepresentative Q A
  let b := fibrantRepresentative Q B
  let _ : HasLimit (pair (Q.obj a.obj) (Q.obj b.obj)) :=
    ⟨⟨{ cone := productCone Q a.obj b.obj, isLimit := productIsLimit Q a.obj b.obj }⟩⟩
  exact hasLimit_of_iso (mapPairIso (F := pair (Q.obj a.obj) (Q.obj b.obj)) (G := pair A B)
    (fibrantRepresentativeIso Q A) (fibrantRepresentativeIso Q B))

include Q in
/-- The actual native product producers give binary-product limits on the entire original
localization. -/
theorem hasBinaryProducts : HasBinaryProducts H := by
  let _ : ∀ {A B : H}, HasLimit (pair A B) := fun {A B} => hasBinaryProduct Q A B
  exact hasBinaryProducts_of_hasLimit_pair H

include Q in
/-- The original terminal and binary product cones construct all finite products in the actual model
localization. -/
theorem hasFiniteProducts : HasFiniteProducts H := by
  let _ : HasTerminal H := hasTerminal Q
  let _ : HasBinaryProducts H := hasBinaryProducts Q
  exact hasFiniteProducts_of_has_binary_and_terminal

end HomotopicalAlgebra.ModelLocalization

namespace HomotopicalAlgebra
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The SAME original model homotopy category has finite products by its actual native cone
producers. -/
instance homotopyCategoryHasFiniteProducts :
    HasFiniteProducts ((weakEquivalences C).Localization) :=
  ModelLocalization.hasFiniteProducts ((weakEquivalences C).Q)

end HomotopicalAlgebra
