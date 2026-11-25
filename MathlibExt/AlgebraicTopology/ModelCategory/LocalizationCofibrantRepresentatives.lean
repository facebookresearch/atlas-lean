/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant

/-!
# Genuine cofibrant representatives of every model-localized object

The original cofibrant derivability structure supplies a representative
and its actual localization isomorphism. The fundamental lemma supplies
an original arrow into any fibrant target and retains its full projected
map. Independent carrier and Hom universes are preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v uH vH
open CategoryTheory

namespace HomotopicalAlgebra.ModelLocalization
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H]
  (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]

/-- The genuine original cofibrant derivability structure covers every object of the given
localization. -/
def cofibrantRepresentative (K : H) : CofibrantObject C :=
  let Φ := CofibrantObject.localizerMorphism C
  let _ : (Φ.functor ⋙ Q).EssSurj := Φ.essSurj_of_hasLeftResolutions Q
  (Φ.functor ⋙ Q).objPreimage K

/-- The actual complete localization isomorphism from the SAME original cofibrant representative. -/
def cofibrantRepresentativeIso (K : H) : Q.obj (cofibrantRepresentative Q K).obj ≅ K :=
  let Φ := CofibrantObject.localizerMorphism C
  let _ : (Φ.functor ⋙ Q).EssSurj := Φ.essSurj_of_hasLeftResolutions Q
  (Φ.functor ⋙ Q).objObjPreimageIso K

/-- The fundamental lemma supplies an actual original arrow for each localized map into a genuine
fibrant target. -/
def liftToFibrant {K : H} {Y : C} [IsFibrant Y] (f : K ⟶ Q.obj Y) :
    (cofibrantRepresentative Q K).obj ⟶ Y :=
  Classical.choose ((map_surjective_of_isLocalization Q (cofibrantRepresentative Q K).obj Y)
    ((cofibrantRepresentativeIso Q K).hom ≫ f))

/-- The full original representing arrow reads exactly the SAME localized map after the actual
representative
isomorphism. -/
theorem liftToFibrant_fac {K : H} {Y : C} [IsFibrant Y] (f : K ⟶ Q.obj Y) :
    Q.map (liftToFibrant Q f) = (cofibrantRepresentativeIso Q K).hom ≫ f :=
  Classical.choose_spec ((map_surjective_of_isLocalization Q (cofibrantRepresentative Q K).obj Y)
    ((cofibrantRepresentativeIso Q K).hom ≫ f))

end HomotopicalAlgebra.ModelLocalization
