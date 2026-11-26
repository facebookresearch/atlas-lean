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

import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeZeroSource

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {F G F' G' : CochainComplex C ℤ}
variable (f : F ⟶ G) (f' : F' ⟶ G')
variable (hF : IsZero F) (hF' : IsZero F')

example : mappingCone f ≅ G :=
  mappingConeZeroSourceIso f hF

example : mappingCone f ⟶ G :=
  mappingConeZeroSourceDesc f hF

example : QuasiIso (mappingConeZeroSourceDesc f hF) :=
  mappingConeZeroSourceDesc_quasiIso f hF

example :
    mappingCone.inr f ≫ mappingConeZeroSourceDesc f hF = 𝟙 G :=
  mappingCone_inr_comp_zeroSourceDesc f hF

example :
    mappingConeZeroSourceDesc f hF ≫ mappingCone.inr f =
      𝟙 (mappingCone f) :=
  mappingConeZeroSourceDesc_comp_inr f hF

example (k : ℤ) : (mappingCone f).homology k ≅ G.homology k :=
  mappingConeZeroSourceHomologyIso f hF k

example (k : ℤ) :
    HomologicalComplex.homologyMap (mappingCone.inr f) k ≫
        (mappingConeZeroSourceHomologyIso f hF k).hom = 𝟙 _ :=
  homologyMap_inr_comp_mappingConeZeroSourceHomologyIso_hom f hF k

example (a : F ⟶ F') (b : G ⟶ G')
    (comm : f ≫ b = a ≫ f') (k : ℤ) :
    HomologicalComplex.homologyMap
        (mappingCone.map f f' a b comm) k ≫
        (mappingConeZeroSourceHomologyIso f' hF' k).hom =
      (mappingConeZeroSourceHomologyIso f hF k).hom ≫
        HomologicalComplex.homologyMap b k :=
  mappingConeZeroSourceHomologyIso_hom_naturality
    f f' hF hF' a b comm k

example (a : F ⟶ F') (b : G ⟶ G')
    (comm : f ≫ b = a ≫ f') :
    mappingCone.map f f' a b comm ≫
        mappingConeZeroSourceDesc f' hF' =
      mappingConeZeroSourceDesc f hF ≫ b :=
  mappingConeZeroSourceDesc_naturality f f' hF hF' a b comm

end CochainComplex

#print axioms CochainComplex.mappingConeZeroSourceIso
#print axioms CochainComplex.mappingConeZeroSourceDesc_naturality

end
