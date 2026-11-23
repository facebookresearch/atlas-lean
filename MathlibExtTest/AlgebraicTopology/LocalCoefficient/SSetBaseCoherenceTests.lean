/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.SSetBaseCoherence
public import Mathlib.Data.ZMod.Basic

/-! # Tests for SSet local-coefficient pullback coherence -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetBaseCoherenceTests

universe uR uX

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y Z : SSet.{uX}}
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable {L K : SSet.LocalSystem R Z}
variable (α : L ⟶ K)

example : L.pullback (𝟙 Z) ≅ L :=
  SSet.LocalSystem.pullbackIdIso L

example : L.pullback (f ≫ g) ≅ (L.pullback g).pullback f :=
  SSet.LocalSystem.pullbackCompIso f g L

example {f g : X ⟶ Y} (h : f = g)
    (M : SSet.LocalSystem R Y) :
    M.pullback f ≅ M.pullback g :=
  SSet.LocalSystem.pullbackCongrIso h M

example : L.pullback g ⟶ K.pullback g :=
  SSet.LocalSystem.pullbackMap g α

example (x : SSet.FundamentalGroupoid Z) :
    (SSet.LocalSystem.pullbackIdIso L).hom.app x = 𝟙 _ :=
  SSet.LocalSystem.pullbackIdIso_hom_app L x

example (x : SSet.FundamentalGroupoid X) :
    (SSet.LocalSystem.pullbackCompIso f g L).hom.app x = 𝟙 _ :=
  SSet.LocalSystem.pullbackCompIso_hom_app f g L x

example :
    SSet.localCoefficientPullbackChainMap (𝟙 Z) L =
      SSet.localCoefficientChainMap
        (SSet.LocalSystem.pullbackIdIso L).hom :=
  SSet.localCoefficientPullbackChainMap_id L

example :
    SSet.localCoefficientPullbackChainMap (f ≫ g) L =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCompIso f g L).hom ≫
        SSet.localCoefficientPullbackChainMap f (L.pullback g) ≫
        SSet.localCoefficientPullbackChainMap g L :=
  SSet.localCoefficientPullbackChainMap_comp f g L

example {f g : X ⟶ Y} (h : f = g)
    (M : SSet.LocalSystem R Y) :
    SSet.localCoefficientPullbackChainMap f M =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCongrIso h M).hom ≫
        SSet.localCoefficientPullbackChainMap g M :=
  SSet.localCoefficientPullbackChainMap_congr h M

example :
    SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackMap g α) ≫
        SSet.localCoefficientPullbackChainMap g K =
      SSet.localCoefficientPullbackChainMap g L ≫
        SSet.localCoefficientChainMap α :=
  SSet.localCoefficientPullbackChainMap_naturality g α

end Generic

section NonidentityComposite

private abbrev firstFace : (Δ[0] : SSet) ⟶ Δ[1] :=
  SSet.stdSimplex.δ (0 : Fin 2)

private abbrev secondFace : (Δ[1] : SSet) ⟶ Δ[2] :=
  SSet.stdSimplex.δ (0 : Fin 3)

variable (L : SSet.LocalSystem (ZMod 1) Δ[2])

example :
    SSet.localCoefficientPullbackChainMap (firstFace ≫ secondFace) L =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCompIso firstFace secondFace L).hom ≫
        SSet.localCoefficientPullbackChainMap firstFace
          (L.pullback secondFace) ≫
        SSet.localCoefficientPullbackChainMap secondFace L :=
  SSet.localCoefficientPullbackChainMap_comp firstFace secondFace L

end NonidentityComposite

section IndependentUniverses

variable (R₁ : Type 1) [CommRing R₁]
variable {X₂ Y₂ Z₂ : SSet.{2}}
variable (f₂ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂)
variable (L₁ : SSet.LocalSystem R₁ Z₂)

example :
    SSet.localCoefficientPullbackChainMap (f₂ ≫ g₂) L₁ =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCompIso f₂ g₂ L₁).hom ≫
        SSet.localCoefficientPullbackChainMap f₂ (L₁.pullback g₂) ≫
        SSet.localCoefficientPullbackChainMap g₂ L₁ :=
  SSet.localCoefficientPullbackChainMap_comp f₂ g₂ L₁

variable (R₂ : Type 2) [CommRing R₂]
variable {X₁ Y₁ Z₁ : SSet.{1}}
variable (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁)
variable (L₂ : SSet.LocalSystem R₂ Z₁)

example :
    SSet.localCoefficientPullbackChainMap (f₁ ≫ g₁) L₂ =
      SSet.localCoefficientChainMap
          (SSet.LocalSystem.pullbackCompIso f₁ g₁ L₂).hom ≫
        SSet.localCoefficientPullbackChainMap f₁ (L₂.pullback g₁) ≫
        SSet.localCoefficientPullbackChainMap g₁ L₂ :=
  SSet.localCoefficientPullbackChainMap_comp f₁ g₁ L₂

end IndependentUniverses

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.localCoefficientPullbackChainMap_id

#guard_msgs (error, substring := true) in
#check SSet.localCoefficientPullbackHomologyMap_comp

end StoppingBoundary

#print axioms SSet.LocalSystem.pullbackIdIso
#print axioms SSet.LocalSystem.pullbackCompIso
#print axioms SSet.LocalSystem.pullbackIdIso_hom_app
#print axioms SSet.LocalSystem.pullbackCompIso_hom_app
#print axioms SSet.LocalSystem.pullbackCongrIso
#print axioms SSet.LocalSystem.pullbackCongrIso_hom_app
#print axioms SSet.LocalSystem.pullbackMap
#print axioms SSet.LocalSystem.pullbackMap_app
#print axioms SSet.localCoefficientPullbackFamilyEq_id_eq_refl
#print axioms SSet.localCoefficientCompIndexEq
#print axioms SSet.localCoefficientι_eqToHom_index
#print axioms SSet.localCoefficientPullbackFamilyEq_comp
#print axioms SSet.localCoefficientPullbackChainMap_id
#print axioms SSet.localCoefficientPullbackChainMap_comp
#print axioms SSet.localCoefficientPullbackChainMap_congr
#print axioms SSet.localCoefficientPullbackChainMap_naturality

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetBaseCoherenceTests
