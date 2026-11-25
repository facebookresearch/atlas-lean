/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# Public clients for the simplicial model structure on simplicial sets

These tests pin the canonical global simplicial enrichment, the opt-in model
scope, all six pushout-product and pullback-hom theorems, and representative
identity, horn, boundary, initial, and universe boundary cases.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed
  HomotopicalAlgebra MorphismProperty
open scoped Simplicial MonoidalCategory

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplicialModelTests

section CanonicalEnrichmentBeforeModelScope

#synth CategoryTheory.SimplicialCategory SSet.{u}

example (X Y : SSet.{u}) :
    CategoryTheory.SimplicialCategory.sHom X Y = (ihom X).obj Y := rfl

example : SSet.{u}ᵒᵖ ⥤ SSet.{u} ⥤ SSet.{u} :=
  CategoryTheory.SimplicialCategory.sHomFunctor SSet.{u}

example (X Y : SSet.{u}) :
    (X ⟶ Y) ≃
      (CategoryTheory.SimplicialCategory.sHom X Y) _⦋0⦌ :=
  CategoryTheory.SimplicialCategory.homEquiv' X Y

example (K X Y : SSet.{u}) :
    (K ⊗ X ⟶ Y) ≃
      (X ⟶ CategoryTheory.SimplicialCategory.sHom K Y) :=
  (ihom.adjunction K).homEquiv X Y

/--
error: failed to synthesize
  CategoryWithWeakEquivalences SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithWeakEquivalences SSet.{u}

/--
error: failed to synthesize
  ModelCategory SSet
-/
#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

end CanonicalEnrichmentBeforeModelScope

section SelectedModelScope

open scoped SSet.modelCategoryQuillen

#synth CategoryWithWeakEquivalences SSet.{u}
#synth ModelCategory SSet.{u}
#synth CategoryTheory.SimplicialCategory SSet.{u}

example (X Y : SSet.{u}) :
    CategoryTheory.SimplicialCategory.sHom X Y = (ihom X).obj Y := rfl

example : SSet.{u}ᵒᵖ ⥤ SSet.{u} ⥤ SSet.{u} :=
  CategoryTheory.SimplicialCategory.sHomFunctor SSet.{u}

example (X Y : SSet.{u}) :
    (X ⟶ Y) ≃
      (CategoryTheory.SimplicialCategory.sHom X Y) _⦋0⦌ :=
  CategoryTheory.SimplicialCategory.homEquiv' X Y

example (K X Y : SSet.{u}) :
    (K ⊗ X ⟶ Y) ≃
      (X ⟶ CategoryTheory.SimplicialCategory.sHom K Y) :=
  (ihom.adjunction K).homEquiv X Y

end SelectedModelScope

section CanonicalEnrichmentAfterModelScope

#synth CategoryTheory.SimplicialCategory SSet.{u}

example (X Y : SSet.{u}) :
    CategoryTheory.SimplicialCategory.sHom X Y = (ihom X).obj Y := rfl

example : SSet.{u}ᵒᵖ ⥤ SSet.{u} ⥤ SSet.{u} :=
  CategoryTheory.SimplicialCategory.sHomFunctor SSet.{u}

example (X Y : SSet.{u}) :
    (X ⟶ Y) ≃
      (CategoryTheory.SimplicialCategory.sHom X Y) _⦋0⦌ :=
  CategoryTheory.SimplicialCategory.homEquiv' X Y

example (K X Y : SSet.{u}) :
    (K ⊗ X ⟶ Y) ≃
      (X ⟶ CategoryTheory.SimplicialCategory.sHom K Y) :=
  (ihom.adjunction K).homEquiv X Y

/--
error: failed to synthesize
  CategoryWithWeakEquivalences SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithWeakEquivalences SSet.{u}

/--
error: failed to synthesize
  ModelCategory SSet
-/
#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

end CanonicalEnrichmentAfterModelScope

section SymbolicSM7

open scoped SSet.modelCategoryQuillen

variable {A B K L X Y : SSet.{u}}
variable (i : A ⟶ B) (j : K ⟶ L) (p : X ⟶ Y)

example [Cofibration i] [Cofibration j] :
    Cofibration ((Arrow.mk i □ Arrow.mk j).hom) :=
  SSet.cofibration_pushoutProduct i j

example [Cofibration i] [WeakEquivalence i] [Cofibration j] :
    trivialCofibrations SSet.{u} ((Arrow.mk i □ Arrow.mk j).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_left i j

example [Cofibration i] [Cofibration j] [WeakEquivalence j] :
    trivialCofibrations SSet.{u} ((Arrow.mk i □ Arrow.mk j).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_right i j

example [Cofibration i] [Fibration p] :
    Fibration (SSet.ihomToPullback i p) :=
  SSet.fibration_ihomToPullback i p

example [Cofibration i] [WeakEquivalence i] [Fibration p] :
    trivialFibrations SSet.{u} (SSet.ihomToPullback i p) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_left i p

example [Cofibration i] [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{u} (SSet.ihomToPullback i p) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_right i p

section NontrivialWeaknessGuard

variable [Cofibration i] [Fibration p]

/--
error: failed to synthesize
  WeakEquivalence (SSet.ihomToPullback i p)
-/
#guard_msgs (error, substring := true) in
#synth WeakEquivalence (SSet.ihomToPullback i p)

end NontrivialWeaknessGuard

end SymbolicSM7

section IdentityClients

open scoped SSet.modelCategoryQuillen

variable (X Y : SSet.{u})

example : Cofibration ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.cofibration_pushoutProduct (𝟙 X) (𝟙 Y)

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_left (𝟙 X) (𝟙 Y)

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_right (𝟙 X) (𝟙 Y)

example : trivialFibrations SSet.{u}
    (SSet.ihomToPullback (𝟙 X) (𝟙 X)) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_left (𝟙 X) (𝟙 X)

example : trivialFibrations SSet.{u}
    (SSet.ihomToPullback (𝟙 X) (𝟙 X)) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_right (𝟙 X) (𝟙 X)

end IdentityClients

section HornBoundaryClients

open scoped SSet.modelCategoryQuillen

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (SSet.horn.{u} 1 (0 : Fin 2)).ι □
      Arrow.mk (SSet.boundary.{u} 1).ι).hom) := by
  let h := (SSet.horn.{u} 1 (0 : Fin 2)).ι
  let b := (SSet.boundary.{u} 1).ι
  let _ : Cofibration h := SSet.modelCategoryQuillen.cofibration_of_mono _
  let _ : Cofibration b := SSet.modelCategoryQuillen.cofibration_of_mono _
  have hh : SSet.anodyneExtensions.{u} h :=
    SSet.anodyneExtensions.horn_ι (0 : Fin 2)
  have ht : trivialCofibrations SSet.{u} h := by
    rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
    exact hh
  let _ : WeakEquivalence h :=
    ((mem_trivialCofibrations_iff h).1 ht).2
  exact SSet.pushoutProduct_mem_trivialCofibrations_of_left h b

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (SSet.boundary.{u} 1).ι □
      Arrow.mk (SSet.horn.{u} 1 (0 : Fin 2)).ι).hom) := by
  let b := (SSet.boundary.{u} 1).ι
  let h := (SSet.horn.{u} 1 (0 : Fin 2)).ι
  let _ : Cofibration b := SSet.modelCategoryQuillen.cofibration_of_mono _
  let _ : Cofibration h := SSet.modelCategoryQuillen.cofibration_of_mono _
  have hh : SSet.anodyneExtensions.{u} h :=
    SSet.anodyneExtensions.horn_ι (0 : Fin 2)
  have ht : trivialCofibrations SSet.{u} h := by
    rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
    exact hh
  let _ : WeakEquivalence h :=
    ((mem_trivialCofibrations_iff h).1 ht).2
  exact SSet.pushoutProduct_mem_trivialCofibrations_of_right b h

example : trivialFibrations SSet.{u}
    (SSet.ihomToPullback (SSet.horn.{u} 1 (0 : Fin 2)).ι
      (𝟙 (Δ[0] : SSet.{u}))) := by
  let h := (SSet.horn.{u} 1 (0 : Fin 2)).ι
  let _ : Cofibration h := SSet.modelCategoryQuillen.cofibration_of_mono _
  have hh : SSet.anodyneExtensions.{u} h :=
    SSet.anodyneExtensions.horn_ι (0 : Fin 2)
  have ht : trivialCofibrations SSet.{u} h := by
    rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
    exact hh
  let _ : WeakEquivalence h :=
    ((mem_trivialCofibrations_iff h).1 ht).2
  exact SSet.ihomToPullback_mem_trivialFibrations_of_left h (𝟙 _)

example : trivialFibrations SSet.{u}
    (SSet.ihomToPullback (SSet.horn.{u} 1 (0 : Fin 2)).ι
      (𝟙 (Δ[0] : SSet.{u}))) := by
  let h := (SSet.horn.{u} 1 (0 : Fin 2)).ι
  let _ : Cofibration h := SSet.modelCategoryQuillen.cofibration_of_mono _
  exact SSet.ihomToPullback_mem_trivialFibrations_of_right h (𝟙 _)

end HornBoundaryClients

section EmptyAndZeroDimensionalClients

open scoped SSet.modelCategoryQuillen

variable (X : SSet.{u})

example : Cofibration
    ((Arrow.mk (initial.to X) □ Arrow.mk (𝟙 (Δ[0] : SSet.{u}))).hom) :=
  let _ : Cofibration (initial.to X) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  SSet.cofibration_pushoutProduct (initial.to X) (𝟙 _)

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (initial.to X) □ Arrow.mk (𝟙 (Δ[0] : SSet.{u}))).hom) :=
  let _ : Cofibration (initial.to X) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  SSet.pushoutProduct_mem_trivialCofibrations_of_right
    (initial.to X) (𝟙 _)

end EmptyAndZeroDimensionalClients

section UniverseSpecializations

open scoped SSet.modelCategoryQuillen

example : SSet.anodyneExtensions.{1} =
    trivialCofibrations SSet.{1} :=
  SSet.anodyneExtensions_eq_trivialCofibrations

example (X Y : SSet.{1}) :
    Cofibration ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.cofibration_pushoutProduct (𝟙 X) (𝟙 Y)

example (X Y : SSet.{1}) : trivialCofibrations SSet.{1}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_left (𝟙 X) (𝟙 Y)

example (X Y : SSet.{1}) : trivialCofibrations SSet.{1}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_right (𝟙 X) (𝟙 Y)

example (X : SSet.{1}) : trivialFibrations SSet.{1}
    (SSet.ihomToPullback (𝟙 X) (𝟙 X)) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_left (𝟙 X) (𝟙 X)

example (X : SSet.{1}) : trivialFibrations SSet.{1}
    (SSet.ihomToPullback (𝟙 X) (𝟙 X)) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_right (𝟙 X) (𝟙 X)

example : SSet.anodyneExtensions.{0} =
    trivialCofibrations SSet.{0} :=
  SSet.anodyneExtensions_eq_trivialCofibrations

example (X Y : SSet.{0}) :
    Cofibration ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.cofibration_pushoutProduct (𝟙 X) (𝟙 Y)

example (X Y : SSet.{0}) : trivialCofibrations SSet.{0}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_left (𝟙 X) (𝟙 Y)

example (X Y : SSet.{0}) : trivialCofibrations SSet.{0}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  SSet.pushoutProduct_mem_trivialCofibrations_of_right (𝟙 X) (𝟙 Y)

example (X : SSet.{0}) : trivialFibrations SSet.{0}
    (SSet.ihomToPullback (𝟙 X) (𝟙 X)) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_left (𝟙 X) (𝟙 X)

example (X : SSet.{0}) : trivialFibrations SSet.{0}
    (SSet.ihomToPullback (𝟙 X) (𝟙 X)) :=
  SSet.ihomToPullback_mem_trivialFibrations_of_right (𝟙 X) (𝟙 X)

end UniverseSpecializations

section APIBoundary

#check CategoryTheory.SimplicialCategory.sHom
#check CategoryTheory.SimplicialCategory.sHomFunctor
#check CategoryTheory.SimplicialCategory.homEquiv'

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialTensor

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialCotensor

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.sHom

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialMappingObject

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.SimplicialModelCategory

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.instSimplicialModelCategory

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.ihomToPullback_mem_cofibrations_rlp

end APIBoundary

#check SSet.anodyneExtensions_eq_trivialCofibrations
#check SSet.cofibration_pushoutProduct
#check SSet.pushoutProduct_mem_trivialCofibrations_of_left
#check SSet.pushoutProduct_mem_trivialCofibrations_of_right
#check SSet.ihomToPullback_mem_trivialFibrations_of_left
#check SSet.ihomToPullback_mem_trivialFibrations_of_right

#print axioms SSet.anodyneExtensions_eq_trivialCofibrations
#print axioms SSet.cofibration_pushoutProduct
#print axioms SSet.pushoutProduct_mem_trivialCofibrations_of_left
#print axioms SSet.pushoutProduct_mem_trivialCofibrations_of_right
#print axioms SSet.ihomToPullback_mem_trivialFibrations_of_left
#print axioms SSet.ihomToPullback_mem_trivialFibrations_of_right

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplicialModelTests
