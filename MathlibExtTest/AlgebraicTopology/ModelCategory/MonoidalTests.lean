/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
public import Mathlib.Algebra.Homology.ModelCategory.Injective

/-!
# Tests for closed symmetric monoidal model categories

These clients pin the three-name interface, both pushout-product orientations,
the closed pullback-Hom consequences, the noncofibrant-unit contract, selected
simplicial sets, universe polymorphism, and parent-instance isolation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.MonoidalTests

#check MonoidalUnitAxiomWitness
#check IsClosedSymmetricMonoidalModelCategory
#check isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
#check IsClosedSymmetricMonoidalModelCategory.cartesianPushoutProductAxiom
#check IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom

section GenericInterface

variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

section NoncofibrantUnitContract

variable
  (hcof : PushoutProductLe (cofibrations C) (cofibrations C)
    (cofibrations C))
  (hleft : PushoutProductLe (trivialCofibrations C) (cofibrations C)
    (trivialCofibrations C))
  (hright : PushoutProductLe (cofibrations C) (trivialCofibrations C)
    (trivialCofibrations C))

example (w : MonoidalUnitAxiomWitness C) :
    IsClosedSymmetricMonoidalModelCategory C where
  cofibration_pushoutProduct := hcof
  trivial_pushoutProduct_left := hleft
  trivial_pushoutProduct_right := hright
  unit_axiom := ⟨w⟩

example (w : MonoidalUnitAxiomWitness C) : True := by
  let _ : IsClosedSymmetricMonoidalModelCategory C := {
    cofibration_pushoutProduct := hcof
    trivial_pushoutProduct_left := hleft
    trivial_pushoutProduct_right := hright
    unit_axiom := ⟨w⟩ }
  fail_if_success
    let _ : IsCofibrant (𝟙_ C) := inferInstance
  trivial

end NoncofibrantUnitContract

section Projections

variable [IsClosedSymmetricMonoidalModelCategory C]
  {A B K L : C} (i : A ⟶ B) (j : K ⟶ L)

example (hi : cofibrations C i) (hj : cofibrations C j) :
    cofibrations C ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    i j hi hj

example (hi : trivialCofibrations C i) (hj : cofibrations C j) :
    trivialCofibrations C ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    i j hi hj

example (hi : cofibrations C i) (hj : trivialCofibrations C j) :
    trivialCofibrations C ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
    i j hi hj

example : Nonempty (MonoidalUnitAxiomWitness C) :=
  IsClosedSymmetricMonoidalModelCategory.unit_axiom (C := C)

end Projections

section PullbackHom

variable {D : Type u} [Category.{v} D] [ModelCategory D]
  [CartesianMonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  [IsClosedSymmetricMonoidalModelCategory D]
  {A B X Y : D} (i : A ⟶ B) (p : X ⟶ Y)

example : CartesianPushoutProductAxiom (C := D) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPushoutProductAxiom

example : CartesianPullbackHomAxiom (C := D) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom

example (hi : cofibrations D i) (hp : fibrations D p) :
    fibrations D ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.2.2
    i p hi hp

example (hi : trivialCofibrations D i) (hp : fibrations D p) :
    trivialFibrations D ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.2.1
    i p hi hp

example (hi : cofibrations D i) (hp : trivialFibrations D p) :
    trivialFibrations D ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.1
    i p hi hp

example {K L : D} (j : K ⟶ L) :
    HasLiftingProperty ((Arrow.mk i □ Arrow.mk j).hom) p ↔
      HasLiftingProperty i
        ((Opposite.op (Arrow.mk j) ⋔ Arrow.mk p).hom) :=
  Arrow.PushoutProduct.hasLiftingProperty_mk_iff'

end PullbackHom

end GenericInterface

section ParentIsolation

variable (D : Type u) [Category.{v} D]
  [model : ModelCategory D] [monoidal : MonoidalCategory D]
  [symmetric : SymmetricCategory D] [closed : MonoidalClosed D]
  [IsClosedSymmetricMonoidalModelCategory D]

example : True := by
  have hModel : (inferInstance : ModelCategory D) = model := rfl
  have hMonoidal : (inferInstance : MonoidalCategory D) = monoidal := rfl
  have hSymmetric : (inferInstance : SymmetricCategory D) = symmetric := rfl
  have hClosed : (inferInstance : MonoidalClosed D) = closed := rfl
  clear hModel hMonoidal hSymmetric hClosed
  trivial

end ParentIsolation

section SelectedSSet

open scoped SSet.modelCategoryQuillen

local instance : IsClosedSymmetricMonoidalModelCategory SSet.{u} :=
  isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    SSet.{u}
    (by
      intro A B K L i j hi hj
      let _ : Cofibration i := (cofibration_iff i).2 hi
      let _ : Cofibration j := (cofibration_iff j).2 hj
      exact (cofibration_iff _).1
        (SSet.cofibration_pushoutProduct i j))
    (by
      intro A B K L i j hi hj
      have hi' := (mem_trivialCofibrations_iff i).1 hi
      let _ : Cofibration i := hi'.1
      let _ : WeakEquivalence i := hi'.2
      let _ : Cofibration j := (cofibration_iff j).2 hj
      exact SSet.pushoutProduct_mem_trivialCofibrations_of_left i j)
    (by
      intro A B K L i j hi hj
      let _ : Cofibration i := (cofibration_iff i).2 hi
      have hj' := (mem_trivialCofibrations_iff j).1 hj
      let _ : Cofibration j := hj'.1
      let _ : WeakEquivalence j := hj'.2
      exact SSet.pushoutProduct_mem_trivialCofibrations_of_right i j)

#synth ModelCategory SSet.{u}
#synth MonoidalCategory SSet.{u}
#synth SymmetricCategory SSet.{u}
#synth MonoidalClosed SSet.{u}
#synth IsClosedSymmetricMonoidalModelCategory SSet.{u}
#synth IsClosedSymmetricMonoidalModelCategory SSet.{1}
#synth IsClosedSymmetricMonoidalModelCategory SSet.{0}

example : Nonempty (MonoidalUnitAxiomWitness SSet.{u}) :=
  IsClosedSymmetricMonoidalModelCategory.unit_axiom (C := SSet.{u})

example (X : SSet.{u}) : IsCofibrant X := inferInstance

section IdentityAndSymmetry

variable (X Y : SSet.{u})

example : cofibrations SSet.{u}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    (𝟙 X) (𝟙 Y) (mem_cofibrations (𝟙 X))
      (mem_cofibrations (𝟙 Y))

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    (𝟙 X) (𝟙 Y) (mem_trivialCofibrations (𝟙 X))
      (mem_cofibrations (𝟙 Y))

example : trivialCofibrations SSet.{u}
    ((Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
    (𝟙 X) (𝟙 Y) (mem_cofibrations (𝟙 X))
      (mem_trivialCofibrations (𝟙 Y))

example : (Arrow.mk (𝟙 X) □ Arrow.mk (𝟙 Y)) ≅
    (Arrow.mk (𝟙 Y) □ Arrow.mk (𝟙 X)) :=
  Arrow.PushoutProduct.braiding _ _

end IdentityAndSymmetry

section HornBoundary

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
  exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    h b ht (mem_cofibrations b)

end HornBoundary

end SelectedSSet

section InjectiveChainNegative

open scoped CochainComplex.Plus.modelCategoryQuillen

variable (A : Type u) [Category.{v} A] [Abelian A] [EnoughInjectives A]

example : ModelCategory (CochainComplex.Plus A) := inferInstance

example : True := by
  fail_if_success
    let _ : IsClosedSymmetricMonoidalModelCategory
      (CochainComplex.Plus A) := inferInstance
  trivial

end InjectiveChainNegative

#print axioms MonoidalUnitAxiomWitness
#print axioms IsClosedSymmetricMonoidalModelCategory
#print axioms isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
#print axioms
  IsClosedSymmetricMonoidalModelCategory.cartesianPushoutProductAxiom
#print axioms
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom

end MathlibExtTest.AlgebraicTopology.ModelCategory.MonoidalTests
