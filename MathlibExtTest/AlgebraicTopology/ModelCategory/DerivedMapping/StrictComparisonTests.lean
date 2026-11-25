/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.StrictComparison

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.StrictComparisonTests

#check strictToDerivedMappingObject
#check strictToDerivedMappingObject_app
#check strictToDerivedMappingObject_app_mem_realizationWeakEquivalences

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [SimplicialCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

section SymbolicUniverses

variable {X X' Y Y' : C}

example :
    SimplicialCategory.sHomFunctor C ⟶ derivedMappingObject (C := C) :=
  strictToDerivedMappingObject (C := C)

example (X Y : C) :
    ((strictToDerivedMappingObject (C := C)).app (.op X)).app Y =
      eHomWhiskerLeft SSet X
          ((fibrantReplacementUnit (C := C)).app Y) ≫
        eHomWhiskerRight SSet
          ((cofibrantReplacementCounit (C := C)).app X)
          ((fibrantReplacement (C := C)).obj Y) :=
  strictToDerivedMappingObject_app X Y

/-- The outer variable is contravariant, including for an arbitrary source map. -/
example (f : X ⟶ X') :
    (SimplicialCategory.sHomFunctor C).map f.op ≫
        (strictToDerivedMappingObject (C := C)).app (.op X) =
      (strictToDerivedMappingObject (C := C)).app (.op X') ≫
        (derivedMappingObject (C := C)).map f.op :=
  (strictToDerivedMappingObject (C := C)).naturality f.op

/-- The inner variable is covariant, including for an arbitrary target map. -/
example (g : Y ⟶ Y') :
    ((SimplicialCategory.sHomFunctor C).obj (.op X)).map g ≫
        ((strictToDerivedMappingObject (C := C)).app (.op X)).app Y' =
      ((strictToDerivedMappingObject (C := C)).app (.op X)).app Y ≫
        ((derivedMappingObject (C := C)).obj (.op X)).map g :=
  ((strictToDerivedMappingObject (C := C)).app (.op X)).naturality g

/-- Target naturality also specializes coherently to the identity. -/
example :
    ((SimplicialCategory.sHomFunctor C).obj (.op X)).map (𝟙 Y) ≫
        ((strictToDerivedMappingObject (C := C)).app (.op X)).app Y =
      ((strictToDerivedMappingObject (C := C)).app (.op X)).app Y ≫
        ((derivedMappingObject (C := C)).obj (.op X)).map (𝟙 Y) :=
  ((strictToDerivedMappingObject (C := C)).app (.op X)).naturality (𝟙 Y)

example (data : HomotopyFunctionComplexInvarianceData (C := C))
    (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    SSet.realizationWeakEquivalences
      (((strictToDerivedMappingObject (C := C)).app (.op X)).app Y) :=
  strictToDerivedMappingObject_app_mem_realizationWeakEquivalences data X Y

/-- Cofibrancy of the source is an actual hypothesis of the weak-equivalence theorem. -/
example (_data : HomotopyFunctionComplexInvarianceData (C := C))
    (_X Y : C) [IsFibrant Y] : True := by
  fail_if_success
    have := strictToDerivedMappingObject_app_mem_realizationWeakEquivalences _data _X Y
  trivial

/-- Fibrancy of the target is an actual hypothesis of the weak-equivalence theorem. -/
example (_data : HomotopyFunctionComplexInvarianceData (C := C))
    (X _Y : C) [IsCofibrant X] : True := by
  fail_if_success
    have := strictToDerivedMappingObject_app_mem_realizationWeakEquivalences _data X _Y
  trivial

/-- The invariance packet is explicit and is not selected by typeclass inference. -/
example : True := by
  fail_if_success
    let _ : HomotopyFunctionComplexInvarianceData (C := C) := by
      infer_instance
  trivial

/-- Strict and replacement-derived mapping bifunctors are not definitionally equal. -/
example : True := by
  fail_if_success
    have : SimplicialCategory.sHomFunctor C = derivedMappingObject (C := C) := rfl
  trivial

end SymbolicUniverses

section UniverseOneZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
  [SimplicialCategory C₁]
  [HasFunctorialFactorization (cofibrations C₁) (trivialFibrations C₁)]
  [HasFunctorialFactorization (trivialCofibrations C₁) (fibrations C₁)]
variable (data : HomotopyFunctionComplexInvarianceData (C := C₁))
  (X Y : C₁) [IsCofibrant X] [IsFibrant Y]

example :
    SimplicialCategory.sHomFunctor C₁ ⟶ derivedMappingObject (C := C₁) :=
  strictToDerivedMappingObject (C := C₁)

example :
    SSet.realizationWeakEquivalences
      (((strictToDerivedMappingObject (C := C₁)).app (.op X)).app Y) :=
  strictToDerivedMappingObject_app_mem_realizationWeakEquivalences data X Y

end UniverseOneZero

section UniverseZero

variable {C₀ : Type} [Category C₀] [ModelCategory C₀]
  [SimplicialCategory C₀]
  [HasFunctorialFactorization (cofibrations C₀) (trivialFibrations C₀)]
  [HasFunctorialFactorization (trivialCofibrations C₀) (fibrations C₀)]

example :
    SimplicialCategory.sHomFunctor C₀ ⟶ derivedMappingObject (C := C₀) :=
  strictToDerivedMappingObject (C := C₀)

end UniverseZero

/- No isomorphism or unconditional component theorem is asserted. -/

/-- error: Unknown identifier `strictToDerivedMappingObjectIso` -/
#guard_msgs (error) in
#check strictToDerivedMappingObjectIso

/-- error: Unknown identifier `strictToDerivedMappingObject_isIso` -/
#guard_msgs (error) in
#check strictToDerivedMappingObject_isIso

#print axioms strictToDerivedMappingObject
#print axioms strictToDerivedMappingObject_app
#print axioms strictToDerivedMappingObject_app_mem_realizationWeakEquivalences

end HomotopicalAlgebra.StrictComparisonTests
