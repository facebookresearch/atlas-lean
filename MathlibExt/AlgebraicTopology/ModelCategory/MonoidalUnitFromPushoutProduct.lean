/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductBrown

/-!
# Unit axioms for the original chosen replacement

True cofibrancy of the tensor unit and the pushout-product laws verify the
unit axiom for any supplied cofibrant unit replacement. The same argument
applies to the original factorization of the initial unit map. All objects,
factor maps and unitors below are those supplied by the caller; no default
replacement is selected from an existential monoidal-model witness.

When the unit is not known to be cofibrant, a final comparison uses an
explicit, already established unit witness. That comparison is separate
from the cofibrant-unit construction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

section UnitMaps

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The entire left unit comparison for the specified original map to the
unit, with the actual left unitor. -/
noncomputable def leftUnitReplacementMap {Q : C} (q : Q ⟶ 𝟙_ C) :
    tensorLeft Q ⟶ 𝟭 C :=
  (tensoringLeft C).map q ≫ (leftUnitorNatIso C).hom

/-- The entire right unit comparison uses the same original map to the
unit and the actual right unitor. -/
noncomputable def rightUnitReplacementMap {Q : C} (q : Q ⟶ 𝟙_ C) :
    tensorRight Q ⟶ 𝟭 C :=
  (tensoringRight C).map q ≫ (rightUnitorNatIso C).hom

@[simp]
theorem leftUnitReplacementMap_app {Q : C} (q : Q ⟶ 𝟙_ C) (X : C) :
    (leftUnitReplacementMap q).app X = (q ▷ X) ≫ (λ_ X).hom :=
  rfl

@[simp]
theorem rightUnitReplacementMap_app {Q : C} (q : Q ⟶ 𝟙_ C) (X : C) :
    (rightUnitReplacementMap q).app X = (X ◁ q) ≫ (ρ_ X).hom :=
  rfl

/-- Left unit comparison is natural in every original input morphism. -/
theorem leftUnitReplacementMap_naturality
    {Q X Y : C} (q : Q ⟶ 𝟙_ C) (f : X ⟶ Y) :
    (Q ◁ f) ≫ (q ▷ Y) ≫ (λ_ Y).hom =
      ((q ▷ X) ≫ (λ_ X).hom) ≫ f :=
  (leftUnitReplacementMap q).naturality f

/-- Right unit comparison is natural in every original input morphism. -/
theorem rightUnitReplacementMap_naturality
    {Q X Y : C} (q : Q ⟶ 𝟙_ C) (f : X ⟶ Y) :
    (f ▷ Q) ≫ (Y ◁ q) ≫ (ρ_ Y).hom =
      ((X ◁ q) ≫ (ρ_ X).hom) ≫ f :=
  (rightUnitReplacementMap q).naturality f

/-- A specified comparison over the same unit preserves the entire left
unit natural transformation, including every tensor and unitor map. -/
theorem leftUnitReplacementMap_comparison
    {Q Q' : C} (q : Q ⟶ 𝟙_ C) (q' : Q' ⟶ 𝟙_ C)
    (a : Q ⟶ Q') (ha : a ≫ q' = q) :
    (tensoringLeft C).map a ≫ leftUnitReplacementMap q' =
      leftUnitReplacementMap q := by
  ext X
  change (a ▷ X) ≫ (q' ▷ X) ≫ (λ_ X).hom = (q ▷ X) ≫ (λ_ X).hom
  rw [← Category.assoc, ← comp_whiskerRight, ha]

/-- The same specified comparison preserves the entire right unit map. -/
theorem rightUnitReplacementMap_comparison
    {Q Q' : C} (q : Q ⟶ 𝟙_ C) (q' : Q' ⟶ 𝟙_ C)
    (a : Q ⟶ Q') (ha : a ≫ q' = q) :
    (tensoringRight C).map a ≫ rightUnitReplacementMap q' =
      rightUnitReplacementMap q := by
  ext X
  change (X ◁ a) ≫ (X ◁ q') ≫ (ρ_ X).hom = (X ◁ q) ≫ (ρ_ X).hom
  rw [← Category.assoc, ← whiskerLeft_comp, ha]

end UnitMaps

namespace MonoidalPushoutProductAxiom

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
variable (hPP : MonoidalPushoutProductAxiom C)
include hPP

/-- A true cofibrant unit verifies the left tensor unit condition for the
actual supplied replacement map. -/
theorem unitReplacement_whiskerRight_weak
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) (X : C) [IsCofibrant X] :
    weakEquivalences C (q ▷ X) :=
  hPP.whiskerRight_mem_weakEquivalences q X inferInstance hQ inferInstance hq.2

/-- The same true cofibrant unit and the same replacement map verify the
right tensor unit condition. -/
theorem unitReplacement_whiskerLeft_weak
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) (X : C) [IsCofibrant X] :
    weakEquivalences C (X ◁ q) :=
  hPP.whiskerLeft_mem_weakEquivalences X inferInstance q hQ inferInstance hq.2

/-- The actual left unitor composite of the given replacement is weak on
each cofibrant object. -/
theorem leftUnitReplacementMap_weak
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) (X : C) [IsCofibrant X] :
    weakEquivalences C ((leftUnitReplacementMap q).app X) := by
  let _ : WeakEquivalence (q ▷ X) :=
    (weakEquivalence_iff _).mpr (hPP.unitReplacement_whiskerRight_weak q hQ hq X)
  rw [leftUnitReplacementMap_app]
  exact mem_weakEquivalences _

/-- The actual right unitor composite of the same replacement is weak. -/
theorem rightUnitReplacementMap_weak
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) (X : C) [IsCofibrant X] :
    weakEquivalences C ((rightUnitReplacementMap q).app X) := by
  let _ : WeakEquivalence (X ◁ q) :=
    (weakEquivalence_iff _).mpr (hPP.unitReplacement_whiskerLeft_weak q hQ hq X)
  rw [rightUnitReplacementMap_app]
  exact mem_weakEquivalences _

/-- The unit witness contains the same given cofibrant replacement object
and map. Its tensor condition is proved from PP and true unit cofibrancy. -/
noncomputable def unitAxiomWitnessOfCofibrantUnit
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) : MonoidalUnitAxiomWitness C where
  Q := Q
  q := q
  Q_cofibrant := hQ
  q_trivialFibration := hq
  tensor_weak X hX := by
    let _ : IsCofibrant X := hX
    exact hPP.unitReplacement_whiskerRight_weak q hQ hq X

@[simp]
theorem unitAxiomWitnessOfCofibrantUnit_Q
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) :
    (hPP.unitAxiomWitnessOfCofibrantUnit q hQ hq).Q = Q :=
  rfl

@[simp]
theorem unitAxiomWitnessOfCofibrantUnit_q
    [IsCofibrant (𝟙_ C)] {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) :
    (hPP.unitAxiomWitnessOfCofibrantUnit q hQ hq).q = q :=
  rfl

omit hPP [BraidedCategory C] [MonoidalClosed C] in
/-- The original factorization of the initial unit map already proves
cofibrancy of its own middle object. No replacement algorithm is chosen. -/
theorem isCofibrant_unitFactor
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) : IsCofibrant d.Z := by
  exact (isCofibrant_iff_of_isInitial d.i initialIsInitial).mpr
    ((cofibration_iff _).mpr d.hi)

/-- The actual supplied initial-unit factor yields the unit witness, with
exactly its original middle object and right factor. -/
noncomputable def unitAxiomWitnessOfUnitFactor
    [IsCofibrant (𝟙_ C)]
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) : MonoidalUnitAxiomWitness C :=
  hPP.unitAxiomWitnessOfCofibrantUnit d.p (isCofibrant_unitFactor d) d.hp

@[simp]
theorem unitAxiomWitnessOfUnitFactor_Q
    [IsCofibrant (𝟙_ C)]
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    (hPP.unitAxiomWitnessOfUnitFactor d).Q = d.Z :=
  rfl

@[simp]
theorem unitAxiomWitnessOfUnitFactor_q
    [IsCofibrant (𝟙_ C)]
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    (hPP.unitAxiomWitnessOfUnitFactor d).q = d.p :=
  rfl

/-- The original factor equation is preserved by the selected unit witness. -/
theorem unitAxiomWitnessOfUnitFactor_fac
    [IsCofibrant (𝟙_ C)]
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    d.i ≫ (hPP.unitAxiomWitnessOfUnitFactor d).q = initial.to (𝟙_ C) :=
  d.fac

omit [BraidedCategory C] in
/-- PP and true unit cofibrancy give the full monoidal model axiom record
using the caller's original factor, rather than the identity replacement. -/
theorem monoidalModelOfUnitFactor
    [SymmetricCategory C] [IsCofibrant (𝟙_ C)]
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    IsClosedSymmetricMonoidalModelCategory C where
  cofibration_pushoutProduct := hPP.cofibration_pushoutProduct
  trivial_pushoutProduct_left := hPP.trivial_pushoutProduct_left
  trivial_pushoutProduct_right := hPP.trivial_pushoutProduct_right
  unit_axiom := ⟨hPP.unitAxiomWitnessOfUnitFactor d⟩

/-- The whole original functorial factorization supplies its literal
initial-unit factor to the unit construction. -/
noncomputable def unitAxiomWitnessOfFunctorialFactorization
    [IsCofibrant (𝟙_ C)]
    (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    MonoidalUnitAxiomWitness C :=
  hPP.unitAxiomWitnessOfUnitFactor (F.factorizationData (initial.to (𝟙_ C)))

@[simp]
theorem unitAxiomWitnessOfFunctorialFactorization_Q
    [IsCofibrant (𝟙_ C)]
    (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (hPP.unitAxiomWitnessOfFunctorialFactorization F).Q =
      F.Z.obj (Arrow.mk (initial.to (𝟙_ C))) :=
  rfl

@[simp]
theorem unitAxiomWitnessOfFunctorialFactorization_q
    [IsCofibrant (𝟙_ C)]
    (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (hPP.unitAxiomWitnessOfFunctorialFactorization F).q =
      F.p.app (Arrow.mk (initial.to (𝟙_ C))) :=
  rfl

end MonoidalPushoutProductAxiom

end HomotopicalAlgebra
