/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitFromPushoutProduct

/-!
# The same unit factor under a change of model with unchanged cofibrations

Two explicitly selected models on the same category with the same
cofibrations have the same trivial fibrations by their original WFS.
Cofibrancy and the entire original cofibrant factorization therefore
transport by membership proofs alone. The unit witness keeps the same
middle functor and natural maps. No model, replacement algorithm,
generating family, cardinal or tensor structure is selected here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra.ModelCategory

variable {C : Type u} [Category.{v} C]

/-- Equality of the actual cofibration classes forces equality of the
actual trivial fibration classes through both original WFS equations. -/
theorem trivialFibrations_eq_of_cofibrations_eq
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C)) :
    (letI : ModelCategory C := M₀; trivialFibrations C) =
      (letI : ModelCategory C := M₁; trivialFibrations C) := by
  have h₀ : (letI : ModelCategory C := M₀; cofibrations C).rlp =
      (letI : ModelCategory C := M₀; trivialFibrations C) := by
    let _ : ModelCategory C := M₀
    exact cofibrations_rlp C
  have h₁ : (letI : ModelCategory C := M₁; cofibrations C).rlp =
      (letI : ModelCategory C := M₁; trivialFibrations C) := by
    let _ : ModelCategory C := M₁
    exact cofibrations_rlp C
  exact h₀.symm.trans ((congrArg MorphismProperty.rlp hCof).trans h₁)

/-- The same objects are cofibrant in both explicitly selected models
when their original cofibration classes agree. -/
theorem isCofibrant_iff_of_cofibrations_eq
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C)) (X : C) :
    (letI : ModelCategory C := M₀; IsCofibrant X) ↔
      (letI : ModelCategory C := M₁; IsCofibrant X) := by
  let _ : ModelCategory C := M₀
  simp only [cofibration_iff]
  change (letI : ModelCategory C := M₀; cofibrations C) (initial.to X) ↔
    (letI : ModelCategory C := M₁; cofibrations C) (initial.to X)
  rw [hCof]

/-- An individual caller-supplied factor record retains its exact middle
object, maps and factor equation under the same class transport. -/
noncomputable def cofibrantMapFactorizationOfCofibrationsEq
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    {X Y : C} (f : X ⟶ Y)
    (d : letI : ModelCategory C := M₀;
      MapFactorizationData (cofibrations C) (trivialFibrations C) f) :
    letI : ModelCategory C := M₁;
    MapFactorizationData (cofibrations C) (trivialFibrations C) f where
  Z := d.Z
  i := d.i
  p := d.p
  fac := d.fac
  hi := hCof.le _ d.hi
  hp := (trivialFibrations_eq_of_cofibrations_eq M₀ M₁ hCof).le _ d.hp

/-- The original functorial cofibrant factorization is retained as a whole
under the new model. Only its two membership proofs are transported. -/
noncomputable def cofibrantFactorizationOfCofibrationsEq
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    letI : ModelCategory C := M₁;
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) :=
  F.ofLE hCof.le (trivialFibrations_eq_of_cofibrations_eq M₀ M₁ hCof).le

/-- The full original middle functor, with every Arrow input and map, is
unchanged by membership transport. -/
@[simp]
theorem cofibrantFactorizationOfCofibrationsEq_Z
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (cofibrantFactorizationOfCofibrationsEq M₀ M₁ hCof F).Z = F.Z :=
  rfl

/-- The entire original left factor transformation is preserved. -/
@[simp]
theorem cofibrantFactorizationOfCofibrationsEq_i
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (cofibrantFactorizationOfCofibrationsEq M₀ M₁ hCof F).i = F.i :=
  rfl

/-- The entire original right factor transformation is preserved. -/
@[simp]
theorem cofibrantFactorizationOfCofibrationsEq_p
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (cofibrantFactorizationOfCofibrationsEq M₀ M₁ hCof F).p = F.p :=
  rfl

/-- Every original Arrow factor equation is retained after the class
change, without comparing independently selected middle objects. -/
theorem cofibrantFactorizationOfCofibrationsEq_fac
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) (f : Arrow C) :
    (cofibrantFactorizationOfCofibrationsEq M₀ M₁ hCof F).i.app f ≫
      (cofibrantFactorizationOfCofibrationsEq M₀ M₁ hCof F).p.app f = f.hom :=
  F.fac_app

section MonoidalUnit

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- The same original individual initial-unit factor is a unit witness
under the new model, after transferring true original unit cofibrancy. -/
noncomputable def unitAxiomWitnessOfCofibrationsEqUnitFactor
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (d : letI : ModelCategory C := M₀;
      MapFactorizationData (cofibrations C) (trivialFibrations C) (initial.to (𝟙_ C))) :
    letI : ModelCategory C := M₁; MonoidalUnitAxiomWitness C := by
  let _ : ModelCategory C := M₁
  let _ : IsCofibrant (𝟙_ C) :=
    (isCofibrant_iff_of_cofibrations_eq M₀ M₁ hCof (𝟙_ C)).mp hUnit
  exact hPP.unitAxiomWitnessOfUnitFactor
    (cofibrantMapFactorizationOfCofibrationsEq M₀ M₁ hCof (initial.to (𝟙_ C)) d)

/-- The replacement source of the transported unit witness is exactly the
caller-supplied middle object, not a newly generated one. -/
@[simp]
theorem unitAxiomWitnessOfCofibrationsEqUnitFactor_Q
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (d : letI : ModelCategory C := M₀;
      MapFactorizationData (cofibrations C) (trivialFibrations C) (initial.to (𝟙_ C))) :
    (unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d).Q = d.Z :=
  rfl

/-- The actual replacement map is the same original right factor. -/
@[simp]
theorem unitAxiomWitnessOfCofibrationsEqUnitFactor_q
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (d : letI : ModelCategory C := M₀;
      MapFactorizationData (cofibrations C) (trivialFibrations C) (initial.to (𝟙_ C))) :
    (unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d).q = d.p :=
  rfl

/-- True unit cofibrancy in the original model transfers to the selected
new model with the same cofibrations. PP-only Brown then verifies the unit
condition for the SAME original full functorial factorization. -/
noncomputable def unitAxiomWitnessOfCofibrationsEq
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    letI : ModelCategory C := M₁; MonoidalUnitAxiomWitness C := by
  let _ : ModelCategory C := M₁
  let _ : IsCofibrant (𝟙_ C) :=
    (isCofibrant_iff_of_cofibrations_eq M₀ M₁ hCof (𝟙_ C)).mp hUnit
  exact hPP.unitAxiomWitnessOfFunctorialFactorization
    (cofibrantFactorizationOfCofibrationsEq M₀ M₁ hCof F)

/-- The resulting unit replacement source is the original middle functor
evaluated on the original initial-unit Arrow. -/
@[simp]
theorem unitAxiomWitnessOfCofibrationsEq_Q
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (unitAxiomWitnessOfCofibrationsEq M₀ M₁ hCof hPP hUnit F).Q =
      F.Z.obj (Arrow.mk (letI : ModelCategory C := M₀; initial.to (𝟙_ C))) :=
  rfl

/-- The resulting unit replacement map is exactly the original right
factor at that same initial-unit Arrow. -/
@[simp]
theorem unitAxiomWitnessOfCofibrationsEq_q
    (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (F : letI : ModelCategory C := M₀;
      FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    (unitAxiomWitnessOfCofibrationsEq M₀ M₁ hCof hPP hUnit F).q =
      F.p.app (Arrow.mk (letI : ModelCategory C := M₀; initial.to (𝟙_ C))) :=
  rfl

end MonoidalUnit

end HomotopicalAlgebra.ModelCategory

namespace HomotopicalAlgebra.ModelCategory.TypedUnitModelChange

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

variable (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (d : letI : ModelCategory C := M₀;
      MapFactorizationData (cofibrations C) (trivialFibrations C) (initial.to (𝟙_ C)))

include M₀ hCof hUnit in
omit [BraidedCategory C] [MonoidalClosed C] in
/-- The true unit cofibrancy is transferred from the actual original model. -/
theorem selectedUnit_isCofibrant :
    letI : ModelCategory C := M₁; IsCofibrant (𝟙_ C) :=
  (isCofibrant_iff_of_cofibrations_eq M₀ M₁ hCof (𝟙_ C)).mp hUnit

include hCof hPP hUnit in
/-- The same full original source is cofibrant in the new model. -/
theorem originalFactor_isCofibrant :
    letI : ModelCategory C := M₁; IsCofibrant d.Z :=
  (unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d).Q_cofibrant

include hCof hPP hUnit in
/-- The same full original right factor is a true trivial fibration in the new model. -/
theorem originalFactor_isTrivialFibration :
    letI : ModelCategory C := M₁; trivialFibrations C d.p :=
  (unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d).q_trivialFibration

include M₀ hCof hPP hUnit d in
omit [BraidedCategory C] in
/-- All four monoidal model laws use the actual selected new model and the same original factor. -/
theorem monoidalModel [SymmetricCategory C] :
    letI : ModelCategory C := M₁; IsClosedSymmetricMonoidalModelCategory C := by
  let : ModelCategory C := M₁
  exact { cofibration_pushoutProduct := hPP.cofibration_pushoutProduct
          trivial_pushoutProduct_left := hPP.trivial_pushoutProduct_left
          trivial_pushoutProduct_right := hPP.trivial_pushoutProduct_right
          unit_axiom := ⟨unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d⟩ }


include M₀ hCof hPP hUnit d in
/-- The existing transported unit witness satisfies the full left replacement law in the new model.
-/
theorem leftUnitReplacement (X : C)
    (hX : letI : ModelCategory C := M₁; IsCofibrant X) :
    letI : ModelCategory C := M₁;
    weakEquivalences C
      ((leftUnitReplacementMap
          (unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d).q).app X) := by
  let : ModelCategory C := M₁
  let : IsCofibrant X := hX
  let : IsCofibrant (𝟙_ C) := selectedUnit_isCofibrant M₀ M₁ hCof hUnit
  let w : MonoidalUnitAxiomWitness C := unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP
      hUnit d
  exact hPP.leftUnitReplacementMap_weak w.q w.Q_cofibrant w.q_trivialFibration X

include M₀ hCof hPP hUnit d in
/-- The existing transported unit witness satisfies the full right replacement law in the new model.
-/
theorem rightUnitReplacement (X : C)
    (hX : letI : ModelCategory C := M₁; IsCofibrant X) :
    letI : ModelCategory C := M₁;
    weakEquivalences C
      ((rightUnitReplacementMap
          (unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP hUnit d).q).app X) := by
  let : ModelCategory C := M₁
  let : IsCofibrant X := hX
  let : IsCofibrant (𝟙_ C) := selectedUnit_isCofibrant M₀ M₁ hCof hUnit
  let w : MonoidalUnitAxiomWitness C := unitAxiomWitnessOfCofibrationsEqUnitFactor M₀ M₁ hCof hPP
      hUnit d
  exact hPP.rightUnitReplacementMap_weak w.q w.Q_cofibrant w.q_trivialFibration X

end HomotopicalAlgebra.ModelCategory.TypedUnitModelChange
