/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementComparisons
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Complete replacement data from the original functorial factors

The actual cofibration and fibration factories construct the full Q/R data
and every original natural comparison. Conventional generation specializes
the same interface with its literal fixed-cardinal factories and maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedFunctorialReplacements

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]

/-- Actual chosen functorial factors and their complete replacement data. -/
structure Data where
  /-- The full supplied cofibration factorization record on every Arrow. -/
  cofibrantFactor : FunctorialFactorizationData (cofibrations C) (trivialFibrations C)
  /-- The full supplied fibration factorization record on every Arrow. -/
  fibrantFactor : FunctorialFactorizationData (trivialCofibrations C) (fibrations C)
  /-- The complete chosen cofibrant replacement functor. -/
  Q : C ⥤ C
  /-- The complete chosen fibrant replacement functor. -/
  R : C ⥤ C
  /-- The full original initial factor arrow into Q. -/
  qInitial : (Functor.const C).obj (⊥_ C) ⟶ Q
  /-- The full original natural weak Q counit. -/
  q : Q ⟶ 𝟭 C
  /-- The full original natural weak R unit. -/
  r : 𝟭 C ⟶ R
  /-- The full original terminal factor arrow out of R. -/
  rTerminal : R ⟶ (Functor.const C).obj (⊤_ C)
  /-- The same initial factor arrows recover every original initial map. -/
  q_fac : qInitial ≫ q = initialMap
  /-- The same terminal factor arrows recover every original terminal map. -/
  r_fac : r ≫ rTerminal = terminalMap
  /-- All Q objects are actually cofibrant. -/
  q_cofibrant (X : C) : IsCofibrant (Q.obj X)
  /-- All R objects are actually fibrant. -/
  r_fibrant (X : C) : IsFibrant (R.obj X)
  /-- The original Q counit is a trivial fibration at every object. -/
  q_trivialFibration (X : C) : trivialFibrations C (q.app X)
  /-- The original R unit is a trivial cofibration at every object. -/
  r_trivialCofibration (X : C) : trivialCofibrations C (r.app X)
  /-- Q preserves all original weak equivalences. -/
  q_map_weak {X Y : C} (f : X ⟶ Y) : weakEquivalences C f → weakEquivalences C (Q.map f)
  /-- R preserves all original weak equivalences. -/
  r_map_weak {X Y : C} (f : X ⟶ Y) : weakEquivalences C f → weakEquivalences C (R.map f)

section FactorFactories

variable {B : Type uC} [Category.{vC} B] [ModelCategory B]
  (Fc : FunctorialFactorizationData (cofibrations B) (trivialFibrations B))
  (Ff : FunctorialFactorizationData (trivialCofibrations B) (fibrations B))

/-- The original cofibration factory factors the full natural initial arrow. -/
def initialFactory :
    MapFactorizationData ((cofibrations B).functorCategory B)
      ((trivialFibrations B).functorCategory B)
      (GeneratedFunctorialReplacements.initialMap (C := B)) :=
  (Fc.functorCategory B).factorizationData GeneratedFunctorialReplacements.initialMap

/-- The original fibration factory factors the full natural terminal arrow. -/
def terminalFactory :
    MapFactorizationData ((trivialCofibrations B).functorCategory B)
      ((fibrations B).functorCategory B)
      (GeneratedFunctorialReplacements.terminalMap (C := B)) :=
  (Ff.functorCategory B).factorizationData GeneratedFunctorialReplacements.terminalMap

/-- The two actual functorial factories construct complete replacement data in any model category.
-/
def replacementsOfFactors : GeneratedFunctorialReplacements.Data (C := B) where
  cofibrantFactor := Fc
  fibrantFactor := Ff
  Q := (initialFactory Fc).Z
  R := (terminalFactory Ff).Z
  qInitial := (initialFactory Fc).i
  q := (initialFactory Fc).p
  r := (terminalFactory Ff).i
  rTerminal := (terminalFactory Ff).p
  q_fac := (initialFactory Fc).fac
  r_fac := (terminalFactory Ff).fac
  q_cofibrant X :=
    (isCofibrant_iff_of_isInitial ((initialFactory Fc).i.app X) initialIsInitial).mpr
      ((cofibration_iff _).mpr ((initialFactory Fc).hi X))
  r_fibrant X :=
    (isFibrant_iff_of_isTerminal ((terminalFactory Ff).p.app X) terminalIsTerminal).mpr
      ((fibration_iff _).mpr ((terminalFactory Ff).hp X))
  q_trivialFibration := (initialFactory Fc).hp
  r_trivialCofibration := (terminalFactory Ff).hi
  q_map_weak := by
    intro X Y a ha
    apply (weakEquivalences B).of_postcomp _ ((initialFactory Fc).p.app Y)
      ((initialFactory Fc).hp Y).2
    rw [(initialFactory Fc).p.naturality]
    exact (weakEquivalences B).comp_mem _ _ ((initialFactory Fc).hp X).2 ha
  r_map_weak := by
    intro X Y a ha
    apply (weakEquivalences B).of_precomp ((terminalFactory Ff).i.app X) _
      ((terminalFactory Ff).hi X).2
    rw [← (terminalFactory Ff).i.naturality]
    exact (weakEquivalences B).comp_mem _ _ ha ((terminalFactory Ff).hi Y).2

/-- Both original whole factor records survive in the constructed data. -/
theorem replacementsOfFactors_factors :
    (replacementsOfFactors Fc Ff).cofibrantFactor = Fc ∧
      (replacementsOfFactors Fc Ff).fibrantFactor = Ff := ⟨rfl, rfl⟩

/-- The actual initial-factor middle functor is the constructed Q, on objects and all maps. -/
theorem replacementsOfFactors_Q :
    (replacementsOfFactors Fc Ff).Q = (initialFactory Fc).Z := rfl

/-- The actual terminal-factor middle functor is the constructed R, on objects and all maps. -/
theorem replacementsOfFactors_R :
    (replacementsOfFactors Fc Ff).R = (terminalFactory Ff).Z := rfl

/-- Each whole original initial square retains the actual factory's Q middle map. -/
theorem replacementsOfFactors_Q_map {X Y : B} (a : X ⟶ Y) :
    (replacementsOfFactors Fc Ff).Q.map a =
      Fc.Z.map (Arrow.homMk (𝟙 (⊥_ B)) a (by simp [GeneratedFunctorialReplacements.initialMap])) :=
        rfl

/-- Each whole original terminal square retains the actual factory's R middle map. -/
theorem replacementsOfFactors_R_map {X Y : B} (a : X ⟶ Y) :
    (replacementsOfFactors Fc Ff).R.map a =
      Ff.Z.map (Arrow.homMk a (𝟙 (⊤_ B)) (by simp [GeneratedFunctorialReplacements.terminalMap])) :=
        rfl

end FactorFactories

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Actual conventional generation constructs all complete functorial factors and replacements. -/
def fromGeneration (d : CofibrantGenerationData C κ) : Data (C := C) where
  cofibrantFactor := d.cofibrantFactorizationData
  fibrantFactor := d.fibrantFactorizationData
  Q := Q d
  R := R d
  qInitial := initialLeg d
  q := counit d
  r := unit d
  rTerminal := terminalLeg d
  q_fac := initial_fac d
  r_fac := terminal_fac d
  q_cofibrant := Q_isCofibrant d
  r_fibrant := R_isFibrant d
  q_trivialFibration := counit_trivialFibration d
  r_trivialCofibration := unit_trivialCofibration d
  q_map_weak := Q_map_weak d
  r_map_weak := R_map_weak d

/-- Conventional generation supplies complete data without incoming factor/replacement outcomes. -/
theorem constructs (d : CofibrantGenerationData C κ) : Nonempty (Data (C := C)) :=
  ⟨fromGeneration d⟩

/-- The complete constructed I factor is the exact original generation factory. -/
theorem fromGeneration_cofibrantFactor (d : CofibrantGenerationData C κ) :
    (fromGeneration d).cofibrantFactor = d.cofibrantFactorizationData := rfl

/-- The complete constructed J factor is the exact original generation factory. -/
theorem fromGeneration_fibrantFactor (d : CofibrantGenerationData C κ) :
    (fromGeneration d).fibrantFactor = d.fibrantFactorizationData := rfl

/-- The complete constructed Q object and morphism functions are the original initial restriction.
-/
theorem fromGeneration_Q (d : CofibrantGenerationData C κ) : (fromGeneration d).Q = Q d := rfl

/-- The complete constructed R object and morphism functions are the original terminal restriction.
-/
theorem fromGeneration_R (d : CofibrantGenerationData C κ) : (fromGeneration d).R = R d := rfl

/-- The entire constructed weak counit is the original natural I projection. -/
theorem fromGeneration_q (d : CofibrantGenerationData C κ) : (fromGeneration d).q = counit d := rfl

/-- The entire constructed weak unit is the original natural J inclusion. -/
theorem fromGeneration_r (d : CofibrantGenerationData C κ) : (fromGeneration d).r = unit d := rfl

end HomotopicalAlgebra.GeneratedFunctorialReplacements
