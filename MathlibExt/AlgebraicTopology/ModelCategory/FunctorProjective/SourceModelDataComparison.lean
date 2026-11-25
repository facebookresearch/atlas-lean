/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EquivalenceModelData
import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacementsEquivalence
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeEquivalence
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeRoundtrip

/-!
# Whole original projective model and replacement data

The original ordinary source factory and its two original small-side
algorithms are retained. Their complete factor diagrams compare through the
actual chosen index equivalence. The caller's original initial and terminal
objects give the two replacements, and the same whole comparisons preserve
all their object and map functions and both endpoint maps.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra.GivenFactorizationReplacements

namespace HomotopicalAlgebra.FunctorProjective.SourceConstruction.FromData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] (d : CofibrantGenerationData C κ)
  (s : Functor.EssentialIndexData.{w} D C)

local instance comparisonSmallIndexLocallySmall : LocallySmall.{w} s.index :=
  locallySmall_self s.index

/-- The whole original source model is the existing transport of its actual small-side model. -/
theorem modelCategory_eq_equivalenceTransport :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    modelCategory d s =
      CofibrantGenerationData.Equivalence.modelCategory (s.equivalence.congrLeft (E := C)) := by
  apply ModelCategory.eq_of_classes <;> rfl

/-- One whole original I diagram comparison retains its source, middle, target and both arrows. -/
def cofibrantWholeFactorizationIso :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    (cofibrantFactorizationData d s).originalFactorizationFunctor ⋙
        (s.equivalence.congrLeft (E := C)).functor.mapComposableArrows 2 ≅
      (s.equivalence.congrLeft (E := C)).functor.mapArrow ⋙
        FunctorialFactorizationData.originalFactorizationFunctor
          (FunctorProjective.cofibrantFactorizationData (D := s.index) d) := by
  letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
  exact FunctorialFactorizationData.originalWholeFactorizationEquivalenceIso
    (FunctorProjective.cofibrantFactorizationData (D := s.index) d)
    (s.equivalence.congrLeft (E := C))

/-- The same whole original J diagram comparison uses the actual second small-side algorithm. -/
def fibrantWholeFactorizationIso :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    (fibrantFactorizationData d s).originalFactorizationFunctor ⋙
        (s.equivalence.congrLeft (E := C)).functor.mapComposableArrows 2 ≅
      (s.equivalence.congrLeft (E := C)).functor.mapArrow ⋙
        FunctorialFactorizationData.originalFactorizationFunctor
          (FunctorProjective.fibrantFactorizationData (D := s.index) d) := by
  letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
  exact FunctorialFactorizationData.originalWholeFactorizationEquivalenceIso
    (FunctorProjective.fibrantFactorizationData (D := s.index) d)
    (s.equivalence.congrLeft (E := C))

/-- The complete original I algorithm returns through its actual chosen index unit. -/
def cofibrantWholeRoundtripIso :
    (((cofibrantFactorizationData d s).ofEquivalence
      (s.equivalence.congrLeft (E := C)).symm).ofEquivalence
        (s.equivalence.congrLeft (E := C))).originalFactorizationFunctor ≅
      (cofibrantFactorizationData d s).originalFactorizationFunctor :=
  (cofibrantFactorizationData d s).originalWholeFactorizationRoundtripIso
    (s.equivalence.congrLeft (E := C))

/-- The same original index unit returns the entire original J algorithm and both factors. -/
def fibrantWholeRoundtripIso :
    (((fibrantFactorizationData d s).ofEquivalence
      (s.equivalence.congrLeft (E := C)).symm).ofEquivalence
        (s.equivalence.congrLeft (E := C))).originalFactorizationFunctor ≅
      (fibrantFactorizationData d s).originalFactorizationFunctor :=
  (fibrantFactorizationData d s).originalWholeFactorizationRoundtripIso
    (s.equivalence.congrLeft (E := C))

/-- The caller's original initial arrows and native first algorithm give the whole Q functor. -/
def cofibrantReplacement (Z : D ⥤ C) (hZ : IsInitial Z) : (D ⥤ C) ⥤ (D ⥤ C) :=
  initialReplacement (cofibrantFactorizationData d s) Z hZ

/-- The complete original first projection is Q's counit to the unchanged original diagram. -/
def cofibrantReplacementCounit (Z : D ⥤ C) (hZ : IsInitial Z) :
    cofibrantReplacement d s Z hZ ⟶ 𝟭 (D ⥤ C) :=
  initialProjection (cofibrantFactorizationData d s) Z hZ

/-- Q retains the original initial leg from that same whole factor record. -/
def initialToCofibrantReplacement (Z : D ⥤ C) (hZ : IsInitial Z) :
    (Functor.const (D ⥤ C)).obj Z ⟶ cofibrantReplacement d s Z hZ :=
  initialLeg (cofibrantFactorizationData d s) Z hZ

/-- The original terminal arrows and second native algorithm give the whole R functor. -/
def fibrantReplacement (Z : D ⥤ C) (hZ : IsTerminal Z) : (D ⥤ C) ⥤ (D ⥤ C) :=
  terminalReplacement (fibrantFactorizationData d s) Z hZ

/-- The original second inclusion is R's unit on the unchanged original diagrams. -/
def fibrantReplacementUnit (Z : D ⥤ C) (hZ : IsTerminal Z) :
    𝟭 (D ⥤ C) ⟶ fibrantReplacement d s Z hZ :=
  terminalUnit (fibrantFactorizationData d s) Z hZ

/-- R retains its original terminal leg from the same native second factorization. -/
def fibrantReplacementToTerminal (Z : D ⥤ C) (hZ : IsTerminal Z) :
    fibrantReplacement d s Z hZ ⟶ (Functor.const (D ⥤ C)).obj Z :=
  terminalLeg (fibrantFactorizationData d s) Z hZ

/-- The entire Q functor retains the original initial-arrow family and every native Arrow map. -/
theorem cofibrantReplacement_original_functor (Z : D ⥤ C) (hZ : IsInitial Z) :
    cofibrantReplacement d s Z hZ = initialArrows Z hZ ⋙ (cofibrantFactorizationData d s).Z :=
  rfl

/-- The entire R functor retains the actual terminal-arrow family and every native Arrow map. -/
theorem fibrantReplacement_original_functor (Z : D ⥤ C) (hZ : IsTerminal Z) :
    fibrantReplacement d s Z hZ = terminalArrows Z hZ ⋙ (fibrantFactorizationData d s).Z :=
  rfl

/-- Every original Q map is the same native algorithm on the original initial-endpoint square. -/
theorem cofibrantReplacement_original_map (Z : D ⥤ C) (hZ : IsInitial Z)
    {X Y : D ⥤ C} (f : X ⟶ Y) :
    (cofibrantReplacement d s Z hZ).map f =
      (cofibrantFactorizationData d s).Z.map (Arrow.homMk (𝟙 Z) f (hZ.hom_ext _ _)) := rfl

/-- Every original R map retains the original terminal endpoint and native middle map. -/
theorem fibrantReplacement_original_map (Z : D ⥤ C) (hZ : IsTerminal Z)
    {X Y : D ⥤ C} (f : X ⟶ Y) :
    (fibrantReplacement d s Z hZ).map f =
      (fibrantFactorizationData d s).Z.map (Arrow.homMk f (𝟙 Z) (hZ.hom_ext _ _)) := rfl

/-- Both complete Q legs factor the same original initial-map transformation. -/
theorem cofibrantReplacement_fac (Z : D ⥤ C) (hZ : IsInitial Z) :
    initialToCofibrantReplacement d s Z hZ ≫ cofibrantReplacementCounit d s Z hZ =
      initialMapNatTrans Z hZ := initial_fac (cofibrantFactorizationData d s) Z hZ

/-- Both complete R legs recover the caller's original terminal-map transformation. -/
theorem fibrantReplacement_fac (Z : D ⥤ C) (hZ : IsTerminal Z) :
    fibrantReplacementUnit d s Z hZ ≫ fibrantReplacementToTerminal d s Z hZ =
      terminalMapNatTrans Z hZ := terminal_fac (fibrantFactorizationData d s) Z hZ

/-- The actual index equivalence compares all Q objects and maps to the same small-side data. -/
def cofibrantReplacementComparisonIso (Z : D ⥤ C) (hZ : IsInitial Z) :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    cofibrantReplacement d s Z hZ ⋙ (s.equivalence.congrLeft (E := C)).functor ≅
      (s.equivalence.congrLeft (E := C)).functor ⋙
        initialReplacement (FunctorProjective.cofibrantFactorizationData (D := s.index) d)
          ((s.equivalence.congrLeft (E := C)).functor.obj Z)
          (hZ.isInitialObj (s.equivalence.congrLeft (E := C)).functor Z) := by
  letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
  exact initialReplacementEquivalenceIso
    (FunctorProjective.cofibrantFactorizationData (D := s.index) d)
    (s.equivalence.congrLeft (E := C)) Z hZ

/-- The same complete original index comparison also retains all R objects and maps. -/
def fibrantReplacementComparisonIso (Z : D ⥤ C) (hZ : IsTerminal Z) :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    fibrantReplacement d s Z hZ ⋙ (s.equivalence.congrLeft (E := C)).functor ≅
      (s.equivalence.congrLeft (E := C)).functor ⋙
        terminalReplacement (FunctorProjective.fibrantFactorizationData (D := s.index) d)
          ((s.equivalence.congrLeft (E := C)).functor.obj Z)
          (hZ.isTerminalObj (s.equivalence.congrLeft (E := C)).functor Z) := by
  letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
  exact terminalReplacementEquivalenceIso
    (FunctorProjective.fibrantFactorizationData (D := s.index) d)
    (s.equivalence.congrLeft (E := C)) Z hZ

/-- The original Q inclusion and projection have the exact constructed projective classes. -/
theorem cofibrantReplacement_classes (Z : D ⥤ C) (hZ : IsInitial Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    cofibrations (D ⥤ C) ((initialToCofibrantReplacement d s Z hZ).app X) ∧
      trivialFibrations (D ⥤ C) ((cofibrantReplacementCounit d s Z hZ).app X) := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  constructor
  · rw [(five_classes d s).2.2.2.1]
    exact (cofibrantFactorizationData d s).hi _
  · rw [(five_classes d s).2.2.1]
    exact (cofibrantFactorizationData d s).hp _

/-- Both original R legs retain the constructed trivial-cofibration and fibration classes. -/
theorem fibrantReplacement_classes (Z : D ⥤ C) (hZ : IsTerminal Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    trivialCofibrations (D ⥤ C) ((fibrantReplacementUnit d s Z hZ).app X) ∧
      fibrations (D ⥤ C) ((fibrantReplacementToTerminal d s Z hZ).app X) := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  constructor
  · rw [(five_classes d s).2.2.2.2]
    exact (fibrantFactorizationData d s).hi _
  · rw [(five_classes d s).2.1]
    exact (fibrantFactorizationData d s).hp _

/-- Every returned Q object is cofibrant using its actual original initial leg. -/
theorem cofibrantReplacement_isCofibrant (Z : D ⥤ C) (hZ : IsInitial Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    IsCofibrant ((cofibrantReplacement d s Z hZ).obj X) := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  apply (isCofibrant_iff_of_isInitial ((initialToCofibrantReplacement d s Z hZ).app X) hZ).2
  exact (cofibration_iff _).2 (cofibrantReplacement_classes d s Z hZ X).1

/-- Every returned R object is fibrant by the same original terminal leg. -/
theorem fibrantReplacement_isFibrant (Z : D ⥤ C) (hZ : IsTerminal Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    IsFibrant ((fibrantReplacement d s Z hZ).obj X) := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  apply (isFibrant_iff_of_isTerminal ((fibrantReplacementToTerminal d s Z hZ).app X) hZ).2
  exact (fibration_iff _).2 (fibrantReplacement_classes d s Z hZ X).2

end HomotopicalAlgebra.FunctorProjective.SourceConstruction.FromData
