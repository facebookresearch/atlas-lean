/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacementsEquivalence
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeFunctor
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeRoundtrip

/-!
# Whole original injective factor and replacement data

The coefficient source, complete original index equivalence and produced
common-rank generation are unchanged. Reclassification retains the whole
two-factor functors and both given natural maps. The original endpoint
certificates and these same algorithms construct Q and R on the unchanged
ordinary functor category, with all source classes and every Arrow map.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra.GivenFactorizationReplacements

namespace HomotopicalAlgebra.FunctorInjective.SourceConstruction.CoefficientData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] (c : CoefficientData.{w} C)
  (s : Functor.EssentialIndexData.{w} D C)

local instance comparisonCoefficientRegular : Fact c.cardinal.IsRegular := c.regular
/-- The exact original coefficient witness supplies the same native ordinal bottom. -/
local instance comparisonCoefficientBottom : OrderBot c.cardinal.ord.ToType := c.bottom
local instance comparisonCoefficientPresentable : IsCardinalLocallyPresentable C c.cardinal :=
  c.locallyPresentable

/-- The whole first diagram functor retains the actual common-rank native I algorithm. -/
theorem cofibrantWholeFactorization_eq_native :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    (c.cofibrantFactorizationData s).originalFactorizationFunctor =
      g.generationData.cofibrantFactorizationData.originalFactorizationFunctor := rfl

/-- The whole second diagram functor retains the same produced rank and native J algorithm. -/
theorem fibrantWholeFactorization_eq_native :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    (c.fibrantFactorizationData s).originalFactorizationFunctor =
      g.generationData.fibrantFactorizationData.originalFactorizationFunctor := rfl

/-- The full original injective I algorithm returns through the actual selected index unit. -/
def cofibrantWholeRoundtripIso :
    (((c.cofibrantFactorizationData s).ofEquivalence
      (s.equivalence.congrLeft (E := C)).symm).ofEquivalence
        (s.equivalence.congrLeft (E := C))).originalFactorizationFunctor ≅
      (c.cofibrantFactorizationData s).originalFactorizationFunctor :=
  (c.cofibrantFactorizationData s).originalWholeFactorizationRoundtripIso
    (s.equivalence.congrLeft (E := C))

/-- The same actual unit returns both entire original injective J factors at their produced rank. -/
def fibrantWholeRoundtripIso :
    (((c.fibrantFactorizationData s).ofEquivalence
      (s.equivalence.congrLeft (E := C)).symm).ofEquivalence
        (s.equivalence.congrLeft (E := C))).originalFactorizationFunctor ≅
      (c.fibrantFactorizationData s).originalFactorizationFunctor :=
  (c.fibrantFactorizationData s).originalWholeFactorizationRoundtripIso
    (s.equivalence.congrLeft (E := C))

/-- The caller's initial arrows and original first algorithm construct the entire Q functor. -/
def cofibrantReplacement (Z : D ⥤ C) (hZ : IsInitial Z) : (D ⥤ C) ⥤ (D ⥤ C) :=
  initialReplacement (c.cofibrantFactorizationData s) Z hZ

/-- Q's full counit is the actual original I projection. -/
def cofibrantReplacementCounit (Z : D ⥤ C) (hZ : IsInitial Z) :
    c.cofibrantReplacement s Z hZ ⟶ 𝟭 (D ⥤ C) :=
  initialProjection (c.cofibrantFactorizationData s) Z hZ

/-- The original initial leg retains the whole first natural factor transformation. -/
def initialToCofibrantReplacement (Z : D ⥤ C) (hZ : IsInitial Z) :
    (Functor.const (D ⥤ C)).obj Z ⟶ c.cofibrantReplacement s Z hZ :=
  initialLeg (c.cofibrantFactorizationData s) Z hZ

/-- The original terminal-arrow family and second algorithm construct the whole R functor. -/
def fibrantReplacement (Z : D ⥤ C) (hZ : IsTerminal Z) : (D ⥤ C) ⥤ (D ⥤ C) :=
  terminalReplacement (c.fibrantFactorizationData s) Z hZ

/-- R's full original unit is the same native J inclusion. -/
def fibrantReplacementUnit (Z : D ⥤ C) (hZ : IsTerminal Z) :
    𝟭 (D ⥤ C) ⟶ c.fibrantReplacement s Z hZ :=
  terminalUnit (c.fibrantFactorizationData s) Z hZ

/-- The original terminal leg is the full second projection from that same factor record. -/
def fibrantReplacementToTerminal (Z : D ⥤ C) (hZ : IsTerminal Z) :
    c.fibrantReplacement s Z hZ ⟶ (Functor.const (D ⥤ C)).obj Z :=
  terminalLeg (c.fibrantFactorizationData s) Z hZ

/-- Reclassification preserves the entire Q functor at the actual produced common rank. -/
theorem cofibrantReplacement_eq_native (Z : D ⥤ C) (hZ : IsInitial Z) :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    c.cofibrantReplacement s Z hZ =
      initialReplacement g.generationData.cofibrantFactorizationData Z hZ := rfl

/-- Reclassification retains the entire original R functor and every original terminal square. -/
theorem fibrantReplacement_eq_native (Z : D ⥤ C) (hZ : IsTerminal Z) :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    c.fibrantReplacement s Z hZ =
      terminalReplacement g.generationData.fibrantFactorizationData Z hZ := rfl

/-- The whole original Q counit transformation is the actual native common-rank projection. -/
def cofibrantReplacementNativeIso (Z : D ⥤ C) (hZ : IsInitial Z) :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    c.cofibrantReplacement s Z hZ ≅
      initialReplacement g.generationData.cofibrantFactorizationData Z hZ := by
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The entire original second algorithm supplies the native R functor comparison. -/
def fibrantReplacementNativeIso (Z : D ⥤ C) (hZ : IsTerminal Z) :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    c.fibrantReplacement s Z hZ ≅
      terminalReplacement g.generationData.fibrantFactorizationData Z hZ := by
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The whole Q counit is preserved through the genuine native replacement functor comparison. -/
theorem cofibrantReplacementCounit_eq_native (Z : D ⥤ C) (hZ : IsInitial Z) :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    (c.cofibrantReplacementNativeIso s Z hZ).hom ≫
        initialProjection g.generationData.cofibrantFactorizationData Z hZ =
      c.cofibrantReplacementCounit s Z hZ := by
  ext X
  exact Category.id_comp _

/-- The entire original R unit retains its native value through that same whole functor iso. -/
theorem fibrantReplacementUnit_eq_native (Z : D ⥤ C) (hZ : IsTerminal Z) :
    let g := c.generationAndFactors s
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    c.fibrantReplacementUnit s Z hZ ≫ (c.fibrantReplacementNativeIso s Z hZ).hom =
      terminalUnit g.generationData.fibrantFactorizationData Z hZ := by
  ext X
  exact Category.comp_id _

/-- Q retains its complete original middle functor on all given initial arrows. -/
theorem cofibrantReplacement_original_functor (Z : D ⥤ C) (hZ : IsInitial Z) :
    c.cofibrantReplacement s Z hZ = initialArrows Z hZ ⋙ (c.cofibrantFactorizationData s).Z :=
  rfl

/-- R retains the entire original middle functor on the caller's terminal arrows. -/
theorem fibrantReplacement_original_functor (Z : D ⥤ C) (hZ : IsTerminal Z) :
    c.fibrantReplacement s Z hZ = terminalArrows Z hZ ⋙ (c.fibrantFactorizationData s).Z :=
  rfl

/-- Every Q map retains the original initial endpoint identity and native middle square. -/
theorem cofibrantReplacement_original_map (Z : D ⥤ C) (hZ : IsInitial Z)
    {X Y : D ⥤ C} (f : X ⟶ Y) :
    (c.cofibrantReplacement s Z hZ).map f =
      (c.cofibrantFactorizationData s).Z.map (Arrow.homMk (𝟙 Z) f (hZ.hom_ext _ _)) := rfl

/-- Every R map retains the native full terminal square and its original identity endpoint. -/
theorem fibrantReplacement_original_map (Z : D ⥤ C) (hZ : IsTerminal Z)
    {X Y : D ⥤ C} (f : X ⟶ Y) :
    (c.fibrantReplacement s Z hZ).map f =
      (c.fibrantFactorizationData s).Z.map (Arrow.homMk f (𝟙 Z) (hZ.hom_ext _ _)) := rfl

/-- Both original Q legs recover the complete original initial-map transformation. -/
theorem cofibrantReplacement_fac (Z : D ⥤ C) (hZ : IsInitial Z) :
    c.initialToCofibrantReplacement s Z hZ ≫ c.cofibrantReplacementCounit s Z hZ =
      initialMapNatTrans Z hZ := initial_fac (c.cofibrantFactorizationData s) Z hZ

/-- Both original R legs retain the same entire original terminal-map transformation. -/
theorem fibrantReplacement_fac (Z : D ⥤ C) (hZ : IsTerminal Z) :
    c.fibrantReplacementUnit s Z hZ ≫ c.fibrantReplacementToTerminal s Z hZ =
      terminalMapNatTrans Z hZ := terminal_fac (c.fibrantFactorizationData s) Z hZ

/-- The original Q inclusion and projection belong to the actual constructed injective classes. -/
theorem cofibrantReplacement_classes (Z : D ⥤ C) (hZ : IsInitial Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    cofibrations (D ⥤ C) ((c.initialToCofibrantReplacement s Z hZ).app X) ∧
      trivialFibrations (D ⥤ C) ((c.cofibrantReplacementCounit s Z hZ).app X) := by
  let : ModelCategory (D ⥤ C) := c.modelCategory s
  constructor
  · rw [(c.fiveClasses s).2.1]
    exact (c.cofibrantFactorizationData s).hi _
  · rw [(c.fiveClasses s).2.2.2.2]
    exact (c.cofibrantFactorizationData s).hp _

/-- Both original R legs retain the constructed trivial-cofibration and fibration classes. -/
theorem fibrantReplacement_classes (Z : D ⥤ C) (hZ : IsTerminal Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    trivialCofibrations (D ⥤ C) ((c.fibrantReplacementUnit s Z hZ).app X) ∧
      fibrations (D ⥤ C) ((c.fibrantReplacementToTerminal s Z hZ).app X) := by
  let : ModelCategory (D ⥤ C) := c.modelCategory s
  constructor
  · rw [(c.fiveClasses s).2.2.1]
    exact (c.fibrantFactorizationData s).hi _
  · rw [(c.fiveClasses s).2.2.2.1]
    exact (c.fibrantFactorizationData s).hp _

/-- Every actual Q object is cofibrant through its retained original initial leg. -/
theorem cofibrantReplacement_isCofibrant (Z : D ⥤ C) (hZ : IsInitial Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    IsCofibrant ((c.cofibrantReplacement s Z hZ).obj X) := by
  let : ModelCategory (D ⥤ C) := c.modelCategory s
  apply (isCofibrant_iff_of_isInitial ((c.initialToCofibrantReplacement s Z hZ).app X) hZ).2
  exact (cofibration_iff _).2 (c.cofibrantReplacement_classes s Z hZ X).1

/-- Every actual R object is fibrant using the original terminal factor projection. -/
theorem fibrantReplacement_isFibrant (Z : D ⥤ C) (hZ : IsTerminal Z) (X : D ⥤ C) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    IsFibrant ((c.fibrantReplacement s Z hZ).obj X) := by
  let : ModelCategory (D ⥤ C) := c.modelCategory s
  apply (isFibrant_iff_of_isTerminal ((c.fibrantReplacementToTerminal s Z hZ).app X) hZ).2
  exact (fibration_iff _).2 (c.fibrantReplacement_classes s Z hZ X).2

end HomotopicalAlgebra.FunctorInjective.SourceConstruction.CoefficientData
