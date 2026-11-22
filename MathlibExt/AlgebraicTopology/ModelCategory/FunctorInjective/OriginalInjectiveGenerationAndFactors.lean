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

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial

/-!
# Original injective generation and native factors at one constructed rank

The original coefficient model and actual ordinary index construct the Smith
model and its original I/J families. Actual source endpoint bounds then produce
one common enlarged regular rank, small-object eligibility for those same
families and their two native functorial factors. Every original Arrow map,
middle functor, factor leg and model-class law is retained at that rank.

The source is Jacob Lurie's *Higher Topos Theory*, author PDF dated April 9,
2017, A.2.8.2–3 (printed page 830/PDF page 848), with the original ordinary
injective generation proof A.3.3.3/A.3.3.16–17 (printed pages 878–884).
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

section OriginalConstruction

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)

/-- Actual source uniformization for the two families constructed on the original category.
Its factor methods below use this cardinal and these same families. -/
structure OriginalInjectiveGenerationAndFactorsData where
  /-- The common rank constructed from the actual two source families. -/
  cardinal : Cardinal.{w}
  regular : Fact cardinal.IsRegular
  /-- The chosen initial stage of the regular cardinal's native small-object iteration. -/
  bottom : OrderBot cardinal.ord.ToType
  coefficient_lt : kappa < cardinal
  localPresentability_lt : kappaLP < cardinal
  profile_lt : (boundedConstruction d kappaLP s).cardinal < cardinal
  locallyPresentable : IsCardinalLocallyPresentable (D ⥤ C) cardinal
  sourceI : ∀ i : (boundedConstruction d kappaLP s).family.generators.toSet,
    IsCardinalPresentable i.1.left cardinal
  sourceJ : ∀ j : (originalSmithData d kappaLP s).J.toSet,
    IsCardinalPresentable j.1.left cardinal
  I_smallObject :
    letI : Fact cardinal.IsRegular := regular
    letI : OrderBot cardinal.ord.ToType := bottom
    (boundedConstruction d kappaLP s).family.generators.IsCardinalForSmallObjectArgument
      cardinal
  J_smallObject :
    letI : Fact cardinal.IsRegular := regular
    letI : OrderBot cardinal.ord.ToType := bottom
    (originalSmithData d kappaLP s).J.IsCardinalForSmallObjectArgument cardinal

/-- Construct a single enlarged rank from the original coefficient, compact profile and Smith
source families. Neither a target model nor a target factorization is supplied. -/
def originalInjectiveGenerationAndFactors :
    OriginalInjectiveGenerationAndFactorsData d kappaLP s := by
  apply Classical.choice
  let b := boundedConstruction d kappaLP s
  let M := originalSmithData d kappaLP s
  let : IsCardinalLocallyPresentable (D ⥤ C) kappaLP := s.isCardinalLocallyPresentable kappaLP
  let : b.family.generators.HasSmallObjectArgument.{w} := b.hasSmallObjectArgument
  let : M.J.HasSmallObjectArgument.{w} := M.J_smallObject
  let Fixed := kappa.ord.ToType ⊕ b.cardinal.ord.ToType
  obtain ⟨rho, hreg, hbot, hLP, hFixed, hPresentable, hSourceI, hSourceJ, hI, hJ⟩ :=
    HomotopicalAlgebra.exists_common_generation_cardinal_from_sources kappaLP
      b.family.generators M.J Fixed
  have hKappa : kappa < rho := by
    have h := hFixed.of_injective (Sum.inl : kappa.ord.ToType → Fixed) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hProfile : b.cardinal < rho := by
    have h := hFixed.of_injective (Sum.inr : b.cardinal.ord.ToType → Fixed) Sum.inr_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  exact ⟨
    { cardinal := rho
      regular := hreg
      bottom := hbot
      coefficient_lt := hKappa
      localPresentability_lt := hLP
      profile_lt := hProfile
      locallyPresentable := hPresentable
      sourceI := hSourceI
      sourceJ := hSourceJ
      I_smallObject := hI
      J_smallObject := hJ }⟩

namespace OriginalInjectiveGenerationAndFactorsData

variable {d kappaLP s} (g : OriginalInjectiveGenerationAndFactorsData d kappaLP s)

/-- The same selected ordinary index retains its full original Arrow bound at the new rank. -/
theorem selectedIndexArrows : HasCardinalLT (Arrow s.index) g.cardinal :=
  (boundedConstruction d kappaLP s).profile.arrows.of_le g.profile_lt.le

/-- The two original families give genuine generation data for the constructed model at the
one chosen rank. The right-class laws are the actual Smith laws, not caller hypotheses. -/
def generationData :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    CofibrantGenerationData (D ⥤ C) g.cardinal := by
  letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  letI : Fact g.cardinal.IsRegular := g.regular
  letI : OrderBot g.cardinal.ord.ToType := g.bottom
  exact
    { I := (boundedConstruction d kappaLP s).family.generators
      J := (originalSmithData d kappaLP s).J
      I_smallObject := g.I_smallObject
      J_smallObject := g.J_smallObject
      I_rlp := (originalSmithModel_trivialFibrations d kappaLP s).symm
      J_rlp := rfl }

/-- The first family is literally the internally chosen original compact diagram family. -/
theorem generationData_I :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    g.generationData.I = (boundedConstruction d kappaLP s).family.generators := rfl

/-- The second family is literally the internally produced Smith family. -/
theorem generationData_J :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    g.generationData.J = (originalSmithData d kappaLP s).J := rfl

section OriginalClasses

local instance generationRegular : Fact g.cardinal.IsRegular := g.regular
/-- The native iteration retains the bottom returned by the actual rank constructor. -/
local instance generationBottom : OrderBot g.cardinal.ord.ToType := g.bottom

/-- The generated right classes are the exact original injective lifting classes. -/
theorem generationData_rightClasses :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    g.generationData.I.rlp = ((cofibrations C).functorCategory D).rlp ∧
      g.generationData.J.rlp = ((trivialCofibrations C).functorCategory D).rlp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  exact
    ⟨g.generationData.I_rlp.trans (originalInjectiveModel_trivialFibrations d kappaLP s),
      g.generationData.J_rlp.trans (originalInjectiveModel_fibrations d kappaLP s)⟩

/-- The actual first factors lie in the original objectwise cofibrations and their full
right lifting class. No model class is supplied as a premise. -/
theorem cofibrantFactorizationData_mem (f : Arrow (D ⥤ C)) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    (cofibrations C).functorCategory D (g.generationData.cofibrantFactorizationData.i.app f) ∧
      ((cofibrations C).functorCategory D).rlp
        (g.generationData.cofibrantFactorizationData.p.app f) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  constructor
  · rw [← originalInjectiveModel_cofibrations d kappaLP s]
    exact g.generationData.cofibrantFactorizationData.hi f
  · rw [← originalInjectiveModel_trivialFibrations d kappaLP s]
    exact g.generationData.cofibrantFactorizationData.hp f

/-- The actual second factors lie in the original objectwise trivial cofibrations and
their full right lifting class. -/
theorem fibrantFactorizationData_mem (f : Arrow (D ⥤ C)) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    (trivialCofibrations C).functorCategory D
        (g.generationData.fibrantFactorizationData.i.app f) ∧
      ((trivialCofibrations C).functorCategory D).rlp
        (g.generationData.fibrantFactorizationData.p.app f) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  constructor
  · rw [← originalInjectiveModel_trivialCofibrations d kappaLP s]
    exact g.generationData.fibrantFactorizationData.hi f
  · rw [← originalInjectiveModel_fibrations d kappaLP s]
    exact g.generationData.fibrantFactorizationData.hp f

end OriginalClasses

end OriginalInjectiveGenerationAndFactorsData

end OriginalConstruction

end HomotopicalAlgebra.FunctorInjective
