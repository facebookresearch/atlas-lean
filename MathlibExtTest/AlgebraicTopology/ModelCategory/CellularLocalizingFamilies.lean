/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizingFamilies
import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen
open HomotopicalAlgebra.CellularLocalizingFamilies
open HomotopicalAlgebra.GeneratedFunctorialReplacements

section OriginalGeneratedArrows

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

example (p : Arrow C) : ((cellApproximation d).obj p).left = (Q d).obj p.left :=
  cellApproximation_left d p

example (p : Arrow C) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      ((cellApproximation d).obj p).hom := cellComplex d p

example {p q : Arrow C} (φ : p ⟶ q) :
    ((cellApproximation d).map φ).left = (Q d).map φ.left := cellApproximation_map_left d φ

example {p q : Arrow C} (φ : p ⟶ q) :
    ((cellApproximation d).map φ).left ≫ ((cellApproximation d).obj q).hom =
      ((cellApproximation d).obj p).hom ≫ ((cellApproximation d).map φ).right :=
  ((cellApproximation d).map φ).w

example {p q : Arrow C} (φ : p ⟶ q) :
    (cellApproximation d).map φ ≫ (toOriginal d).app q = (toOriginal d).app p ≫ φ :=
  (toOriginal d).naturality φ

example (p : Arrow C) : ((toOriginal d).app p).left = (counit d).app p.left :=
  toOriginal_left d p

example (p : Arrow C) :
    ((toOriginal d).app p).left ≫ p.hom =
      ((cellApproximation d).obj p).hom ≫ ((toOriginal d).app p).right := toOriginal_square d p

example (p : Arrow C) :
    trivialFibrations C ((toOriginal d).app p).left ∧
      trivialFibrations C ((toOriginal d).app p).right :=
  ⟨toOriginal_left_trivialFibration d p, toOriginal_right_trivialFibration d p⟩

example (p : Arrow C) :
    IsCofibrant ((cellApproximation d).obj p).left ∧
      IsCofibrant ((cellApproximation d).obj p).right :=
  ⟨cellApproximation_source_cofibrant d p, cellApproximation_target_cofibrant d p⟩

example (p : Arrow C) :
    (cosimplicialFactor d p).i ≫ targetResolution d p =
      sourceResolution d p ≫ (CosimplicialObject.const C).map ((Q d).map p.hom) :=
  resolution_square d p

example (p : Arrow C) (j : SimplexCategory) :
    weakEquivalences C ((sourceResolution d p).app j) ∧
      weakEquivalences C ((targetResolution d p).app j) :=
  ⟨sourceResolution_weak d p j, targetResolution_weak d p j⟩

example (p : Arrow C) (n : ℕ) :
    cofibrations C (latchingArrow d p n).hom ∧
      IsCofibrant (latchingArrow d p n).left ∧ IsCofibrant (latchingArrow d p n).right :=
  ⟨latchingArrow_cofibration d p n, latchingArrow_source_cofibrant d p n,
    latchingArrow_target_cofibrant d p n⟩

example {p q : Arrow C} (φ : p ⟶ q) (n : ℕ) :
    ((latchingFamilyFunctor d n).map φ).left =
      SimplexCategory.reedy.latchingCornerSourceMap
        ((cosimplicialApproximation d).map φ) ⦋n⦌ :=
  latchingFamilyFunctor_map_left d φ n

example {p q : Arrow C} (φ : p ⟶ q) (n : ℕ) :
    ((latchingFamilyFunctor d n).map φ).left ≫ (latchingArrow d q n).hom =
      (latchingArrow d p n).hom ≫ ((latchingFamilyFunctor d n).map φ).right :=
  ((latchingFamilyFunctor d n).map φ).w

example (p : Arrow C) (Z : C) [IsFibrant Z] :
    WeakEquivalence (ResolutionHomComplex.precomp (cosimplicialFactor d p).i
      ((SimplicialObject.const C).obj Z)) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d p.hom Z) :=
  resolutionPrecomp_weak_iff d p Z

example (p : Arrow C) {j k : SimplexCategory} (a : j ⟶ k) :
    weakEquivalences C (((GeneratedFramings.leftFrame d).obj p.left).map a) ∧
      weakEquivalences C ((cosimplicialFactor d p).Z.map a) :=
  ⟨sourceResolution_map_weak d p a, targetResolution_map_weak d p a⟩

example (p : Arrow C) : ((originalCellFactor d).obj p).left = p.left :=
  originalCellFactor_source d p

example (p : Arrow C) (hp : cofibrations C p.hom) :
    RetractArrow p.hom ((originalCellFactor d).obj p).hom :=
  originalCellFactorRetract d p hp

example {p q : Arrow C} (φ : p ⟶ q) :
    (originalCellFactor d).map φ ≫ (originalCellProjection d).app q =
      (originalCellProjection d).app p ≫ φ := (originalCellProjection d).naturality φ

variable {K : Type wS} (S : K → Arrow C)

example (Z : C) : generatedLocalFibrant d (approximatedFamily d S) Z ↔ generatedLocalFibrant d S Z :=
  localFibrant_iff d S Z

example : generatedLocalEquivalences d (approximatedFamily d S) = generatedLocalEquivalences d S :=
  localEquivalences_eq d S

example (k : K) : generatedLocalEquivalences d S (approximatedFamily d S k).hom :=
  approximatedFamily_local d S k

end OriginalGeneratedArrows

section OriginalCellularFactories

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} [Small.{w} K]
  (S : K → Arrow C) (h : CellularSource d)

example (Z : C) (hZ : generatedLocalFibrant d S Z) (j : SimplexCategoryᵒᵖ) :
    generatedLocalFibrant d S (((GeneratedFramings.rightFrame d).obj Z).obj j) :=
  rightFrame_coefficient_localFibrant d S Z hZ j

example (k : K) (Z : C) (hZ : generatedLocalFibrant d S Z) (j : SimplexCategoryᵒᵖ) :
    WeakEquivalence (ResolutionHomComplex.precomp (cosimplicialFactor d (S k)).i
      ((SimplicialObject.const C).obj (((GeneratedFramings.rightFrame d).obj Z).obj j))) :=
  resolutionPrecomp_frameCoefficient_local_weak d S k Z hZ j

example (j : d.J.toSet) : (attachingFamily d S (Sum.inl j)).left = j.1.left :=
  attachingFamily_J_source d S j

example (a : d.J.toSet ⊕ (K × ℕ)) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      (attachingFamily d S a).hom := attachingFamilyComplex d S a

example : (attachingClass d S).rlp ≤ fibrations C := attachingRLP_le_fibrations d S

example : d.J ≤ (attachingClass d S).retracts := original_J_le_attaching_retracts d S

example (a : d.J.toSet ⊕ (K × ℕ)) :
    IsUniformlySmallRelativeTo.{w} d.I (attachingFamily d S a).left :=
  attachingFamily_source_small d S h a

example (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonAttachingSourceBound d S h < μ) :
    (attachingClass d S).IsCardinalForSmallObjectArgument μ :=
  attachingIsCardinalForSmallObjectArgument d S h μ hμ

example : (attachingRank d S h).IsRegular := attachingRank_regular d S h

example : FunctorialFactorizationData (attachingClass d S).rlp.llp (attachingClass d S).rlp :=
  hornFactorizationData d S h

example {p q : Arrow C} (φ : p ⟶ q) :
    φ.left ≫ (hornFactorizationData d S h).i.app q =
      (hornFactorizationData d S h).i.app p ≫ (hornFactorizationData d S h).Z.map φ :=
  (hornFactorizationData d S h).i.naturality φ

example {p q : Arrow C} (φ : p ⟶ q) :
    letI : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
    letI : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
    letI : (attachingClass d S).IsCardinalForSmallObjectArgument (attachingRank d S h) :=
      attachingIsCardinalForSmallObjectArgument d S h _ (Order.lt_succ _)
    (hornFactorizationData d S h).Z.map φ =
      SmallObject.objMap (attachingClass d S) (attachingRank d S h) φ :=
  hornFactorizationData_map d S h φ

example {X Y : C} (f : X ⟶ Y) :
    f ≫ (hornUnit d S h).app Y = (hornUnit d S h).app X ≫ (hornObjectFunctor d S h).map f :=
  (hornUnit d S h).naturality f

example (X : C) :
    cofibrations C ((hornUnit d S h).app X) ∧ IsFibrant ((hornObjectFunctor d S h).obj X) :=
  ⟨hornUnit_cofibration d S h X, hornObject_isFibrant d S h X⟩

example (X : C) : (attachingClass d S).rlp (hornProjection d S h X) :=
  hornProjection_rlp d S h X

example (X : C) :
    letI : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
    letI : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
    RelativeCellComplex.{w}
      (fun _ : (attachingRank d S h).ord.ToType => (attachingClass d S).homFamily)
      ((hornUnit d S h).app X) := hornUnitComplex d S h X

end OriginalCellularFactories

#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cellApproximation
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.toOriginal
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.toOriginal_square
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cellComplex
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cellApproximation_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cellApproximation_source_cofibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cellApproximation_target_cofibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.toOriginal_left_trivialFibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.toOriginal_right_trivialFibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.nativePrecomp_iff
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.derivedLocal_iff
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.localFibrant_iff
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.localEquivalences_eq
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.approximatedFamily_local
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cosimplicialFactor
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.sourceResolution
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.targetResolution
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.resolution_square
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.sourceResolution_weak
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.targetResolution_weak
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingArrow
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingArrow_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.sourceResolution_cofibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.targetResolution_latching_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.targetResolution_cofibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingArrow_source_cofibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingArrow_target_cofibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.cosimplicialApproximation
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingFamilyFunctor
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingFamilyFunctor_obj
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingFamilyFunctor_map_left
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.latchingFamilyFunctor_map_right
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.resolutionPrecomp_weak_iff
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.rightFrame_coefficient_localFibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.resolutionPrecomp_local_weak
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.resolutionPrecomp_frameCoefficient_local_weak
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.sourceResolution_map_weak
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.targetResolution_map_weak
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellFactor
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellProjection
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellFactor_source
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellFactorComplex
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellFactor_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellProjection_trivialFibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellFactorRetract
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.original_J_trivialCofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.originalCellFactor_J_trivialCofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingFamily
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingFamily_J_source
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingFamilyComplex
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingFamily_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingClass
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingClass_le_cofibrations
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingLeftClass_le_cofibrations
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.original_J_le_attaching_retracts
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingRLP_le_fibrations
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingFamily_source_small
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingFamily_cofibration_small
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingSourceBound
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.commonAttachingSourceBound
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingSourceBound_le_common
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingIsCardinalForSmallObjectArgument
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingRank
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingRank_regular
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.attachingRankOrderBot
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornFactorizationData
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornFactorizationData_map
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.terminalArrowFunctor
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornObjectFunctor
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornUnit
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornProjection
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornUnit_projection
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornUnit_cofibration
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornProjection_rlp
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornObject_isFibrant
#print axioms HomotopicalAlgebra.CellularLocalizingFamilies.hornUnitComplex
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizingFamilies
