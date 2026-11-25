/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
public import MathlibExt.AlgebraicTopology.NativeDiagramFamilies
public import MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps
public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels

/-!
# Native evaluation and the initial-index cocartesian section comparison

Evaluation is fixed by the actual full section inclusion and native
parameter evaluation at the original index vertex. Its fibre map is
normalized by that complete formula. An initial-index inverse is an
actual categorical inverse of this same evaluation map, preserving
all noninvertible parameter arrows.

Source: Lurie, *Higher Topos Theory*, Section 3.3.3;
Bhatt--Mathew1807.04725v4, the full categorical descent comparisons.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeInitialSectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels CategoricalCocartesianSections
open NativeDiagramFamilies StableInfinityMappingSpaceMaps SimplicialCovariantModels
open scoped Simplicial

universe u

/-- The native point of the prescribed base is the original value of q. -/
def baseVertex {B A : SSet.{u}} (q : A ⟶ B) (x : A _⦋0⦌) : B _⦋0⦌ := q.app (op ⦋0⦌) x

/-- The entire original section simplex is evaluated by the native internal-Hom map. -/
def sectionValue {E B A : SSet.{u}} (p : E ⟶ B) (q : A ⟶ B) (x : A _⦋0⦌) :
    sectionsOver p q ⟶ E :=
  (sectionSubcomplexOver p q).ι ≫ evaluateAt A E x

/-- The actual fibre evaluation is fixed by the complete native section formula. -/
structure SectionFibreEvaluation {E B A : SSet.{u}} (p : E ⟶ B) (q : A ⟶ B) (x : A _⦋0⦌) where
  map : sectionsOver p q ⟶ fibre p (baseVertex q x)
  normalization : map ≫ pullback.fst p (SSet.const (baseVertex q x) : Δ[0] ⟶ B) = sectionValue p q x

/-- The categorical inverse is normalized to the original evaluation on all higher parameters. -/
structure InitialSectionComparison {E B A : SSet.{u}} (p : E ⟶ B) (q : A ⟶ B) (x : A _⦋0⦌)
    extends SectionFibreEvaluation p q x where
  inverse : fibre p (baseVertex q x) ⟶ sectionsOver p q
  left_natural : NaturallyEquivalentMaps (inverse ≫ map) (𝟙 (fibre p (baseVertex q x)))
  right_natural : NaturallyEquivalentMaps (map ≫ inverse) (𝟙 (sectionsOver p q))
  weak : CategoricalWeakEquivalence map

end MathlibExt.AlgebraicTopology.NativeInitialSectionModels
