/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.IntegerDGRestriction
public import MathlibExt.CategoryTheory.DGSourceMore.DGSimplicial
public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Actual scalar-changing maps of DG coherent nerves

Transport of an enriched functor applies the actual lax monoidal
functor to every Hom map. The DG-to-simplicial construction retains
the native double-opposite Alexander--Whitney convention. Nerve maps
are actual postcomposition of every coherent simplex.

Integer restriction provides these maps between different coefficient
rings without forgetting the native DG-module values or actions.
References: Lurie, Higher Algebra, Construction 1.3.1.13;
Anschuetz--Mann, arXiv:2403.01951v2, Theorem 1.1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.CategoryTheory.DGScalarNerveMaps

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource IntegerDGRestriction SemilinearDGModuleRestrictions

universe u v w t

/-- The actual map of enriched Hom objects under a lax monoidal change of base. -/
def transportFunctor {V : Type u} {W : Type v}
    [Category V] [MonoidalCategory V] [Category W] [MonoidalCategory W]
    (U : V ⥤ W) [U.LaxMonoidal] {C D : Type w}
    [EnrichedCategory V C] [EnrichedCategory V D] (F : EnrichedFunctor V C D) :
    EnrichedFunctor W (TransportEnrichment U C) (TransportEnrichment U D) where
  obj X := F.obj X
  map X Y := U.map (F.map X Y)
  map_id X := by
    rw [TransportEnrichment.eId_eq U, TransportEnrichment.eId_eq U]
    rw [Category.assoc, ← U.map_comp, F.map_id]
  map_comp X Y Z := by
    rw [TransportEnrichment.eComp_eq U, TransportEnrichment.eComp_eq U]
    rw [Category.assoc, ← U.map_comp, F.map_comp, U.map_comp,
      ← Category.assoc, ← Functor.LaxMonoidal.μ_natural]
    exact Category.assoc _ _ _

/-- The actual simplicial enrichment map of a native DG functor. -/
def dgSimplicialFunctor {R : Type u} [CommRing R] {C D : Type w}
    [DGCategory R C] [DGCategory R D]
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) C D) :
    EnrichedFunctor SSet.{u} (DGSimplicialCategory R C) (DGSimplicialCategory R D) :=
  (transportFunctor (cochainToSSet R) F.op).op

/-- The same actual enrichment map on the underlying simplicial categories. -/
def onUnderlying {C D : Type w} [EnrichedCategory SSet.{u} C]
    [EnrichedCategory SSet.{u} D] (F : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} (ForgetEnrichment SSet.{u} C)
      (ForgetEnrichment SSet.{u} D) where
  obj X := F.obj X
  map X Y := F.map X Y
  map_id X := F.map_id X
  map_comp X Y Z := F.map_comp X Y Z

/-- Native postcomposition on every homotopy-coherent nerve simplex. -/
def nerveMap {C D : Type w} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) : SimplicialNerve C ⟶ SimplicialNerve D where
  app n := ↾fun a ↦ a.comp SSet.{u} F
  naturality n m g := by
    ext a
    exact EnrichedFunctor.ext SSet.{u} (fun _ ↦ rfl) (fun X Y ↦ by
      dsimp [EnrichedFunctor.comp]
      exact Category.assoc _ _ _)

/-- The actual integer-enriched coherent nerve of a geometric coefficient category. -/
def integerNerve {R : Type u} [CommRing R] (C : Type w) [DGCategory R C] :
    SSet.{max u w} :=
  SimplicialNerve (ForgetEnrichment SSet.{u} (DGSimplicialCategory Integers.{u}
    (IntegerDG R C)))

/-- The actual coherent nerve over a fixed source coefficient ring. -/
def coherentNerve {R : Type u} [CommRing R] (C : Type w) [DGCategory R C] :
    SSet.{max u w} :=
  SimplicialNerve (ForgetEnrichment SSet.{u} (DGSimplicialCategory R C))

/-- Every simplex of this comparison is actual DG-functor postcomposition. -/
def dgNerveMap {R : Type u} [CommRing R] {C D : Type w}
    [DGCategory R C] [DGCategory R D]
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) C D) :
    coherentNerve (R := R) C ⟶ coherentNerve (R := R) D :=
  nerveMap (onUnderlying (dgSimplicialFunctor F))

/-- The actual nerve map of the prescribed scalar-changing DG functor. -/
def scalarNerveMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {C D : Type w} [DGCategory R C] [DGCategory S D]
    (F : SemilinearFunctor φ C D) :
    integerNerve (R := R) C ⟶ integerNerve (R := S) D :=
  nerveMap (onUnderlying (dgSimplicialFunctor (integerFunctor φ F)))

end MathlibExt.CategoryTheory.DGScalarNerveMaps
