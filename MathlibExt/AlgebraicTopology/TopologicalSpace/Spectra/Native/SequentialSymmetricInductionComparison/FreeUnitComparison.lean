/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.FreeComparison

/-!
# Free-object units for sequential-to-symmetric induction

The enriched left Kan extension/restriction adjunction is compared with free objects
through its unit characteristic. For the sequential-to-symmetric index functor, the
induction unit and free comparison recover the coefficient-tensored index Hom map at
every degree, coefficient and component.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj


namespace CategoryTheory.EnrichedFunctorCat.FreeUnitComparison
universe uV vV uA uB
open EnrichedFunctorCat
variable {Bv : Type uV} [Category.{vV} Bv] [MonoidalCategory Bv]
  [BraidedCategory Bv] [MonoidalClosed Bv]
  {A : Type uA} [EnrichedCategory Bv A] {B : Type uB} [EnrichedCategory Bv B]
  (j : EnrichedFunctor Bv A B)
  [∀ (F : EnrichedFunctorCat Bv A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat Bv A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat Bv A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]

/-- The actual native Kan/free comparison has its complete original restricted-unit characteristic. -/
private theorem restrictionUnit_characteristic (a : A) (X : Bv) :
    (leftKanRestrictionAdjunction j).unit.app ((Free.functor a).obj X) ≫
      (restriction j).map (((LeftKanFreeComparison.FullMapFamilies.data j).comparison a).hom.app X) =
      FreeHomTransport.map j a X := by
  have hU := leftKanRestrictionAdjunction_unit j ((Free.functor a).obj X)
  have hM := (LeftKanFreeComparison.FullMapFamilies.data j).homEquation a X
  exact (congrArg (fun q => q ≫ (restriction j).map
      (((LeftKanFreeComparison.FullMapFamilies.data j).comparison a).hom.app X)) hU).trans
    ((congrArg (fun q => leftKanUnit j (Free.object a X) ≫ (restriction j).map q) hM).trans
      (LeftKanFreeComparison.hom_unit j a X))

end CategoryTheory.EnrichedFunctorCat.FreeUnitComparison

namespace CategoryTheory.EnrichedFunctorCat.FreeUnitComparison
universe uV vV uA uB
open EnrichedFunctorCat
variable {Bv : Type uV} [Category.{vV} Bv] [MonoidalCategory Bv]
  [BraidedCategory Bv] [MonoidalClosed Bv]
  {A : Type uA} [EnrichedCategory Bv A] {B : Type uB} [EnrichedCategory Bv B]
  (j : EnrichedFunctor Bv A B)

/-- The actual ordinary components of any complete restricted map triple compose at every index. -/
private theorem triple_component {F G : EnrichedFunctorCat Bv A} {H I : EnrichedFunctorCat Bv B}
    (p : F ⟶ G) (q : G ⟶ restrictionObject j H) (r : H ⟶ I) (c : A) :
    component (p ≫ q ≫ restrictionMap j r) c =
      component p c ≫ component q c ≫ component r (j.obj c) := by
  rw [component_comp, component_comp, restrictionMap_component]
  rfl

/-- Identity-slot evaluation of the actual complete unit characteristic retrieves the full target free unit. -/
private theorem generator_unit_of_map_eq (a : A) (X : Bv)
    (t : Free.object a X ⟶ restrictionObject j (Free.object (j.obj a) X))
    (h : t = FreeHomTransport.map j a X) :
    (Free.adjunction a).unit.app X ≫ component t a =
      (Free.adjunction (j.obj a)).unit.app X :=
  (congrArg (fun q => (Free.adjunction a).unit.app X ≫ component q a) h).trans
    (FreeHomTransport.unit_map j a X)

/-- Taking a component of the entire actual characteristic retains the complete original coefficient map. -/
private theorem component_of_map_eq (a : A) (X : Bv)
    (t : Free.object a X ⟶ restrictionObject j (Free.object (j.obj a) X))
    (h : t = FreeHomTransport.map j a X) (c : A) :
    component t c = X ◁ j.map a c :=
  (congrArg (fun q => component q c) h).trans (FreeHomTransport.map_component j a X c)

/-- The complete characteristic gives every original component with the actual full coefficient Hom map. -/
private theorem components_of_map_eq (a : A) (X : Bv)
    {F : EnrichedFunctorCat Bv A} {G : EnrichedFunctorCat Bv B}
    (p : Free.object a X ⟶ F) (q : F ⟶ restrictionObject j G)
    (r : G ⟶ Free.object (j.obj a) X)
    (h : p ≫ q ≫ restrictionMap j r = FreeHomTransport.map j a X) (c : A) :
    component p c ≫ component q c ≫ component r (j.obj c) = X ◁ j.map a c := by
  have hc := congrArg (fun t => component t c) h
  rw [component_comp, component_comp, restrictionMap_component, FreeHomTransport.map_component] at hc
  exact hc

end CategoryTheory.EnrichedFunctorCat.FreeUnitComparison


namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CategoryTheory.EnrichedFunctorCat.FreeUnitComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The entire actual original induction unit gives the full native free Hom map at every index and coefficient. -/
theorem nativeFreeUnit_characteristic
    (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).hom.app K) =
      EnrichedFunctorCat.FreeHomTransport.map sequentialSymmetricOperatorIndexFunctor n K := by
  have hV := congrArg (fun q : EnrichedFunctorCat.Free.functor n ⋙ V.{u, v} ≅
      EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj n) =>
    VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map (q.hom.app K))
    (nativeFreeComparison_eq n)
  exact hV.trans
    ((CategoryTheory.Adjunction.RightIsoComparison.unit_postcompose VWAdjunction.{u, v}
      NativeIndexKanComposition.sequentialSymmetricAdjunction.{u, v}
      nativeRestrictionComparison.{u, v} ((EnrichedFunctorCat.Free.functor n).obj K)
      ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)
      ((NativeIndexKanComposition.sequentialSymmetricFreeData.comparison n).hom.app K)).trans
        (restrictionUnit_characteristic sequentialSymmetricOperatorIndexFunctor.{u, v} n K))

/-- The actual whole inverse free comparison retrieves the complete original induction unit. -/
theorem nativeFreeUnit_inverse
    (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) =
      EnrichedFunctorCat.FreeHomTransport.map sequentialSymmetricOperatorIndexFunctor n K ≫
        NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).inv.app K) :=
  CategoryTheory.Adjunction.RightIsoComparison.eq_comp_map_inv NativeIndexKanComposition.sequentialSymmetricRestriction
    ((nativeFreeComparison n).app K)
    (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)))
    (EnrichedFunctorCat.FreeHomTransport.map sequentialSymmetricOperatorIndexFunctor n K)
    ((Category.assoc _ _ _).trans (nativeFreeUnit_characteristic n K))

/-- Every component of the entire actual native unit diagram is the full original coefficient Hom map. -/
theorem nativeFreeUnit_map_component
    (n c : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    EnrichedFunctorCat.component (V := PointedCGWH.{u, v})
      (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
      (F := (EnrichedFunctorCat.Free.functor n).obj K)
      (G := NativeIndexKanComposition.sequentialSymmetricRestriction.obj
        ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K))
      (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
        nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
        NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).hom.app K)) c =
      K ◁ sequentialSymmetricOperatorIndexFunctor.map n c :=
  component_of_map_eq sequentialSymmetricOperatorIndexFunctor n K
    (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).hom.app K))
    (nativeFreeUnit_characteristic n K) c

/-- The actual unit retrieves the entire original free generator at every degree and coefficient. -/
theorem nativeFreeGenerator_unit
    (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    (EnrichedFunctorCat.Free.adjunction n).unit.app K ≫ EnrichedFunctorCat.component
      (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
        nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
        NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).hom.app K)) n =
      (EnrichedFunctorCat.Free.adjunction (sequentialSymmetricOperatorIndexFunctor.obj n)).unit.app K :=
  generator_unit_of_map_eq sequentialSymmetricOperatorIndexFunctor n K
    (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
      nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
      NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).hom.app K))
    (nativeFreeUnit_characteristic n K)

/-- The whole unit evaluation retains the actual original enriched identity and target free identity. -/
theorem nativeFreeGenerator_evaluation
    (n : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    EnrichedFunctorCat.Free.evaluate n K
      (NativeIndexKanComposition.sequentialSymmetricRestriction.obj
        ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K))
      (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K) ≫
        nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)) ≫
        NativeIndexKanComposition.sequentialSymmetricRestriction.map ((nativeFreeComparison n).hom.app K)) =
      EnrichedFunctorCat.Free.evaluate (sequentialSymmetricOperatorIndexFunctor.obj n) K
        ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)
        (𝟙 ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)) := by
  have hV := congrArg (fun q => EnrichedFunctorCat.Free.evaluate n K
    (NativeIndexKanComposition.sequentialSymmetricRestriction.obj
      ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)) q)
    (nativeFreeUnit_characteristic n K)
  have hE := EnrichedFunctorCat.FreeHomTransport.evaluate_map sequentialSymmetricOperatorIndexFunctor n K
    ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)
    (𝟙 ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K))
  have hi := NativeIndexKanComposition.sequentialSymmetricRestriction.map_id
    ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)
  have hE' := (congrArg (fun q => EnrichedFunctorCat.Free.evaluate n K
    (NativeIndexKanComposition.sequentialSymmetricRestriction.obj
      ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K))
    (EnrichedFunctorCat.FreeHomTransport.map sequentialSymmetricOperatorIndexFunctor n K ≫ q)) hi).trans
      (congrArg (fun q => EnrichedFunctorCat.Free.evaluate n K
        (NativeIndexKanComposition.sequentialSymmetricRestriction.obj
          ((EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)) q)
        (Category.comp_id _))
  exact hV.trans (hE'.symm.trans hE)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CategoryTheory.EnrichedFunctorCat.FreeUnitComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

open NativeIndexKanComposition EnrichedFunctorCat

/-- All native unit and comparison maps retain their original spectrum carriers,
their whole degree/coefficient families and their full characteristic. -/
structure NativeUnitMapData
    (G : Sequential.Index.{u, v} → PointedCGWH.{u, v} → SequentialCarrier.{u, v})
    (H : Sequential.Index.{u, v} → PointedCGWH.{u, v} → SymmetricCarrier.{u, v}) where
  /-- Every original unit map, before selecting any degree or coefficient. -/
  unitMap : ∀ (n : Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}),
    ((Free.functor n).obj K : SequentialCarrier.{u, v}) ⟶ G n K
  /-- The entire original restriction comparison at all source degrees and coefficients. -/
  rightComparison : ∀ (n : Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}),
    G n K ⟶ sequentialSymmetricRestriction.obj (H n K)
  /-- Every original free-comparison map with its complete native target. -/
  freeComparison : ∀ (n : Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}),
    H n K ⟶ ((Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K : SymmetricCarrier.{u, v})
  /-- The full actual unit characteristic at every original degree and coefficient. -/
  characteristic : ∀ (n : Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}),
    unitMap n K ≫ rightComparison n K ≫ sequentialSymmetricRestriction.map (freeComparison n K) =
      FreeHomTransport.map sequentialSymmetricOperatorIndexFunctor n K

/-- The existing generic three-map theorem applies to the complete native family. -/
theorem NativeUnitMapData.components
    {G : Sequential.Index.{u, v} → PointedCGWH.{u, v} → SequentialCarrier.{u, v}}
    {H : Sequential.Index.{u, v} → PointedCGWH.{u, v} → SymmetricCarrier.{u, v}}
    (d : NativeUnitMapData G H) (n c : Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    component (d.unitMap n K) c ≫ component (d.rightComparison n K) c ≫
      component (d.freeComparison n K) (sequentialSymmetricOperatorIndexFunctor.obj c) =
        K ◁ sequentialSymmetricOperatorIndexFunctor.map n c :=
  components_of_map_eq sequentialSymmetricOperatorIndexFunctor n K
    (d.unitMap n K) (d.rightComparison n K) (d.freeComparison n K) (d.characteristic n K) c

/-- Initialize the actual entire native family with all three original map functions. -/
def nativeFreeUnitMapData : NativeUnitMapData
    (fun n K => W.obj (V.obj ((Free.functor n).obj K)))
    (fun n K => V.obj ((Free.functor n).obj K)) where
  unitMap := fun n K => VWAdjunction.unit.app ((Free.functor n).obj K)
  rightComparison := fun n K => nativeRestrictionComparison.hom.app (V.obj ((Free.functor n).obj K))
  freeComparison := fun n K => (nativeFreeComparison n).hom.app K
  characteristic := nativeFreeUnit_characteristic.{u, v}

/-- Every original component of the actual induction unit retains its full coefficient-tensored Hom map. -/
theorem nativeFreeUnit_components
    (n c : PointedCGWH.Spectra.Sequential.Index.{u, v}) (K : PointedCGWH.{u, v}) :
    EnrichedFunctorCat.component (V := PointedCGWH.{u, v})
      (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
      (F := (EnrichedFunctorCat.Free.functor n).obj K)
      (G := W.obj (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)))
      (VWAdjunction.unit.app ((EnrichedFunctorCat.Free.functor n).obj K)) c ≫
      EnrichedFunctorCat.component (V := PointedCGWH.{u, v})
        (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
        (F := W.obj (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)))
        (G := NativeIndexKanComposition.sequentialSymmetricRestriction.obj
          (V.obj ((EnrichedFunctorCat.Free.functor n).obj K)))
        (nativeRestrictionComparison.hom.app (V.obj ((EnrichedFunctorCat.Free.functor n).obj K))) c ≫
      EnrichedFunctorCat.component (V := PointedCGWH.{u, v})
        (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        (F := V.obj ((EnrichedFunctorCat.Free.functor n).obj K))
        (G := (EnrichedFunctorCat.Free.functor (sequentialSymmetricOperatorIndexFunctor.obj n)).obj K)
        ((nativeFreeComparison n).hom.app K) (sequentialSymmetricOperatorIndexFunctor.obj c) =
          K ◁ sequentialSymmetricOperatorIndexFunctor.map n c :=
  NativeUnitMapData.components nativeFreeUnitMapData.{u, v} n c K

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
