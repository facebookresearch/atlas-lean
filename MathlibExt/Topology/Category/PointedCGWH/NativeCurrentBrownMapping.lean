/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingZeroSource
public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentMappingSM7
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourceFunctor

/-!
# Mapping-space fibrations and Brown source invariance

For a fibrant target enriched diagram, precomposition by a projective cofibration gives
a mapping-space fibration, and a trivial cofibration gives a trivial fibration. Brown
factorization then gives weak invariance under weak equivalences between cofibrant
source diagrams.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.NativeCurrentBrownMapping

open PointedCGWH.EnrichedFunctorMapping
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private theorem zero_fibration (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsFibrant Y] :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (toZero Y) := by
  let _ : Fibration (toZero Y) :=
    (isFibrant_iff_of_isTerminal (toZero Y) (zeroDiagramIsTerminal (A := I))).mp inferInstance
  exact mem_fibrations _

/-- Original projective cofibrations give the actual source mapping fibration. -/
theorem source_fibration
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsFibrant Z] :
    fibrations PointedCGWH.{u, v}
      (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
        X.toEnrichedFunctor p) := by
  have h := HomotopicalAlgebra.EnrichedProjective.Native.CurrentMappingSM7.fibration
    p (toZero Z) hp (zero_fibration Z) (NativeMappingCorner.square p (toZero Z))
  exact ((fibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (NativeMappingZeroSource.cornerArrowIso p Z)).mp h

/-- Original projective trivial cofibrations give the whole actual
source mapping trivial fibration. -/
theorem source_trivial_fibration
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsFibrant Z] :
    trivialFibrations PointedCGWH.{u, v}
      (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
        X.toEnrichedFunctor p) := by
  have h := HomotopicalAlgebra.EnrichedProjective.Native.CurrentMappingSM7.trivial_left
    p (toZero Z) hp (zero_fibration Z) (NativeMappingCorner.square p (toZero Z))
  exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (NativeMappingZeroSource.cornerArrowIso p Z)).mp h

/-- Brown's actual native factorization proves full original mapping source weak invariance. -/
theorem source_weak
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y) [WeakEquivalence p]
    [IsCofibrant X] [IsCofibrant Y]
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsFibrant Z] :
    WeakEquivalence (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
      X.toEnrichedFunctor p) := by
  change WeakEquivalence ((NativeMappingSourceFunctor.source Z).map p.op)
  exact sourceFunctor_weak_of_trivialCofibrations
    (NativeMappingSourceFunctor.source (I := I) Z)
    (fun i _ _ => by
      have h := source_trivial_fibration i (mem_trivialCofibrations i) Z
      exact ((mem_trivialFibrations_iff
        (f := (NativeMappingSourceFunctor.source Z).map i.op)).mp h).2) p

end PointedCGWH.NativeCurrentBrownMapping
