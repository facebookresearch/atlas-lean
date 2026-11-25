/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.CategoricalSource.NerveQuasicategory
public import MathlibExt.AlgebraicTopology.CategoricalSource.NerveBasic
public import MathlibExt.CategoryTheory.PerfectDGModuleModels
public import MathlibExt.CategoryTheory.DGSource.EnrichedOppositeFunctor

/-!
# Native maps and quasicategory laws for the actual coherent DG nerve

The generic locally Kan coherent-nerve theorem is the completed Tau Ceti
proof port in CategoricalSource, at revision
62bbc0596dc3539d488232e4e924a338548ea0a9 (Apache 2.0). Its original authors,
file URLs and license are retained there. Transported functors below use
the native lax tensorator, enriched opposite and forgetful enrichment.
Mathlib Enriched/Basic is by Kim Morrison (2021), Apache 2.0, at
56a005855ea17e0b0958f73ec801ae140b0a1679. The two opposites retain the DG
direction and the source Alexander--Whitney/Koszul composition convention.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeDGNerveModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.EnrichedCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels

universe u v w u₁ v₁ u₂ v₂

/-- Change enrichment on an actual functor through the native lax maps. -/
def transportFunctor {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
    {W : Type u₂} [Category.{v₂} W] [MonoidalCategory W]
    (T : V ⥤ W) [T.LaxMonoidal] {C : Type v} {D : Type w}
    [EnrichedCategory V C] [EnrichedCategory V D] (F : EnrichedFunctor V C D) :
    EnrichedFunctor W (TransportEnrichment T C) (TransportEnrichment T D) where
  obj := F.obj
  map X Y := T.map (F.map X Y)
  map_id X := by
    change (Functor.LaxMonoidal.ε T ≫ T.map (eId (C := C) V X)) ≫
      T.map (F.map X X) =
      Functor.LaxMonoidal.ε T ≫ T.map (eId (C := D) V (F.obj X))
    rw [Category.assoc, ← T.map_comp, F.map_id]
  map_comp X Y Z := by
    change (Functor.LaxMonoidal.μ T _ _ ≫ T.map (eComp (C := C) V X Y Z)) ≫
      T.map (F.map X Z) = (T.map (F.map X Y) ⊗ₘ T.map (F.map Y Z)) ≫
      (Functor.LaxMonoidal.μ T _ _ ≫ T.map (eComp (C := D) V (F.obj X) (F.obj Y) (F.obj Z)))
    rw [Category.assoc, ← T.map_comp, F.map_comp, T.map_comp]
    rw [← Category.assoc, ← Functor.LaxMonoidal.μ_natural]
    exact Category.assoc _ _ _

/-- Forget enrichment without changing the enriched object or Hom map. -/
def forgetFunctor {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
    {C : Type v} {D : Type w} [EnrichedCategory V C] [EnrichedCategory V D]
    (F : EnrichedFunctor V C D) :
    EnrichedFunctor V (ForgetEnrichment V C) (ForgetEnrichment V D) where
  obj X := ForgetEnrichment.of V (F.obj (ForgetEnrichment.to V X))
  map X Y := F.map (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y)
  map_id X := F.map_id (ForgetEnrichment.to V X)
  map_comp X Y Z := F.map_comp (ForgetEnrichment.to V X)
    (ForgetEnrichment.to V Y) (ForgetEnrichment.to V Z)

/-- The actual double-opposite simplicial functor of a DG functor. -/
def dgSimplicialFunctor {k : Type u} [CommRing k] {C D : Type v}
    [DGCategory k C] [DGCategory k D] (F : EnrichedFunctor (Cochains k) C D) :
    EnrichedFunctor SSet.{u} (DGSimplicial (k := k) C) (DGSimplicial (k := k) D) :=
  forgetFunctor ((transportFunctor (cochainToSSet k) F.op).op)

/-- Coherent nerve maps retain all native simplices of the transported functor. -/
def dgNerveMap {k : Type u} [CommRing k] {C D : Type v}
    [DGCategory k C] [DGCategory k D] (F : EnrichedFunctor (Cochains k) C D) :
    dgNerve (k := k) C ⟶ dgNerve (k := k) D :=
  simplicialNerveMap (dgSimplicialFunctor F)

/-- The actual DG coherent nerve has the completed source quasicategory law. -/
theorem dgNerve_quasicategory (k : Type u) [CommRing k]
    (C : Type v) [DGCategory k C] : SSet.Quasicategory (dgNerve (k := k) C) := by
  have hkan : ∀ X Y : DGSimplicial (k := k) C, SSet.KanComplex (X ⟶[SSet.{u}] Y) :=
    fun X Y => by
      change SSet.KanComplex ((cochainToSSet k).obj
        (dgHomComplex k
          ((ForgetEnrichment.to SSet.{u} X).underlying k)
          ((ForgetEnrichment.to SSet.{u} Y).underlying k)))
      infer_instance
  unfold dgNerve
  exact @CategoryTheory.SimplicialNerve.quasicategory
    (DGSimplicial (k := k) C) inferInstance inferInstance hkan

end MathlibExt.CategoryTheory.NativeDGNerveModels
