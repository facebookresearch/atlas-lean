/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalContinuousSourceApproximation
import MathlibExt.CategoryTheory.MorphismProperty.InverseTowerMapping

/-!
# Original Omega mapping ordinal closure

The actual source mapping inverse system retains every original ordinal stage
and target. Boundary lifts are constructed from genuine successor lifting and
actual limiting cones. Native Omega-test closure uses the full original source
approximation and caller cocones; no stable model or weak closure is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v w uC vC

namespace PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective
open PointedCGWH.Spectra.NativeOmegaWeakClosure
open PointedCGWH.Spectra.OriginalContinuousSourceApproximation
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Every actual native source predecessor colimit gives the genuine same original
inverse mapping-tower cone at the original limit stage. -/
def nativePrecedingMappingIsLimit (Q : J ⥤ Carrier (I := I)) [Q.IsWellOrderContinuous]
    (E : Carrier (I := I)) (m : J) (hm : Order.IsSuccLimit m) :
    IsLimit (CategoryTheory.OriginalInverseTowerLifting.precedingCone
      (sourceMappingDiagram Q E) m) := by
  let G := PointedCGWH.NativeMappingSourceFunctor.source E
  let : PreservesLimitsOfSize.{v, v} G :=
    PointedCGWH.NativeMappingSourcePreservation.source_preservesLimitsOfSize E
  exact CategoryTheory.OriginalInverseTowerLifting.sourcePrecedingIsLimit G Q m hm

end PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

namespace PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective
open PointedCGWH.Spectra.OriginalContinuousSourceApproximation
open scoped CGWH.modelCategory MonoidalClosed

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev SourceCarrier := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The full original source approximation successor retains original Ω tests of the
caller successor by its same level-weak counit square on actual continuous HEP input F. -/
theorem source_successor_omegaTests (F : J ⥤ SourceCarrier (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j : J, ¬IsMax j → NativeK.omegaTests s (F.map (homOfLE (Order.le_succ j))))
    (j : J) (hj : ¬IsMax j) :
    NativeK.omegaTests s ((source (B := B) F).map (homOfLE (Order.le_succ j))) := by
  have h0 := NativeK.levelWeak_le_omegaTests s ((counit (B := B) F).app j)
    (counit_levelWeak (B := B) F hF j)
  have h1 := NativeK.levelWeak_le_omegaTests s ((counit (B := B) F).app (Order.succ j))
    (counit_levelWeak (B := B) F hF (Order.succ j))
  have hComp := (NativeK.omegaTests s).comp_mem _ _ h0 (hW j hj)
  have hSq := (counit (B := B) F).naturality (homOfLE (Order.le_succ j))
  rw [← hSq] at hComp
  exact (NativeK.omegaTests s).of_postcomp _ _ h1 hComp

/-- Every actual mapping transition against every original Ω target is a genuine scalar
trivial fibration, from original I source cofibrancy and full Ω Hom tests. -/
theorem source_successor_mapping_trivialFibration
    (F : J ⥤ SourceCarrier (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j : J, ¬IsMax j → NativeK.omegaTests s (F.map (homOfLE (Order.le_succ j))))
    (E : SourceCarrier (I := I)) (hE : NativeK.IsOmega s E) (j : J) (hj : ¬IsMax j) :
    trivialFibrations PointedCGWH.{u, v}
      (NativeK.mapSource ((source (B := B) F).map (homOfLE (Order.le_succ j))) E) := by
  let : IsCofibrant ((source (B := B) F).obj j) := source_stage_cofibrant F j
  let : IsCofibrant ((source (B := B) F).obj (Order.succ j)) := source_stage_cofibrant F _
  refine ⟨NativeK.mapSource_fibration _ (source_successor_cofibration F j hj) E, ?_⟩
  exact DerivedLocalMapping.mappingPre_weak_of_omegaTests s _
    (source_successor_omegaTests s F hF hW j hj) E hE

end PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

namespace PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective
open PointedCGWH.Spectra.NativeOmegaWeakClosure
open PointedCGWH.Spectra.OriginalContinuousSourceApproximation
open scoped CGWH.modelCategory MonoidalClosed

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeC := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Every complete source endpoint restriction into an actual Ω target is a genuine scalar
trivial fibration, by the canonical continuous inverse-tower lifting theorem. -/
theorem sourceEndpoint_mapping_trivialFibration
    (F : J ⥤ NativeC (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j : J, ¬IsMax j → NativeK.omegaTests s (F.map (homOfLE (Order.le_succ j))))
    (q : Cocone (source (B := B) F)) (hq : IsColimit q)
    (E : NativeC (I := I)) (hE : NativeK.IsOmega s E) :
    trivialFibrations PointedCGWH.{u, v} (NativeK.mapSource (q.ι.app ⊥) E) := by
  let Q := source (B := B) F
  let : Q.IsWellOrderContinuous := source_continuous F
  let D := sourceMappingDiagram Q E
  let c := sourceMappingCone q E
  let hc := sourceMappingConeIsLimit q hq E
  let G := PointedCGWH.NativeMappingSourceFunctor.source E
  let : PreservesLimitsOfSize.{v, v} G :=
    PointedCGWH.NativeMappingSourcePreservation.source_preservesLimitsOfSize E
  let : D.rightOp.IsWellOrderContinuous :=
    CategoryTheory.OriginalInverseTowerLifting.sourceMappingWellOrderContinuous G Q
  change trivialFibrations PointedCGWH.{u, v} (c.π.app (Opposite.op ⊥))
  rw [← cofibrations_rlp]
  exact MorphismProperty.continuous_inverse_tower_rlp
    (cofibrations PointedCGWH.{u, v}) D c hc (fun j hj => by
      rw [cofibrations_rlp]
      exact source_successor_mapping_trivialFibration s F hF hW E hE j hj)

/-- The exact caller's original HEP/Ωweak successor chain is Ωweak at its actual chosen
bottom-to-colimit map, preserving all original stage/limit/cocone maps and arbitrary endpoints. -/
theorem originalHEPOrdinal_omegaTests
    (F : J ⥤ NativeC (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j : J, ¬IsMax j → NativeK.omegaTests s (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : NativeK.omegaTests s (c.ι.app ⊥) := by
  let Q := source (B := B) F
  let : Q.IsWellOrderContinuous := source_continuous F
  let : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := Native.nativeColimits
  let q := colimit.cocone Q
  let hq := colimit.isColimit Q
  let p := sourceColimitComparison F c q hq
  have hp : NativeK.omegaTests s p := NativeK.levelWeak_le_omegaTests s p
    (sourceColimitComparison_levelWeak F hF c hc q hq)
  have h0 : NativeK.omegaTests s ((counit (B := B) F).app ⊥) :=
    NativeK.levelWeak_le_omegaTests s _ (counit_levelWeak F hF ⊥)
  let : IsCofibrant (Q.obj ⊥) := source_stage_cofibrant F ⊥
  let : IsCofibrant (colimit Q) := continuousCofibrationColimit_cofibrant Q q hq
    (source_successor_cofibration F)
  let : IsCofibrant (((Functor.const J).obj q.pt).obj ⊥) := by
    change IsCofibrant (colimit Q)
    infer_instance
  have hqW : NativeK.omegaTests s (q.ι.app ⊥) := by
    apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s (q.ι.app ⊥)
    intro E hE
    exact (sourceEndpoint_mapping_trivialFibration s F hF hW q hq E hE).2
  have hComp := (NativeK.omegaTests s).comp_mem _ _ hqW hp
  have hLeg := sourceColimitComparison_ι F c q hq ⊥
  rw [hLeg] at hComp
  exact (NativeK.omegaTests s).of_precomp _ _ h0 hComp

end PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure
namespace PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev CNative := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- An actual complete original HEP/Ω-test transfinite witness gives Ω-test weakness of
its unchanged original endpoint map, retaining the actual bottom isomorphism. -/
theorem originalTransfiniteWitness_omegaTests {X Y : CNative (I := I)} {f : X ⟶ Y}
    (d : (PointedCGWH.EnrichedBasedHomotopyExtension.property ⊓
      NativeK.omegaTests s).TransfiniteCompositionOfShape J f) : NativeK.omegaTests s f := by
  let c : Cocone d.F := { pt := Y, ι := d.incl }
  have hEnd := originalHEPOrdinal_omegaTests s d.F (fun j hj => (d.map_mem j hj).1)
    (fun j hj => (d.map_mem j hj).2) c d.isColimit
  have hIso : NativeK.omegaTests s d.isoBot.inv := (NativeK.omegaTests s).of_isIso _
  have hComp := (NativeK.omegaTests s).comp_mem _ _ hIso hEnd
  exact d.fac ▸ hComp

end PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure
namespace PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [Small.{v} J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I

omit B in
private theorem smallShapeMapArrow_target_eq {C : Type uC} [Category.{vC} C]
    {K : Type w} [Preorder K] (F : K ⥤ C) {i j k : K}
    (hij : i ≤ j) (hik : i ≤ k) (h : j = k) :
    Arrow.mk (F.map (homOfLE hij)) = Arrow.mk (F.map (homOfLE hik)) := by
  cases h
  rfl

/-- Every allowed original small ordinal shape retains the caller's actual endpoint,
bottom map, all stage maps and genuine continuity under the original order isomorphism. -/
theorem originalHEPOrdinal_small_omegaTests
    (F : J ⥤ D (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hW : ∀ j : J, ¬IsMax j → NativeK.omegaTests s (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : NativeK.omegaTests s (c.ι.app ⊥) := by
  let e := orderIsoShrink.{v} J
  let G := e.symm.equivalence.functor ⋙ F
  let d := c.whisker e.symm.equivalence.functor
  let hd := hc.whiskerEquivalence e.symm.equivalence
  let : G.IsWellOrderContinuous := inferInstance
  have hG (j : Shrink.{v} J) (hj : ¬IsMax j) :
      PointedCGWH.EnrichedBasedHomotopyExtension.property
        (G.map (homOfLE (Order.le_succ j))) := by
    have hJ : ¬IsMax (e.symm j) := (OrderIso.isMax_apply e.symm).not.mpr hj
    have hArrow : Arrow.mk (G.map (homOfLE (Order.le_succ j))) =
      Arrow.mk (F.map (homOfLE (Order.le_succ (e.symm j)))) := by
      exact smallShapeMapArrow_target_eq F
        (leOfHom (e.symm.equivalence.functor.map (homOfLE (Order.le_succ j))))
        (Order.le_succ (e.symm j)) (e.symm.map_succ j)
    rw [← PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff,
      hArrow, PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff]
    exact hF _ hJ
  have hGW (j : Shrink.{v} J) (hj : ¬IsMax j) :
      NativeK.omegaTests s (G.map (homOfLE (Order.le_succ j))) := by
    have hJ : ¬IsMax (e.symm j) := (OrderIso.isMax_apply e.symm).not.mpr hj
    have hArrow : Arrow.mk (G.map (homOfLE (Order.le_succ j))) =
        Arrow.mk (F.map (homOfLE (Order.le_succ (e.symm j)))) :=
      smallShapeMapArrow_target_eq F
        (leOfHom (e.symm.equivalence.functor.map (homOfLE (Order.le_succ j))))
        (Order.le_succ (e.symm j)) (e.symm.map_succ j)
    rw [← (NativeK.omegaTests s).arrow_mk_mem_toSet_iff, hArrow,
      (NativeK.omegaTests s).arrow_mk_mem_toSet_iff]
    exact hW _ hJ
  have hEnd := originalHEPOrdinal_omegaTests s G hG hGW d hd
  have hBot : e.symm ⊥ = (⊥ : J) := e.symm.map_bot
  have hArrow : Arrow.mk (d.ι.app ⊥) = Arrow.mk (c.ι.app ⊥) := by
    exact congrArg (fun j => Arrow.mk (c.ι.app j)) hBot
  rw [← (NativeK.omegaTests s).arrow_mk_mem_toSet_iff, hArrow,
    (NativeK.omegaTests s).arrow_mk_mem_toSet_iff] at hEnd
  exact hEnd

/-- The actual original HEP/Ωweak class is closed under every allowed original small
ordinal witness, with its continuous diagram and complete endpoint maps retained. -/
theorem originalTransfiniteSmallWitness_omegaTests {X Y : D (I := I)} {f : X ⟶ Y}
    (d : (PointedCGWH.EnrichedBasedHomotopyExtension.property ⊓
      NativeK.omegaTests s).TransfiniteCompositionOfShape J f) : NativeK.omegaTests s f := by
  let c : Cocone d.F := { pt := Y, ι := d.incl }
  have hEnd := originalHEPOrdinal_small_omegaTests s d.F
    (fun j hj => (d.map_mem j hj).1) (fun j hj => (d.map_mem j hj).2) c d.isColimit
  have hIso : NativeK.omegaTests s d.isoBot.inv := (NativeK.omegaTests s).of_isIso _
  have hComp := (NativeK.omegaTests s).comp_mem _ _ hIso hEnd
  exact d.fac ▸ hComp

instance originalHEPOmega_isStableUnderTransfiniteComposition :
    (PointedCGWH.EnrichedBasedHomotopyExtension.property (I := I) ⊓
      NativeK.omegaTests s).IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    intro X Y f hf
    obtain ⟨d⟩ := hf
    exact ⟨MorphismProperty.transfiniteCompositionsOfShape_le _ J _
      (d.ofLE inf_le_left).mem, originalTransfiniteSmallWitness_omegaTests s d⟩

end PointedCGWH.Spectra.OriginalOmegaMappingOrdinalClosure
