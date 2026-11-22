/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.InverseOrdinalInjectiveLimit
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOmegaMappingOrdinalClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSingularModel
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourcePreservation
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Combinatorial

/-!
# Original vertical Omega comparisons on continuous HEP diagrams

The original coherent I approximation is natural on every input diagram.
Its cofibrant stages and cofibration transitions give continuous inverse
mapping towers against every original Omega target. The actual singular
functor preserves those limits and detects their weak maps. The internally
constructed simplicial injective model gives the genuine weak limit map.
Both original approximation counits and caller-colimit comparisons then
transfer the result to the unchanged caller arrow.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits SSet.modelCategoryQuillen MonoidalClosed

namespace PointedCGWH.Spectra.StableHEPOrdinalWeakComparison

open PointedCGWH.SingularHomotopyGeometry
open OriginalContinuousSourceApproximation

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.NativeMappingSourceFunctor.sourceHasProducts
  PointedCGWH.NativeMappingSourceFunctor.sourceHasEqualizers

private theorem singular_preservesLimits : PreservesLimits singularFunctor.{u, v} := by
  let _ : underlyingSingularFunctor.{u, v}.IsRightAdjoint := SSet.sSetCGWHAdj.{u, v}.isRightAdjoint
  let _ : (Under.forget CGWH.point.{u, v}).IsRightAdjoint :=
    (Under.costarAdjForget CGWH.point.{u, v}).isRightAdjoint
  change PreservesLimits (Under.forget CGWH.point.{u, v} ⋙ underlyingSingularFunctor.{u, v})
  infer_instance

private theorem singular_isFibrant (X : PointedCGWH.{u, v}) :
    IsFibrant (singularFunctor.obj X) :=
  TopCat.toSSet_obj_kanComplex (CGWH.cgwhToTop.obj X.right)

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (s : NativeStabilizationFamily.{u, v} I L)

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

section NativeSize

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- Actual cofibrant stages, original cofibration transitions and all
component Omega tests give the full caller-colimit Omega comparison. -/
theorem cofibrantContinuousComparison_omegaTests
    (F G : J ⥤ Carrier (I := I)) [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hFcof : ∀ j : J, IsCofibrant (F.obj j)) (hGcof : ∀ j : J, IsCofibrant (G.obj j))
    (hFstep : ∀ j : J, ¬IsMax j → cofibrations (Carrier (I := I))
      (F.map (homOfLE (Order.le_succ j))))
    (hGstep : ∀ j : J, ¬IsMax j → cofibrations (Carrier (I := I))
      (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j : J, NativeK.omegaTests s (α.app j))
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ j : J, cF.ι.app j ≫ d = α.app j ≫ cG.ι.app j) :
    NativeK.omegaTests s d := by
  let _ : IsCofibrant (F.obj ⊥) := hFcof ⊥
  let _ : IsCofibrant (G.obj ⊥) := hGcof ⊥
  let _ : IsCofibrant cF.pt := continuousCofibrationColimit_cofibrant F cF hcF hFstep
  let _ : IsCofibrant cG.pt := continuousCofibrationColimit_cofibrant G cG hcG hGstep
  apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s d
  intro E hE
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  let R := PointedCGWH.NativeMappingSourceFunctor.source E
  let _ : PreservesLimitsOfSize.{v, v} R :=
    PointedCGWH.NativeMappingSourcePreservation.source_preservesLimitsOfSize E
  let _ : PreservesLimits singularFunctor.{u, v} := singular_preservesLimits
  let K := R ⋙ singularFunctor.{u, v}
  let _ : PreservesLimitsOfSize.{v, v} K := inferInstance
  let TF := F.op ⋙ K
  let TG := G.op ⋙ K
  let _ : TF.rightOp.IsWellOrderContinuous :=
    OriginalInverseTowerLifting.sourceMappingWellOrderContinuous K F
  let _ : TG.rightOp.IsWellOrderContinuous :=
    OriginalInverseTowerLifting.sourceMappingWellOrderContinuous K G
  let β : TG ⟶ TF := Functor.whiskerRight (NatTrans.op α) K
  have hTFbot : IsFibrant (TF.obj (Opposite.op (⊥ : J))) :=
    singular_isFibrant (R.obj (Opposite.op (F.obj ⊥)))
  have hTGbot : IsFibrant (TG.obj (Opposite.op (⊥ : J))) :=
    singular_isFibrant (R.obj (Opposite.op (G.obj ⊥)))
  have hTFstep (j : J) (hj : ¬IsMax j) :
      Fibration (TF.map (homOfLE (Order.le_succ j)).op) := by
    apply (HomotopicalAlgebra.fibration_iff _).mpr
    apply PointedCGWH.SingularModel.preservesFibrations
    change fibrations PointedCGWH.{u, v}
      (NativeK.mapSource (F.map (homOfLE (Order.le_succ j))) E)
    exact NativeK.mapSource_fibration _ (hFstep j hj) E
  have hTGstep (j : J) (hj : ¬IsMax j) :
      Fibration (TG.map (homOfLE (Order.le_succ j)).op) := by
    apply (HomotopicalAlgebra.fibration_iff _).mpr
    apply PointedCGWH.SingularModel.preservesFibrations
    change fibrations PointedCGWH.{u, v}
      (NativeK.mapSource (G.map (homOfLE (Order.le_succ j))) E)
    exact NativeK.mapSource_fibration _ (hGstep j hj) E
  have hβ (j : Jᵒᵖ) : weakEquivalences SSet.{v} (β.app j) := by
    let _ : IsCofibrant (F.obj j.unop) := hFcof j.unop
    let _ : IsCofibrant (G.obj j.unop) := hGcof j.unop
    change SSet.realizationWeakEquivalences
      (singularFunctor.map (NativeK.mapSource (α.app j.unop) E))
    exact (SingularMapping.singularFunctor_weak_iff _).mpr
      (DerivedLocalMapping.mappingPre_weak_of_omegaTests s (α.app j.unop) (hα j.unop) E hE)
  let cTF : Cone TF := K.mapCone cF.op
  let cTG : Cone TG := K.mapCone cG.op
  let hcTF : IsLimit cTF := isLimitOfPreserves K hcF.op
  let hcTG : IsLimit cTG := isLimitOfPreserves K hcG.op
  have hLeg (j : Jᵒᵖ) :
      K.map d.op ≫ cTF.π.app j = cTG.π.app j ≫ β.app j := by
    change K.map d.op ≫ K.map (cF.ι.app j.unop).op =
      K.map (cG.ι.app j.unop).op ≫ K.map (α.app j.unop).op
    rw [← K.map_comp, ← K.map_comp]
    have h := congrArg (fun f : F.obj j.unop ⟶ cG.pt => f.op) (hd j.unop)
    exact congrArg K.map h
  have hWeak : WeakEquivalence (K.map d.op) :=
    HomotopicalAlgebra.InverseOrdinalInjectiveLimit.weakEquivalence_of_continuous_inverse_isLimits
      TG TF β hTGbot hTFbot hTGstep hTFstep hβ cTG cTF hcTG hcTF (K.map d.op) hLeg
  have hSingular := (HomotopicalAlgebra.weakEquivalence_iff (K.map d.op)).mp hWeak
  change SSet.realizationWeakEquivalences (singularFunctor.map (NativeK.mapSource d E)) at hSingular
  exact (SingularMapping.singularFunctor_weak_iff _).mp hSingular

/-- The two genuine original I approximations transfer every component
Omega test to the complete comparison of the caller's HEP colimits. -/
theorem originalHEPOrdinalComparison_omegaTests
    (F G : J ⥤ Carrier (I := I)) [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j : J, NativeK.omegaTests s (α.app j))
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ j : J, cF.ι.app j ≫ d = α.app j ≫ cG.ι.app j) :
    NativeK.omegaTests s d := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let QF := source (B := B) F
  let QG := source (B := B) G
  let _ : QF.IsWellOrderContinuous := source_continuous F
  let _ : QG.IsWellOrderContinuous := source_continuous G
  let qF := colimit.cocone QF
  let qG := colimit.cocone QG
  let hqF := colimit.isColimit QF
  let hqG := colimit.isColimit QG
  let γ := sourceMap (B := B) α
  let g := colimMap γ
  let W := NativeK.omegaTests s
  have hγ (j : J) : W (γ.app j) := by
    have hPF : W ((counit (B := B) F).app j) :=
      NativeK.levelWeak_le_omegaTests s _ (counit_levelWeak F hF j)
    have hPG : W ((counit (B := B) G).app j) :=
      NativeK.levelWeak_le_omegaTests s _ (counit_levelWeak G hG j)
    have hn := congrArg (fun η => η.app j) (counit_naturality (B := B) α)
    change γ.app j ≫ (counit (B := B) G).app j =
      (counit (B := B) F).app j ≫ α.app j at hn
    have h := W.comp_mem _ _ hPF (hα j)
    rw [← hn] at h
    exact W.of_postcomp _ _ hPG h
  have hg : W g := cofibrantContinuousComparison_omegaTests s QF QG γ
    (source_stage_cofibrant F) (source_stage_cofibrant G)
    (source_successor_cofibration F) (source_successor_cofibration G) hγ
    qF qG hqF hqG g (fun j => ι_colimMap γ j)
  let pF := sourceColimitComparison F cF qF hqF
  let pG := sourceColimitComparison G cG qG hqG
  have hpF : W pF := NativeK.levelWeak_le_omegaTests s _
    (sourceColimitComparison_levelWeak F hF cF hcF qF hqF)
  have hpG : W pG := NativeK.levelWeak_le_omegaTests s _
    (sourceColimitComparison_levelWeak G hG cG hcG qG hqG)
  have hn : pF ≫ d = g ≫ pG := by
    apply hqF.hom_ext
    intro j
    have h := congrArg (fun η => η.app j) (counit_naturality (B := B) α)
    change γ.app j ≫ (counit (B := B) G).app j =
      (counit (B := B) F).app j ≫ α.app j at h
    calc
      qF.ι.app j ≫ (pF ≫ d) = ((counit (B := B) F).app j ≫ cF.ι.app j) ≫ d := by
        rw [← Category.assoc, sourceColimitComparison_ι]
      _ = (counit (B := B) F).app j ≫ (α.app j ≫ cG.ι.app j) := by
        rw [Category.assoc, hd]
      _ = (γ.app j ≫ (counit (B := B) G).app j) ≫ cG.ι.app j := by
        rw [← Category.assoc]
        exact congrArg (fun f => f ≫ cG.ι.app j) h.symm
      _ = γ.app j ≫ (qG.ι.app j ≫ pG) := by
        rw [Category.assoc, sourceColimitComparison_ι]
      _ = (qF.ι.app j ≫ g) ≫ pG := by
        change γ.app j ≫ colimit.ι QG j ≫ pG =
          (colimit.ι QF j ≫ colimMap γ) ≫ pG
        rw [ι_colimMap γ j, Category.assoc]
      _ = qF.ι.app j ≫ (g ≫ pG) := Category.assoc _ _ _
  have hComp := W.comp_mem _ _ hg hpG
  rw [← hn] at hComp
  exact W.of_precomp _ _ hpF hComp

end NativeSize

section ArbitrarySmallShape

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [Small.{v} J]

omit B in
private theorem mapArrow_target_eq {D : Type*} [Category D] {K : Type*} [Preorder K]
    (F : K ⥤ D) {i j k : K} (hij : i ≤ j) (hik : i ≤ k) (h : j = k) :
    Arrow.mk (F.map (homOfLE hij)) = Arrow.mk (F.map (homOfLE hik)) := by
  cases h
  rfl

/-- Every original permitted small well-order retains both actual caller
colimit endpoints, all diagram maps, all vertical maps and every leg equation. -/
theorem originalHEPOrdinalSmallComparison_omegaTests
    (F G : J ⥤ Carrier (I := I)) [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j : J, NativeK.omegaTests s (α.app j))
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ j : J, cF.ι.app j ≫ d = α.app j ≫ cG.ι.app j) :
    NativeK.omegaTests s d := by
  let e := orderIsoShrink.{v} J
  let U := e.symm.equivalence.functor
  let F' := U ⋙ F
  let G' := U ⋙ G
  let α' := Functor.whiskerLeft U α
  let cF' := cF.whisker U
  let cG' := cG.whisker U
  let hcF' := hcF.whiskerEquivalence e.symm.equivalence
  let hcG' := hcG.whiskerEquivalence e.symm.equivalence
  let _ : F'.IsWellOrderContinuous := inferInstance
  let _ : G'.IsWellOrderContinuous := inferInstance
  have hF' (j : Shrink.{v} J) (hj : ¬IsMax j) :
      PointedCGWH.EnrichedBasedHomotopyExtension.property
        (F'.map (homOfLE (Order.le_succ j))) := by
    have hJ : ¬IsMax (e.symm j) := (OrderIso.isMax_apply e.symm).not.mpr hj
    have hArrow : Arrow.mk (F'.map (homOfLE (Order.le_succ j))) =
        Arrow.mk (F.map (homOfLE (Order.le_succ (e.symm j)))) :=
      mapArrow_target_eq F (leOfHom (U.map (homOfLE (Order.le_succ j))))
        (Order.le_succ (e.symm j)) (e.symm.map_succ j)
    rw [← PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff,
      hArrow, PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff]
    exact hF _ hJ
  have hG' (j : Shrink.{v} J) (hj : ¬IsMax j) :
      PointedCGWH.EnrichedBasedHomotopyExtension.property
        (G'.map (homOfLE (Order.le_succ j))) := by
    have hJ : ¬IsMax (e.symm j) := (OrderIso.isMax_apply e.symm).not.mpr hj
    have hArrow : Arrow.mk (G'.map (homOfLE (Order.le_succ j))) =
        Arrow.mk (G.map (homOfLE (Order.le_succ (e.symm j)))) :=
      mapArrow_target_eq G (leOfHom (U.map (homOfLE (Order.le_succ j))))
        (Order.le_succ (e.symm j)) (e.symm.map_succ j)
    rw [← PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff,
      hArrow, PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff]
    exact hG _ hJ
  exact originalHEPOrdinalComparison_omegaTests s F' G' α' hF' hG'
    (fun j => hα (e.symm j)) cF' cG' hcF' hcG' d (fun j => hd (e.symm j))

end ArbitrarySmallShape

end PointedCGWH.Spectra.StableHEPOrdinalWeakComparison
