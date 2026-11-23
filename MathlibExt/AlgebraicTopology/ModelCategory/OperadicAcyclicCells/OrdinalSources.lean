/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.HCofibration
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells
import MathlibExt.CategoryTheory.MorphismProperty.OrdinalCompactness

/-!
# Couniversal cell closure from original ordinal source-Hom comparisons

Only bottomed well-ordered diagrams occur in the smoothing construction and
its original latching prefixes. This file retains their source-Hom
preservation as explicit source data, without requiring preservation for
every filtered category. The source model's actual stationary factor,
latching maps and chosen endpoint cocones are used throughout.

The source condition must be earned separately in an application. In
particular, this file does not construct a native stable R-model or assert
the compactness of its generating endpoints.
-/

set_option autoImplicit false
noncomputable section

universe u v w w' ν

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.OrdinalCofibrationSmoothing

namespace CategoryTheory.OrdinalCofibrationSmoothing

variable {C : Type u} [Category.{v} C]

/-- The original strict prefix, with its original bottom, supplies source
Hom preservation on the actual latching category through its equivalence. -/
theorem preservesLatchingColimit (P : MorphismProperty C) (A : C)
    (hA : PreservesOrdinalColimits.{u, v, w} P A)
    {O : Type w} [LinearOrder O] [OrderBot O] [WellFoundedLT O]
    (j : O) (hj : ⊥ < j) (F : (ordinalReedy O).Latching j ⥤ C)
    (hF : ∀ (i k : (ordinalReedy O).Latching j) (f : i ⟶ k), P (F.map f)) :
    PreservesColimit F (coyoneda.obj (op A)) := by
  let e := latchingPrefixEquivalence j
  let _ : OrderBot (Set.Iio j) :=
    { bot := ⟨⊥, hj⟩
      bot_le := fun _ => bot_le }
  let _ : PreservesColimit (e.symm.functor ⋙ F) (coyoneda.obj (op A)) :=
    hA (Set.Iio j) (e.symm.functor ⋙ F) (fun i k f => hF _ _ (e.symm.functor.map f))
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  apply IsColimit.ofWhiskerEquivalence e.symm
  apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _)
  exact isColimitOfPreserves (coyoneda.obj (op A)) (hc.whiskerEquivalence e.symm)

end CategoryTheory.OrdinalCofibrationSmoothing

namespace HomotopicalAlgebra.OperadicAcyclicCells.OrdinalSources

variable {C : Type u} [Category.{v} C]

section OriginalSmoothing

variable {O : Type w} [LinearOrder O] [OrderBot O] [WellFoundedLT O]
  [ModelCategory C]
  [∀ j, HasColimitsOfShape ((ordinalReedy O).Latching j) C]
  [∀ j, HasLimitsOfShape ((ordinalReedy O).Matching j) C]

/-- All actual latching prefixes retain the three source-Hom comparisons
and the original stationary factory's full I-injective latching map. -/
theorem originalLimitLatching_trivialFibration
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f))
    (j : O) (hj : Order.IsSuccLimit j) :
    trivialFibrations C (ReedyStructure.StageFactory.latchingP (ordinalReedy O)
      (rootedArrow F).hom (smoothingLowerFactor F j) j rfl) := by
  let r := ordinalReedy O
  let L := smoothingLowerFactor F j
  have hd : r.degree j = j := rfl
  let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  let _ : IsFiltered (r.Latching j) :=
    IsFiltered.of_equivalence (latchingPrefixEquivalence j).symm
  let p := Functor.whiskerLeft (r.latchingBelow j hd) L.p
  have hTarget : IsColimit (r.latchingCocone F j) :=
    latchingIsColimitOfPrefix F j (F.isColimitOfIsWellOrderContinuous j hj)
  have hSourceMaps : ∀ (a b : r.Latching j) (f : a ⟶ b),
      P ((r.lowerLatchingDiagram L.Z j hd).map f) := by
    intro a b f
    change P ((smoothingFactor F).Z.map (r.latchingComparison f))
    exact hCof _ (smoothingFactor_map_cofibration F (leOfHom (r.latchingComparison f)))
  have hTargetMaps : ∀ (a b : r.Latching j) (f : a ⟶ b),
      P ((r.latchingDiagram F j).map f) := by
    intro a b f
    exact hF _ _ (r.latchingComparison f)
  have hp : ∀ a : r.Latching j, I.rlp (p.app a) := by
    intro a
    change I.rlp ((smoothingFactor F).p.app (r.latchingSource a))
    rw [hI]
    exact smoothingFactor_comparison_trivialFibration F (r.latchingSource a)
  have hq : ∀ a : r.Latching j,
      (colimit.cocone (r.lowerLatchingDiagram L.Z j hd)).ι.app a ≫
        ReedyStructure.StageFactory.latchingP r (rootedArrow F).hom L j hd =
          p.app a ≫ (r.latchingCocone F j).ι.app a := by
    intro a
    change colimit.ι (r.lowerLatchingDiagram L.Z j hd) a ≫
        (colimMap p ≫ ReedyStructure.latchingMap r F j) =
      p.app a ≫ F.map (r.latchingArrow a)
    calc
      _ = (colimit.ι (r.lowerLatchingDiagram L.Z j hd) a ≫ colimMap p) ≫
          ReedyStructure.latchingMap r F j := (Category.assoc _ _ _).symm
      _ = (p.app a ≫ colimit.ι (r.latchingDiagram F j) a) ≫
          ReedyStructure.latchingMap r F j :=
        congrArg (fun k => k ≫ ReedyStructure.latchingMap r F j) (ι_colimMap p a)
      _ = p.app a ≫ F.map (r.latchingArrow a) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => p.app a ≫ k) (r.latchingMap_ι F j a))
  have h := rlp_of_filtered_colimit I p
    (colimit.cocone (r.lowerLatchingDiagram L.Z j hd)) (r.latchingCocone F j)
    (colimit.isColimit _) hTarget
    (ReedyStructure.StageFactory.latchingP r (rootedArrow F).hom L j hd)
    hq hp
    (fun i => preservesLatchingColimit P i.1.left (hSources.domains i) j hj.bot_lt _ hSourceMaps)
    (fun i => preservesLatchingColimit P i.1.left (hSources.domains i) j hj.bot_lt _ hTargetMaps)
    (fun i => preservesLatchingColimit P i.1.right (hSources.codomains i) j hj.bot_lt _ hTargetMaps)
  rwa [hI] at h

/-- The original stationary smoothing factor is continuous at every actual
limit, by the earned I-injectivity of its original latching comparison. -/
theorem originalSmoothing_continuous
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f)) :
    (smoothingFactor F).Z.IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have hL := originalLimitLatching_trivialFibration I P hI hSources hCof F hF j hj
    have hC := coefficientMap_trivialFibration_of_latching F j hj.not_isMin hL
    let _ : IsIso (ReedyStructure.latchingMap (ordinalReedy O) (smoothingFactor F).Z j) :=
      smoothingFactor_latchingMap_isIso_of_coefficient F j hj.not_isMin hC
    exact prefixIsColimitOfLatchingMapIso (smoothingFactor F).Z j⟩

/-- The source colimit descends the exact original stationary comparison
against the caller's target cocone. -/
def originalSmoothingComparison (F : O ⥤ C) (cF : Cocone F)
    (cQ : Cocone (smoothingFactor F).Z) (hcQ : IsColimit cQ) : cQ.pt ⟶ cF.pt :=
  hcQ.desc (Cocone.mk cF.pt ((smoothingFactor F).p ≫ cF.ι))

/-- Each original source-colimit leg satisfies the exact original
comparison equation. -/
theorem originalSmoothingComparison_ι (F : O ⥤ C) (cF : Cocone F)
    (cQ : Cocone (smoothingFactor F).Z) (hcQ : IsColimit cQ) (j : O) :
    cQ.ι.app j ≫ originalSmoothingComparison F cF cQ hcQ =
      (smoothingFactor F).p.app j ≫ cF.ι.app j :=
  hcQ.fac (Cocone.mk cF.pt ((smoothingFactor F).p ≫ cF.ι)) j

/-- The actual complete original comparison is I-injective at the caller's
chosen endpoint cocones, by ordinal source-Hom preservation in both columns. -/
theorem originalSmoothingComparison_trivialFibration
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f))
    (cF : Cocone F) (hcF : IsColimit cF)
    (cQ : Cocone (smoothingFactor F).Z) (hcQ : IsColimit cQ) :
    trivialFibrations C (originalSmoothingComparison F cF cQ hcQ) := by
  have hQ : ∀ (i j : O) (f : i ⟶ j), P ((smoothingFactor F).Z.map f) := by
    intro i j f
    exact hCof _ (smoothingFactor_map_cofibration F (leOfHom f))
  have hComparison : ∀ j : O, I.rlp ((smoothingFactor F).p.app j) := by
    intro j
    rw [hI]
    exact smoothingFactor_comparison_trivialFibration F j
  have h := rlp_of_filtered_colimit I (smoothingFactor F).p cQ cF hcQ hcF
    (originalSmoothingComparison F cF cQ hcQ)
    (originalSmoothingComparison_ι F cF cQ hcQ) hComparison
    (fun i => hSources.domains i O _ hQ)
    (fun i => hSources.domains i O F hF)
    (fun i => hSources.codomains i O F hF)
  rwa [hI] at h

variable [HasColimitsOfShape O C] [SuccOrder O]

/-- Weakness of the original bottom-to-colimit map is proved through the
actual continuous smoothing diagram and its genuine source-model comparisons. -/
theorem weakAtOriginalCocone
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f))
    (hWeak : ∀ j : O, ¬ IsMax j → weakEquivalences C (F.map (homOfLE (Order.le_succ j))))
    (cF : Cocone F) (hcF : IsColimit cF) : weakEquivalences C (cF.ι.app ⊥) := by
  let q := smoothingFactor F
  let Q := q.Z
  let _ : Q.IsWellOrderContinuous := originalSmoothing_continuous I P hI hSources hCof F hF
  let cQ := colimit.cocone Q
  let hcQ := colimit.isColimit Q
  let p := originalSmoothingComparison F cF cQ hcQ
  have hpT : trivialFibrations C p :=
    originalSmoothingComparison_trivialFibration I P hI hSources hCof F hF cF hcF cQ hcQ
  let _ : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape O := by
    rw [← fibrations_llp C]
    infer_instance
  let t : (trivialCofibrations C).TransfiniteCompositionOfShape O (colimit.ι Q ⊥) :=
    { F := Q
      isoBot := Iso.refl _
      incl := cQ.ι
      isColimit := hcQ
      fac := Category.id_comp _
      map_mem j hj := smoothingFactor_map_trivialCofibration F (Order.le_succ j) (hWeak j hj) }
  have ht : trivialCofibrations C (colimit.ι Q ⊥) :=
    (trivialCofibrations C).transfiniteCompositionsOfShape_le O _ t.mem
  let i₀ : F.obj ⊥ ⟶ Q.obj ⊥ := q.i.app ⊥
  let p₀ : Q.obj ⊥ ⟶ F.obj ⊥ := q.p.app ⊥
  have hroot : i₀ ≫ p₀ = 𝟙 (F.obj ⊥) :=
    (congr_app q.fac ⊥).trans (rootedArrow_hom_bot F)
  have hrootWeak : weakEquivalences C i₀ :=
    (weakEquivalences C).of_postcomp _ _ (smoothingFactor_comparison_trivialFibration F ⊥).2
      (hroot.symm ▸ (weakEquivalences C).id_mem _)
  have hp₀ : colimit.ι Q ⊥ ≫ p = p₀ ≫ cF.ι.app ⊥ :=
    originalSmoothingComparison_ι F cF cQ hcQ ⊥
  have he : (i₀ ≫ colimit.ι Q ⊥) ≫ p = cF.ι.app ⊥ := by
    rw [Category.assoc, hp₀, ← Category.assoc, hroot, Category.id_comp]
  exact he ▸ (weakEquivalences C).comp_mem _ _
    ((weakEquivalences C).comp_mem _ _ hrootWeak ht.2) hpT.2

end OriginalSmoothing

section OriginalCellularClosure

variable [ModelCategory C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

/-- The entire original transfinite witness retains its bottom isomorphism
and actual endpoint map, under ordinal source-Hom preservation. -/
theorem weakOfOriginalTransfiniteComposition
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I P) (hCof : cofibrations C ≤ P)
    [P.IsStableUnderTransfiniteComposition.{w}]
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    (c : (P ⊓ weakEquivalences C).TransfiniteCompositionOfShape O f) :
    weakEquivalences C f := by
  let _ : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
  let cp := c.ofLE inf_le_left
  have h : weakEquivalences C (c.incl.app ⊥) :=
    weakAtOriginalCocone I P hI hSources hCof c.F
      (fun _ _ g => cp.map_mem_of_stable g)
      (fun j hj => (c.map_mem j hj).2) (Cocone.mk Y c.incl) c.isColimit
  have hroot : weakEquivalences C c.isoBot.inv := mem_weakEquivalences _
  exact c.fac ▸ (weakEquivalences C).comp_mem _ _ hroot h

/-- Each actual cobase change retains the ordinal source condition, so
couniversal weakness is closed inside the structural transition class. -/
theorem couniversalIntersection_stableUnderTransfiniteComposition
    (I S : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I S) (hCof : cofibrations C ≤ S)
    [S.IsStableUnderTransfiniteComposition.{w}] [S.IsStableUnderCobaseChange] :
    (couniversalWeakEquivalences C ⊓ S).IsStableUnderTransfiniteComposition.{w} where
  isStableUnderTransfiniteCompositionOfShape O _ _ _ _ :=
    { le := by
        intro X Y f hf
        obtain ⟨c⟩ := hf
        refine ⟨?_, ?_⟩
        · intro A B a q b sq
          let d := c.cobaseChange a sq
          have hPush : (couniversalWeakEquivalences C ⊓ S).pushouts ≤
              S ⊓ weakEquivalences C := by
            intro U V g hg
            obtain ⟨P, Q, i, u, v, hi, si⟩ := hg
            exact ⟨MorphismProperty.of_isPushout si hi.2, hi.1 U V u g v si⟩
          exact weakOfOriginalTransfiniteComposition I S hI hSources hCof (d.ofLE hPush)
        · exact S.transfiniteCompositionsOfShape_le O _ (c.ofLE inf_le_right).mem }

variable [UnivLE.{w', w}] [UnivLE.{ν, w}]

/-- Literal one-step couniversal arrows in the structural source class
have couniversally weak actual coproduct/pushout/transfinite cellular closure. -/
theorem cellularClosure_couniversal
    (I S Q : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I S) (hCof : cofibrations C ≤ S)
    [S.IsStableUnderTransfiniteComposition.{w}] [S.IsStableUnderCobaseChange]
    (hQ : Q ≤ couniversalWeakEquivalences C) (hQS : Q ≤ S) :
    SmallObject.CellularNormalization.cellularClosure.{w', ν} Q ≤
      couniversalWeakEquivalences C := by
  let T := couniversalWeakEquivalences C ⊓ S
  have hTmax : T.IsStableUnderTransfiniteComposition.{w} :=
    couniversalIntersection_stableUnderTransfiniteComposition I S hI hSources hCof
  have hTν : T.IsStableUnderTransfiniteComposition.{ν} :=
    @IsStableUnderTransfiniteComposition.shrink _ _ T hTmax inferInstance
  let _ : T.IsStableUnderTransfiniteComposition.{w'} :=
    @IsStableUnderTransfiniteComposition.shrink _ _ T hTmax inferInstance
  let _ : T.IsStableUnderCobaseChange := inferInstance
  have hCop : HasCoproducts.{ν} C :=
    fun _ => HasColimitsOfShape.of_essentiallySmall C _
  let _ : T.IsStableUnderCoproducts.{ν} :=
    @isStableUnderCoproducts_of_cobase_transfinite _ _ T inferInstance hTν hCop
  have hQT : Q ≤ T := le_inf hQ hQS
  have hPush : (coproducts.{ν} Q).pushouts ≤ T :=
    (pushouts_le_iff (P := coproducts.{ν} Q)).2 ((coproducts_le_iff (P := Q)).2 hQT)
  exact ((transfiniteCompositions_monotone hPush).trans
    (transfiniteCompositions_le T)).trans inf_le_left

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

/-- The original heterogeneous finite-family coefficient-orbit criterion
earns the full operadic acyclic cellular closure, from ordinal source Hom.
The cofibration-orbit source class and its closure are the existing actual ones. -/
theorem operadicAcyclicCells_couniversal
    (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hSources : SourceHomPreservation.{u, v, w} I (cofibrationCells.{w, ν} C))
    (h : AcyclicSymmetricHMonoidality C) :
    SmallObject.CellularNormalization.cellularClosure.{w', ν}
      (OperadicOrbitCells.orbitGenerators (trivialCofibrations C)) ≤
        couniversalWeakEquivalences C := by
  let S := cofibrationCells.{w, ν} C
  let _ : S.IsStableUnderCobaseChange := cofibrationCells_stable.1
  let _ : S.IsStableUnderTransfiniteComposition.{w} := cofibrationCells_stable.2.2
  exact cellularClosure_couniversal.{u, v, w, w', ν} I S _ hI hSources
    cofibrations_le_cofibrationCells h.generators_le trivialOrbitGenerators_le_cofibrationCells

end OriginalCellularClosure


end HomotopicalAlgebra.OperadicAcyclicCells.OrdinalSources
