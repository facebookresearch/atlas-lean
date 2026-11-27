/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationDeltaGeneratedFiniteLimits
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatDeltaGeneratedWeakHomotopy
public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Realization of boundary-right-lifting simplicial maps

Let p:E→B have right lifting against every simplicial boundary inclusion. Its geometric
realization |p| has right lifting against every realized horn inclusion, in every universe u.

The conclusion concerns the realized-horn lifting class on topological spaces. The retract and
product presentation can be compared through delta-generated coreflection and the
singular-complex functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Convexity Topology
  HomotopicalAlgebra CategoryTheory.MorphismProperty
open scoped SSet.modelCategoryQuillen

noncomputable section
universe u

private theorem fibration_coreflection_iff
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.realizedHornInclusions.{u}.rlp
        (DeltaGenerated.deltaGeneratedToTop.map
          (TopCat.toDeltaGenerated.map f)) ↔
      TopCat.realizedHornInclusions.{u}.rlp f := by
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp,
    TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  let cX := DeltaGenerated.coreflectorAdjunction.counit.app X
  let cY := DeltaGenerated.coreflectorAdjunction.counit.app Y
  let _ : IsIso (TopCat.toSSet.map cX) :=
    TopCat.toSSet_map_coreflectionCounit_isIso X
  let _ : IsIso (TopCat.toSSet.map cY) :=
    TopCat.toSSet_map_coreflectionCounit_isIso Y
  let e : Arrow.mk
      (TopCat.toSSet.map
        (DeltaGenerated.deltaGeneratedToTop.map
          (TopCat.toDeltaGenerated.map f))) ≅
      Arrow.mk (TopCat.toSSet.map f) :=
    Arrow.isoMk (asIso (TopCat.toSSet.map cX))
      (asIso (TopCat.toSSet.map cY)) (by
        dsimp [cX, cY]
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg TopCat.toSSet.map
          (DeltaGenerated.coreflectorAdjunction.counit.naturality f).symm)
  exact SSet.modelCategoryQuillen.J.rlp.arrow_mk_iso_iff e

private theorem productProjection_hornRLP (X Y : TopCat.{u}) :
    TopCat.realizedHornInclusions.{u}.rlp
      (prod.snd : X ⨯ Y ⟶ Y) := by
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
    TopCat.toSSet_obj_kanComplex X
  have hTerminal : SSet.modelCategoryQuillen.J.{u}.rlp
      (terminal.from (TopCat.toSSet.obj X)) := by
    rw [← SSet.modelCategoryQuillen.fibrations_eq]
    exact HomotopicalAlgebra.mem_fibrations _
  have hProduct : SSet.modelCategoryQuillen.J.{u}.rlp
      (prod.snd : TopCat.toSSet.obj X ⨯ TopCat.toSSet.obj Y ⟶
        TopCat.toSSet.obj Y) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasBinaryProduct'
        (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)) hTerminal
  let c := prodComparison TopCat.toSSet X Y
  let _ : IsIso c := inferInstance
  let e : Arrow.mk (TopCat.toSSet.map
      (prod.snd : X ⨯ Y ⟶ Y)) ≅
      Arrow.mk (prod.snd : TopCat.toSSet.obj X ⨯
        TopCat.toSSet.obj Y ⟶ TopCat.toSSet.obj Y) :=
    Arrow.isoMk (asIso c) (Iso.refl _) (by
      dsimp [c]
      rw [prodComparison_snd]
      simp)
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_mk_iso_iff e).mpr hProduct

private noncomputable def graphRetract
    {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.I.{u}.rlp p) :
    RetractArrow p (prod.snd : E ⨯ B ⟶ B) := by
  let i : E ⟶ E ⨯ B := prod.lift (𝟙 E) p
  let _ : Mono i := mono_of_mono_fac (prod.lift_fst (𝟙 E) p)
  have hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
    rwa [SSet.rlp_monomorphisms]
  let _ : HasLiftingProperty i p :=
    hp' i (MorphismProperty.monomorphisms.infer_property i)
  exact RetractArrow.ofRightLiftingProperty
    (f := p) (i := i) (p := (prod.snd : E ⨯ B ⟶ B))
      (prod.lift_snd (𝟙 E) p)

private theorem coreflectedProductProjection_hornRLP
    (E B : SSet.{u}) :
    TopCat.realizedHornInclusions.{u}.rlp
      (DeltaGenerated.deltaGeneratedToTop.map
        (prod.snd :
          (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj E ⨯
            (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B ⟶
          (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B)) := by
  let qTop : SSet.toTop.obj E ⨯ SSet.toTop.obj B ⟶
      SSet.toTop.obj B := prod.snd
  have hTop : TopCat.realizedHornInclusions.{u}.rlp qTop :=
    productProjection_hornRLP _ _
  have hCore : TopCat.realizedHornInclusions.{u}.rlp
      (DeltaGenerated.deltaGeneratedToTop.map
        (TopCat.toDeltaGenerated.map qTop)) :=
    (fibration_coreflection_iff qTop).mpr hTop
  let c := prodComparison TopCat.toDeltaGenerated
    (SSet.toTop.obj E) (SSet.toTop.obj B)
  let _ : IsIso c := inferInstance
  have hc : c ≫
      (prod.snd :
        (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj E ⨯
          (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B ⟶
        (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B) =
      TopCat.toDeltaGenerated.map qTop := by
    dsimp [c, qTop]
    exact prodComparison_snd TopCat.toDeltaGenerated
      (SSet.toTop.obj E) (SSet.toTop.obj B)
  have hLc := congrArg
    (fun k => DeltaGenerated.deltaGeneratedToTop.map k) hc
  let e : Arrow.mk
      (DeltaGenerated.deltaGeneratedToTop.map
        (TopCat.toDeltaGenerated.map qTop)) ≅
      Arrow.mk
        (DeltaGenerated.deltaGeneratedToTop.map
          (prod.snd :
            (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj E ⨯
              (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B ⟶
            (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B)) :=
    Arrow.isoMk
      (DeltaGenerated.deltaGeneratedToTop.mapIso (asIso c))
      (Iso.refl _) (by
        change DeltaGenerated.deltaGeneratedToTop.map c ≫
          DeltaGenerated.deltaGeneratedToTop.map
            (prod.snd :
              (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj E ⨯
                (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B ⟶
              (SSet.toTop ⋙ TopCat.toDeltaGenerated).obj B) =
          DeltaGenerated.deltaGeneratedToTop.map
            (TopCat.toDeltaGenerated.map qTop) ≫ 𝟙 _
        simpa only [Functor.map_comp, Category.comp_id] using hLc)
  exact (TopCat.realizedHornInclusions.rlp.arrow_mk_iso_iff e).mp hCore

namespace SSet

/-- For a simplicial map p:E→B with right lifting against every boundary inclusion, the realized map
|p|:|E|→|B| has right lifting against all realized horn inclusions. All spaces and simplicial
sets use an arbitrary universe u. -/
theorem toTop_map_mem_realizedHornRLP_of_I_rlp
    {E B : SSet.{u}} {p : E ⟶ B}
    (hp : modelCategoryQuillen.I.{u}.rlp p) :
    TopCat.realizedHornInclusions.{u}.rlp (toTop.map p) := by
  let F := SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}
  let L := DeltaGenerated.deltaGeneratedToTop.{u}
  let qS : E ⨯ B ⟶ B := prod.snd
  let qD : F.obj E ⨯ F.obj B ⟶ F.obj B := prod.snd
  have hqD : TopCat.realizedHornInclusions.{u}.rlp (L.map qD) :=
    coreflectedProductProjection_hornRLP E B
  let c := prodComparison F E B
  let _ : IsIso c := inferInstance
  have hc : c ≫ qD = F.map qS := by
    dsimp [c, qD, qS]
    exact prodComparison_snd F E B
  have hLc := congrArg (fun k => L.map k) hc
  let e : Arrow.mk (L.map (F.map qS)) ≅ Arrow.mk (L.map qD) :=
    Arrow.isoMk (L.mapIso (asIso c)) (Iso.refl _) (by
      change L.map c ≫ L.map qD = L.map (F.map qS) ≫ 𝟙 _
      simpa only [Functor.map_comp, Category.comp_id] using hLc)
  have hFq : TopCat.realizedHornInclusions.{u}.rlp (L.map (F.map qS)) :=
    (TopCat.realizedHornInclusions.rlp.arrow_mk_iso_iff e).mpr hqD
  let Q : MorphismProperty DeltaGenerated.{u} :=
    TopCat.realizedHornInclusions.{u}.rlp.inverseImage L
  have hFq' : Q (F.map qS) := hFq
  have hFp : Q (F.map p) :=
    Q.of_retract ((graphRetract p hp).map F) hFq'
  change TopCat.realizedHornInclusions.{u}.rlp
    (DeltaGenerated.deltaGeneratedToTop.map
      (TopCat.toDeltaGenerated.map (SSet.toTop.map p))) at hFp
  exact (fibration_coreflection_iff (SSet.toTop.map p)).mp hFp

end SSet
