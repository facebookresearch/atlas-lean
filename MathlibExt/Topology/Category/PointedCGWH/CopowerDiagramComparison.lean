/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerIndex
public import MathlibExt.Topology.Category.PointedCGWH.CopowerHomDescent
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Ordinary and copower-enriched pointed diagrams

Ordinary PointedCGWH-valued diagrams and enriched diagrams on the based-discrete copower
index are equivalent categories. Enrichment and restriction preserve every object and
recover every original index map through its generator inclusion. The unit and counit are
natural isomorphisms with identity components, using the stated common pointed-space value
universe.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uI

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace PointedCGWH

variable {I : Type uI} [Category.{w} I]

/-- The actual full native Hom map of an original ordinary diagram. -/
def originalDiagramHomMap (F : I ⥤ PointedCGWH.{u, max v w}) (i j : I) :
    (copowerIndexObj.{u, v, w} I i ⟶[PointedCGWH.{u, max v w}]
        copowerIndexObj.{u, v, w} I j) ⟶
      (ihom (F.obj i)).obj (F.obj j) :=
  copowerHomMap.{u, v, w} (i ⟶ j) (F.obj i) (F.obj j) (fun f => F.map f)

/-- The full Hom map keeps every literal original ordinary arrow. -/
theorem originalDiagramHomMap_generator (F : I ⥤ PointedCGWH.{u, max v w})
    {i j : I} (f : i ⟶ j) :
    basedDiscreteIncl.{u, v, w} (i ⟶ j) f ≫ originalDiagramHomMap.{u, v, w} F i j =
      eHomEquiv PointedCGWH.{u, max v w} (F.map f) :=
  copowerHomMap_generator.{u, v, w} (i ⟶ j) (F.obj i) (F.obj j) _ f

/-- The full native Hom map preserves the original identity injection. -/
theorem originalDiagramHomMap_id (F : I ⥤ PointedCGWH.{u, max v w}) (i : I) :
    eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i) ≫
        originalDiagramHomMap.{u, v, w} F i i =
      eId PointedCGWH.{u, max v w} (F.obj i) := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let D : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (i ⟶ i)
  let H : PointedCGWH.{u, max v w} := (ihom (F.obj i)).obj (F.obj i)
  let u0 : U ⟶ D := eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
  let l : U ⟶ D := basedDiscreteIncl.{u, v, w} (i ⟶ i) (𝟙 i)
  let m : D ⟶ H := originalDiagramHomMap.{u, v, w} F i i
  let eh : (F.obj i ⟶ F.obj i) ≃ (U ⟶ H) := eHomEquiv PointedCGWH.{u, max v w}
  have hId : u0 = l := copowerIndex_id.{u, v, w} I i
  have hGen : l ≫ m = eh (F.map (𝟙 i)) :=
    originalDiagramHomMap_generator.{u, v, w} F (𝟙 i)
  have hMap : eh (F.map (𝟙 i)) = eh (𝟙 (F.obj i)) := congrArg eh (F.map_id i)
  have hNative : eh (𝟙 (F.obj i)) = eId PointedCGWH.{u, max v w} (F.obj i) :=
    eHomEquiv_id PointedCGWH.{u, max v w} (F.obj i)
  exact (congrArg (fun q : U ⟶ D => q ≫ m) hId).trans
    (hGen.trans (hMap.trans hNative))

/-- The full native Hom map preserves composition on the entire original Hom copowers. -/
theorem originalDiagramHomMap_comp (F : I ⥤ PointedCGWH.{u, max v w}) (i j k : I) :
    eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
        (copowerIndexObj.{u, v, w} I j) (copowerIndexObj.{u, v, w} I k) ≫
          originalDiagramHomMap.{u, v, w} F i k =
      (originalDiagramHomMap.{u, v, w} F i j ⊗ₘ
          originalDiagramHomMap.{u, v, w} F j k) ≫
        eComp PointedCGWH.{u, max v w} (F.obj i) (F.obj j) (F.obj k) := by
  apply basedDiscretePair_hom_ext.{u, v, w} (i ⟶ j) (j ⟶ k)
  intro f g
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let E : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (i ⟶ j)
  let G : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (j ⟶ k)
  let D : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (i ⟶ k)
  let H1 : PointedCGWH.{u, max v w} := (ihom (F.obj i)).obj (F.obj j)
  let H2 : PointedCGWH.{u, max v w} := (ihom (F.obj j)).obj (F.obj k)
  let H3 : PointedCGWH.{u, max v w} := (ihom (F.obj i)).obj (F.obj k)
  let p : U ⟶ E ⊗ G := basedDiscretePairIncl.{u, v, w} (i ⟶ j) (j ⟶ k) f g
  let lf : U ⟶ E := basedDiscreteIncl.{u, v, w} (i ⟶ j) f
  let lg : U ⟶ G := basedDiscreteIncl.{u, v, w} (j ⟶ k) g
  let lfg : U ⟶ D := basedDiscreteIncl.{u, v, w} (i ⟶ k) (f ≫ g)
  let c : E ⊗ G ⟶ D := eComp PointedCGWH.{u, max v w}
    (copowerIndexObj.{u, v, w} I i) (copowerIndexObj.{u, v, w} I j)
      (copowerIndexObj.{u, v, w} I k)
  let m1 : E ⟶ H1 := originalDiagramHomMap.{u, v, w} F i j
  let m2 : G ⟶ H2 := originalDiagramHomMap.{u, v, w} F j k
  let m3 : D ⟶ H3 := originalDiagramHomMap.{u, v, w} F i k
  let cc : H1 ⊗ H2 ⟶ H3 := eComp PointedCGWH.{u, max v w} (F.obj i) (F.obj j) (F.obj k)
  let ef : U ⟶ H1 := eHomEquiv PointedCGWH.{u, max v w} (F.map f)
  let eg : U ⟶ H2 := eHomEquiv PointedCGWH.{u, max v w} (F.map g)
  let efg : U ⟶ H3 := eHomEquiv PointedCGWH.{u, max v w} (F.map (f ≫ g))
  let unitPair : U ⟶ U ⊗ U := (λ_ U).inv
  have hSource : p ≫ c = lfg := copowerIndex_comp_generator.{u, v, w} I f g
  have hG1 : lf ≫ m1 = ef := originalDiagramHomMap_generator.{u, v, w} F f
  have hG2 : lg ≫ m2 = eg := originalDiagramHomMap_generator.{u, v, w} F g
  have hG3 : lfg ≫ m3 = efg := originalDiagramHomMap_generator.{u, v, w} F (f ≫ g)
  have hPair : p = unitPair ≫ (lf ⊗ₘ lg) := rfl
  have hTensor : (lf ⊗ₘ lg) ≫ (m1 ⊗ₘ m2) = ef ⊗ₘ eg :=
    (tensorHom_comp_tensorHom lf lg m1 m2).trans
      (congrArg₂ (fun a b => a ⊗ₘ b) hG1 hG2)
  have hT : p ≫ (m1 ⊗ₘ m2) = unitPair ≫ (ef ⊗ₘ eg) :=
    (congrArg (fun q : U ⟶ E ⊗ G => q ≫ (m1 ⊗ₘ m2)) hPair).trans
      ((Category.assoc _ _ _).trans (congrArg (fun q => unitPair ≫ q) hTensor))
  have hMap : efg = eHomEquiv PointedCGWH.{u, max v w} (F.map f ≫ F.map g) :=
    congrArg (fun q : F.obj i ⟶ F.obj k => eHomEquiv PointedCGWH.{u, max v w} q)
      (F.map_comp f g)
  have hOrd : efg = unitPair ≫ (ef ⊗ₘ eg) ≫ cc :=
    hMap.trans (eHomEquiv_comp PointedCGWH.{u, max v w} (F.map f) (F.map g))
  have hLeft : p ≫ (c ≫ m3) = efg :=
    (Category.assoc p c m3).symm.trans
      ((congrArg (fun q : U ⟶ D => q ≫ m3) hSource).trans hG3)
  have hRight : p ≫ ((m1 ⊗ₘ m2) ≫ cc) = efg :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ cc) hT).trans
        ((Category.assoc _ _ _).trans hOrd.symm))
  exact hLeft.trans hRight.symm

/-- Enrich an original ordinary diagram using its actual full native Hom maps. -/
abbrev enrichOriginalDiagram (F : I ⥤ PointedCGWH.{u, max v w}) :
    EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I) where
  toEnrichedFunctor :=
    { obj := fun i => F.obj (show I from i)
      map := fun i j => originalDiagramHomMap.{u, v, w} F i j
      map_id := originalDiagramHomMap_id.{u, v, w} F
      map_comp := originalDiagramHomMap_comp.{u, v, w} F }

/-- The actual enriched diagram retains every original level object. -/
theorem enrichOriginalDiagram_obj (F : I ⥤ PointedCGWH.{u, max v w}) (i : I) :
    (enrichOriginalDiagram.{u, v, w} F).toEnrichedFunctor.obj
        (copowerIndexObj.{u, v, w} I i) = F.obj i := rfl

/-- The actual enriched diagram's generator is the original ordinary arrow. -/
theorem enrichOriginalDiagram_map_generator (F : I ⥤ PointedCGWH.{u, max v w})
    {i j : I} (f : i ⟶ j) :
    basedDiscreteIncl.{u, v, w} (i ⟶ j) f ≫
        (enrichOriginalDiagram.{u, v, w} F).toEnrichedFunctor.map
          (copowerIndexObj.{u, v, w} I i) (copowerIndexObj.{u, v, w} I j) =
      eHomEquiv PointedCGWH.{u, max v w} (F.map f) :=
  originalDiagramHomMap_generator.{u, v, w} F f

/-- Restrict the full genuine enriched diagram along the literal original arrow injections. -/
abbrev restrictCopowerDiagram
    (F : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)) :
    I ⥤ PointedCGWH.{u, max v w} where
  obj i := F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I i)
  map {i j} f := (eHomEquiv PointedCGWH.{u, max v w}).symm
    (basedDiscreteIncl.{u, v, w} (i ⟶ j) f ≫
      F.toEnrichedFunctor.map (copowerIndexObj.{u, v, w} I i)
        (copowerIndexObj.{u, v, w} I j))
  map_id i := by
    apply (eHomEquiv PointedCGWH.{u, max v w}).injective
    rw [Equiv.apply_symm_apply, eHomEquiv_id, ← copowerIndex_id]
    exact F.toEnrichedFunctor.map_id _
  map_comp {i j k} f g := by
    let hi : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I i
    let hj : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I j
    let hk : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I k
    let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
    let E : PointedCGWH.{u, max v w} := hi ⟶[PointedCGWH.{u, max v w}] hj
    let G : PointedCGWH.{u, max v w} := hj ⟶[PointedCGWH.{u, max v w}] hk
    let D : PointedCGWH.{u, max v w} := hi ⟶[PointedCGWH.{u, max v w}] hk
    let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj hi
    let Y : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj hj
    let Z : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj hk
    let H1 : PointedCGWH.{u, max v w} := (ihom X).obj Y
    let H2 : PointedCGWH.{u, max v w} := (ihom Y).obj Z
    let H3 : PointedCGWH.{u, max v w} := (ihom X).obj Z
    let lf : U ⟶ E := basedDiscreteIncl.{u, v, w} (i ⟶ j) f
    let lg : U ⟶ G := basedDiscreteIncl.{u, v, w} (j ⟶ k) g
    let lfg : U ⟶ D := basedDiscreteIncl.{u, v, w} (i ⟶ k) (f ≫ g)
    let p : U ⟶ E ⊗ G := basedDiscretePairIncl.{u, v, w} (i ⟶ j) (j ⟶ k) f g
    let m1 : E ⟶ H1 := F.toEnrichedFunctor.map hi hj
    let m2 : G ⟶ H2 := F.toEnrichedFunctor.map hj hk
    let m3 : D ⟶ H3 := F.toEnrichedFunctor.map hi hk
    let c : E ⊗ G ⟶ D := eComp PointedCGWH.{u, max v w} hi hj hk
    let cc : H1 ⊗ H2 ⟶ H3 := eComp PointedCGWH.{u, max v w} X Y Z
    let d : U ⟶ U ⊗ U := (λ_ U).inv
    let ef : (X ⟶ Y) ≃ (U ⟶ H1) := eHomEquiv PointedCGWH.{u, max v w}
    let eg : (Y ⟶ Z) ≃ (U ⟶ H2) := eHomEquiv PointedCGWH.{u, max v w}
    let efg : (X ⟶ Z) ≃ (U ⟶ H3) := eHomEquiv PointedCGWH.{u, max v w}
    have hSource : p ≫ c = lfg := copowerIndex_comp_generator.{u, v, w} I f g
    have hMap : c ≫ m3 = (m1 ⊗ₘ m2) ≫ cc := F.toEnrichedFunctor.map_comp hi hj hk
    have hPair : p = d ≫ (lf ⊗ₘ lg) := rfl
    have hTensor : (lf ⊗ₘ lg) ≫ (m1 ⊗ₘ m2) = (lf ≫ m1) ⊗ₘ (lg ≫ m2) :=
      tensorHom_comp_tensorHom lf lg m1 m2
    have hT : p ≫ (m1 ⊗ₘ m2) = d ≫ ((lf ≫ m1) ⊗ₘ (lg ≫ m2)) :=
      (congrArg (fun q : U ⟶ E ⊗ G => q ≫ (m1 ⊗ₘ m2)) hPair).trans
        ((Category.assoc _ _ _).trans (congrArg (fun q => d ≫ q) hTensor))
    have hPath : lfg ≫ m3 = d ≫ ((lf ≫ m1) ⊗ₘ (lg ≫ m2)) ≫ cc :=
      (congrArg (fun q : U ⟶ D => q ≫ m3) hSource.symm).trans
        ((Category.assoc p c m3).trans
          ((congrArg (fun q : E ⊗ G ⟶ H3 => p ≫ q) hMap).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun q => q ≫ cc) hT).trans (Category.assoc _ _ _)))))
    have hF : ef (ef.symm (lf ≫ m1)) = lf ≫ m1 := ef.apply_symm_apply _
    have hG : eg (eg.symm (lg ≫ m2)) = lg ≫ m2 := eg.apply_symm_apply _
    have hComp : efg (ef.symm (lf ≫ m1) ≫ eg.symm (lg ≫ m2)) =
        d ≫ ((lf ≫ m1) ⊗ₘ (lg ≫ m2)) ≫ cc :=
      (eHomEquiv_comp PointedCGWH.{u, max v w}
        (ef.symm (lf ≫ m1)) (eg.symm (lg ≫ m2))).trans
          (congrArg (fun q => d ≫ q ≫ cc)
            (congrArg₂ (fun a b => a ⊗ₘ b) hF hG))
    apply efg.injective
    exact (efg.apply_symm_apply (lfg ≫ m3)).trans (hPath.trans hComp.symm)

/-- The original restricted map is precisely the complete native unit-shaped Hom generator. -/
theorem restrictCopowerDiagram_generator
    (F : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I))
    {i j : I} (f : i ⟶ j) :
    eHomEquiv PointedCGWH.{u, max v w} ((restrictCopowerDiagram.{u, v, w} F).map f) =
      basedDiscreteIncl.{u, v, w} (i ⟶ j) f ≫
        F.toEnrichedFunctor.map (copowerIndexObj.{u, v, w} I i)
          (copowerIndexObj.{u, v, w} I j) :=
  (eHomEquiv PointedCGWH.{u, max v w}).apply_symm_apply _

/-- Full enriched Hom action on an original arrow is the original restricted arrow action. -/
theorem restrictCopowerDiagram_action_generator
    (F : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I))
    {i j : I} (f : i ⟶ j) :
    (F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I i) ◁
        basedDiscreteIncl.{u, v, w} (i ⟶ j) f) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map (copowerIndexObj.{u, v, w} I i)
        (copowerIndexObj.{u, v, w} I j)) =
      (ρ_ (F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I i))).hom ≫
        (restrictCopowerDiagram.{u, v, w} F).map f := by
  let X : PointedCGWH.{u, max v w} :=
    F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I i)
  let Y : PointedCGWH.{u, max v w} :=
    F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I j)
  let G : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (i ⟶ j)
  let l : 𝟙_ PointedCGWH.{u, max v w} ⟶ G :=
    basedDiscreteIncl.{u, v, w} (i ⟶ j) f
  let m : G ⟶ (ihom X).obj Y :=
    F.toEnrichedFunctor.map (copowerIndexObj.{u, v, w} I i)
      (copowerIndexObj.{u, v, w} I j)
  let d : X ⟶ Y := (restrictCopowerDiagram.{u, v, w} F).map f
  have h : eHomEquiv PointedCGWH.{u, max v w} d = l ≫ m :=
    restrictCopowerDiagram_generator.{u, v, w} F f
  have hc : MonoidalClosed.uncurry (eHomEquiv PointedCGWH.{u, max v w} d) =
      (ρ_ X).hom ≫ d := by
    change MonoidalClosed.uncurry (MonoidalClosed.curry ((ρ_ X).hom ≫ d)) = _
    exact MonoidalClosed.uncurry_curry _
  change (X ◁ l) ≫ MonoidalClosed.uncurry m = (ρ_ X).hom ≫ d
  exact (MonoidalClosed.uncurry_natural_left l m).symm.trans
    ((congrArg MonoidalClosed.uncurry h).symm.trans hc)

/-- Restriction of the actual original-diagram enrichment keeps every ordinary arrow. -/
theorem restrict_enrichOriginalDiagram_map
    (F : I ⥤ PointedCGWH.{u, max v w}) {i j : I} (f : i ⟶ j) :
    (restrictCopowerDiagram.{u, v, w} (enrichOriginalDiagram.{u, v, w} F)).map f =
      F.map f := by
  apply (eHomEquiv PointedCGWH.{u, max v w}).injective
  exact (restrictCopowerDiagram_generator.{u, v, w}
    (enrichOriginalDiagram.{u, v, w} F) f).trans
      (enrichOriginalDiagram_map_generator.{u, v, w} F f)

/-- Enrichment of a restricted genuine diagram recovers its complete enriched Hom map. -/
theorem enrich_restrictCopowerDiagram_map
    (F : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I))
    (i j : I) :
    (enrichOriginalDiagram.{u, v, w} (restrictCopowerDiagram.{u, v, w} F)).toEnrichedFunctor.map
        (copowerIndexObj.{u, v, w} I i) (copowerIndexObj.{u, v, w} I j) =
      F.toEnrichedFunctor.map (copowerIndexObj.{u, v, w} I i)
        (copowerIndexObj.{u, v, w} I j) := by
  apply copowerHomMap_hom_ext.{u, v, w} (i ⟶ j)
    (F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I i))
    (F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I j))
  intro f
  exact (enrichOriginalDiagram_map_generator.{u, v, w}
    (restrictCopowerDiagram.{u, v, w} F) f).trans
      (restrictCopowerDiagram_generator.{u, v, w} F f)

/-- Original ordinary naturality gives the complete uncurried native Hom-object square. -/
theorem enrichOriginalDiagram_uncurried_naturality
    {F G : I ⥤ PointedCGWH.{u, max v w}} (a : F ⟶ G) (i j : I) :
    MonoidalClosed.uncurry (originalDiagramHomMap.{u, v, w} F i j) ≫ a.app j =
      (a.app i ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} (i ⟶ j))) ≫
        MonoidalClosed.uncurry (originalDiagramHomMap.{u, v, w} G i j) := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let X : PointedCGWH.{u, max v w} := F.obj i
  let Y : PointedCGWH.{u, max v w} := G.obj i
  let Z : PointedCGWH.{u, max v w} := G.obj j
  let H : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (i ⟶ j)
  let q : X ⟶ Y := a.app i
  let r : F.obj j ⟶ Z := a.app j
  let mf : H ⟶ (ihom X).obj (F.obj j) := originalDiagramHomMap.{u, v, w} F i j
  let mg : H ⟶ (ihom Y).obj Z := originalDiagramHomMap.{u, v, w} G i j
  let fm : X ⊗ H ⟶ F.obj j := MonoidalClosed.uncurry mf
  let gm : Y ⊗ H ⟶ Z := MonoidalClosed.uncurry mg
  apply (isColimitOfPreserves (tensorLeft X)
    (basedDiscreteCofanIsColimit.{u, v, w} (i ⟶ j))).hom_ext
  intro f
  let l : U ⟶ H := basedDiscreteIncl.{u, v, w} (i ⟶ j) f.as
  let leg : X ⊗ U ⟶ X ⊗ H :=
    ((tensorLeft X).mapCocone (basedDiscreteCofan.{u, v, w} (i ⟶ j))).ι.app f
  have hLeg : leg = X ◁ l := rfl
  have hFGen : l ≫ mf = eHomEquiv PointedCGWH.{u, max v w} (F.map f.as) :=
    originalDiagramHomMap_generator.{u, v, w} F f.as
  have hGGen : l ≫ mg = eHomEquiv PointedCGWH.{u, max v w} (G.map f.as) :=
    originalDiagramHomMap_generator.{u, v, w} G f.as
  have hFCurry :
      MonoidalClosed.uncurry (eHomEquiv PointedCGWH.{u, max v w} (F.map f.as)) =
        (ρ_ X).hom ≫ F.map f.as := by
    change MonoidalClosed.uncurry (MonoidalClosed.curry ((ρ_ X).hom ≫ F.map f.as)) = _
    exact MonoidalClosed.uncurry_curry _
  have hGCurry :
      MonoidalClosed.uncurry (eHomEquiv PointedCGWH.{u, max v w} (G.map f.as)) =
        (ρ_ Y).hom ≫ G.map f.as := by
    change MonoidalClosed.uncurry (MonoidalClosed.curry ((ρ_ Y).hom ≫ G.map f.as)) = _
    exact MonoidalClosed.uncurry_curry _
  have hF : (X ◁ l) ≫ fm = (ρ_ X).hom ≫ F.map f.as :=
    (MonoidalClosed.uncurry_natural_left l mf).symm.trans
      ((congrArg MonoidalClosed.uncurry hFGen).trans hFCurry)
  have hG : (Y ◁ l) ≫ gm = (ρ_ Y).hom ≫ G.map f.as :=
    (MonoidalClosed.uncurry_natural_left l mg).symm.trans
      ((congrArg MonoidalClosed.uncurry hGGen).trans hGCurry)
  have hExchange : (X ◁ l) ≫ (q ▷ H) = (q ▷ U) ≫ (Y ◁ l) := whisker_exchange q l
  have hNatural : F.map f.as ≫ r = q ≫ G.map f.as := a.naturality f.as
  have hUnit : (q ▷ U) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ q := rightUnitor_naturality q
  have hTensor : q ⊗ₘ 𝟙 H = q ▷ H := tensorHom_id q H
  have hLeft0 : (X ◁ l) ≫ (fm ≫ r) = (ρ_ X).hom ≫ q ≫ G.map f.as :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ r) hF).trans
        ((Category.assoc _ _ _).trans (congrArg (fun t => (ρ_ X).hom ≫ t) hNatural)))
  have hRight0 : (X ◁ l) ≫ ((q ▷ H) ≫ gm) = (ρ_ X).hom ≫ q ≫ G.map f.as :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ gm) hExchange).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => (q ▷ U) ≫ t) hG).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun t => t ≫ G.map f.as) hUnit).trans
                (Category.assoc (ρ_ X).hom q (G.map f.as)))))))
  have hLeft : leg ≫ (fm ≫ r) = (ρ_ X).hom ≫ q ≫ G.map f.as :=
    (congrArg (fun t => t ≫ (fm ≫ r)) hLeg).trans hLeft0
  have hRight : leg ≫ ((q ⊗ₘ 𝟙 H) ≫ gm) = (ρ_ X).hom ≫ q ≫ G.map f.as :=
    (congrArg (fun t => leg ≫ (t ≫ gm)) hTensor).trans
      ((congrArg (fun t => t ≫ ((q ▷ H) ≫ gm)) hLeg).trans hRight0)
  exact hLeft.trans hRight.symm

/-- Enrich an actual ordinary transformation without changing its components. -/
abbrev enrichOriginalDiagramMap {F G : I ⥤ PointedCGWH.{u, max v w}} (a : F ⟶ G) :
    enrichOriginalDiagram.{u, v, w} F ⟶ enrichOriginalDiagram.{u, v, w} G :=
  GradedNatTrans.unitOfComponents (fun i => a.app (show I from i))
    (fun i j => enrichOriginalDiagram_uncurried_naturality.{u, v, w} a i j)

/-- Every component of the genuine transformation is the original ordinary component. -/
theorem enrichOriginalDiagramMap_component {F G : I ⥤ PointedCGWH.{u, max v w}}
    (a : F ⟶ G) (i : I) :
    EnrichedFunctorCat.component (enrichOriginalDiagramMap.{u, v, w} a)
      (copowerIndexObj.{u, v, w} I i) = a.app i :=
  GradedNatTrans.unitOfComponents_component _ _ _

/-- The actual forward functor retains full Hom maps and original transformation components. -/
abbrev enrichOriginalDiagramFunctor :
    (I ⥤ PointedCGWH.{u, max v w}) ⥤
      EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I) where
  obj := enrichOriginalDiagram.{u, v, w}
  map := enrichOriginalDiagramMap.{u, v, w}
  map_id F := by
    apply EnrichedFunctorCat.hom_ext
    intro i
    let i0 : I := i
    have hMap : EnrichedFunctorCat.component (enrichOriginalDiagramMap.{u, v, w} (𝟙 F)) i =
        𝟙 (F.obj i0) := enrichOriginalDiagramMap_component.{u, v, w} (𝟙 F) i0
    have hId : EnrichedFunctorCat.component (𝟙 (enrichOriginalDiagram.{u, v, w} F)) i =
        𝟙 (F.obj i0) := EnrichedFunctorCat.component_id _ i
    exact hMap.trans hId.symm
  map_comp {F G H} a b := by
    apply EnrichedFunctorCat.hom_ext
    intro i
    let i0 : I := i
    have hA := enrichOriginalDiagramMap_component.{u, v, w} a i0
    have hB := enrichOriginalDiagramMap_component.{u, v, w} b i0
    have hAB : EnrichedFunctorCat.component (enrichOriginalDiagramMap.{u, v, w} (a ≫ b)) i =
        a.app i0 ≫ b.app i0 := enrichOriginalDiagramMap_component.{u, v, w} (a ≫ b) i0
    have hComp : EnrichedFunctorCat.component
        (enrichOriginalDiagramMap.{u, v, w} a ≫ enrichOriginalDiagramMap.{u, v, w} b) i =
        a.app i0 ≫ b.app i0 :=
      (EnrichedFunctorCat.component_comp _ _ i).trans
        (congrArg₂ (fun f : F.obj i0 ⟶ G.obj i0 => fun g : G.obj i0 ⟶ H.obj i0 => f ≫ g) hA hB)
    exact hAB.trans hComp.symm

/-- Restrict a full genuine transformation using its unchanged actual ordinary components. -/
abbrev restrictCopowerDiagramMap
    {F G : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)}
    (a : F ⟶ G) : restrictCopowerDiagram.{u, v, w} F ⟶ restrictCopowerDiagram.{u, v, w} G where
  app i := EnrichedFunctorCat.component a (copowerIndexObj.{u, v, w} I i)
  naturality {i j} f := by
    let hi : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I i
    let hj : CopowerIndex.{u, v, w} I := copowerIndexObj.{u, v, w} I j
    let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
    let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj hi
    let Y : PointedCGWH.{u, max v w} := G.toEnrichedFunctor.obj hi
    let H : PointedCGWH.{u, max v w} := hi ⟶[PointedCGWH.{u, max v w}] hj
    let l : U ⟶ H := basedDiscreteIncl.{u, v, w} (i ⟶ j) f
    let q : X ⟶ Y := EnrichedFunctorCat.component a hi
    let r : F.toEnrichedFunctor.obj hj ⟶ G.toEnrichedFunctor.obj hj :=
      EnrichedFunctorCat.component a hj
    let fm : X ⊗ H ⟶ F.toEnrichedFunctor.obj hj :=
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map hi hj)
    let gm : Y ⊗ H ⟶ G.toEnrichedFunctor.obj hj :=
      MonoidalClosed.uncurry (G.toEnrichedFunctor.map hi hj)
    let df : X ⟶ F.toEnrichedFunctor.obj hj := (restrictCopowerDiagram.{u, v, w} F).map f
    let dg : Y ⟶ G.toEnrichedFunctor.obj hj := (restrictCopowerDiagram.{u, v, w} G).map f
    have hF : (X ◁ l) ≫ fm = (ρ_ X).hom ≫ df :=
      restrictCopowerDiagram_action_generator.{u, v, w} F f
    have hG : (Y ◁ l) ≫ gm = (ρ_ Y).hom ≫ dg :=
      restrictCopowerDiagram_action_generator.{u, v, w} G f
    have hNative : fm ≫ r = (q ⊗ₘ 𝟙 H) ≫ gm := a.uncurriedNaturality hi hj
    have hTensor : q ⊗ₘ 𝟙 H = q ▷ H := tensorHom_id q H
    have hNatural : fm ≫ r = (q ▷ H) ≫ gm :=
      hNative.trans (congrArg (fun t => t ≫ gm) hTensor)
    have hExchange : (X ◁ l) ≫ (q ▷ H) = (q ▷ U) ≫ (Y ◁ l) :=
      whisker_exchange q l
    have hUnit : (q ▷ U) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ q := rightUnitor_naturality q
    apply (cancel_epi (ρ_ X).hom).1
    have hLeft : (ρ_ X).hom ≫ (df ≫ r) = (X ◁ l) ≫ (fm ≫ r) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ r) hF.symm).trans (Category.assoc _ _ _))
    have hMiddle : (X ◁ l) ≫ (fm ≫ r) = (q ▷ U) ≫ (Y ◁ l) ≫ gm :=
      (congrArg (fun t => (X ◁ l) ≫ t) hNatural).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ gm) hExchange).trans (Category.assoc _ _ _)))
    have hRight : (q ▷ U) ≫ (Y ◁ l) ≫ gm = (ρ_ X).hom ≫ (q ≫ dg) :=
      (congrArg (fun t => (q ▷ U) ≫ t) hG).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ dg) hUnit).trans (Category.assoc _ _ _)))
    exact hLeft.trans (hMiddle.trans hRight)

/-- Restriction on transformations retains each original level component. -/
theorem restrictCopowerDiagramMap_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)}
    (a : F ⟶ G) (i : I) :
    (restrictCopowerDiagramMap.{u, v, w} a).app i =
      EnrichedFunctorCat.component a (copowerIndexObj.{u, v, w} I i) := rfl

/-- The actual reverse functor preserves the original enriched unit-graded components. -/
abbrev restrictCopowerDiagramFunctor :
    EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I) ⥤
      (I ⥤ PointedCGWH.{u, max v w}) where
  obj := restrictCopowerDiagram.{u, v, w}
  map := restrictCopowerDiagramMap.{u, v, w}
  map_id F := by
    apply NatTrans.ext
    funext i
    exact EnrichedFunctorCat.component_id F (copowerIndexObj.{u, v, w} I i)
  map_comp {F G H} a b := by
    apply NatTrans.ext
    funext i
    exact EnrichedFunctorCat.component_comp a b (copowerIndexObj.{u, v, w} I i)

/-- Restriction after actual enrichment is the identity through the original level identities. -/
def originalDiagramUnitIso (F : I ⥤ PointedCGWH.{u, max v w}) :
    F ≅ restrictCopowerDiagram.{u, v, w} (enrichOriginalDiagram.{u, v, w} F) :=
  NatIso.ofComponents (fun i => Iso.refl (F.obj i)) (by
    intro i j f
    change F.map f ≫ 𝟙 _ = 𝟙 _ ≫
      (restrictCopowerDiagram.{u, v, w} (enrichOriginalDiagram.{u, v, w} F)).map f
    rw [Category.comp_id, Category.id_comp, restrict_enrichOriginalDiagram_map])

/-- The complete genuine Hom reconstruction gives the actual identity-component counit. -/
def copowerDiagramCounitIso
    (F : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)) :
    enrichOriginalDiagram.{u, v, w} (restrictCopowerDiagram.{u, v, w} F) ≅ F := by
  let R := enrichOriginalDiagram.{u, v, w} (restrictCopowerDiagram.{u, v, w} F)
  let hom : R ⟶ F := GradedNatTrans.unitOfComponents (fun i => 𝟙 (F.toEnrichedFunctor.obj i))
    (fun i j => by
      let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj i
      let Y : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj j
      let H : PointedCGWH.{u, max v w} := i ⟶[PointedCGWH.{u, max v w}] j
      let rm : H ⟶ (ihom X).obj Y := R.toEnrichedFunctor.map i j
      let fm : H ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map i j
      have h : rm = fm := enrich_restrictCopowerDiagram_map.{u, v, w} F i j
      have hu : MonoidalClosed.uncurry rm = MonoidalClosed.uncurry fm :=
        congrArg MonoidalClosed.uncurry h
      have hLeft : MonoidalClosed.uncurry rm ≫ 𝟙 Y = MonoidalClosed.uncurry fm :=
        (Category.comp_id _).trans hu
      have hTensor : 𝟙 X ⊗ₘ 𝟙 H = 𝟙 (X ⊗ H) := id_tensorHom_id X H
      have hRight : (𝟙 X ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry fm = MonoidalClosed.uncurry fm :=
        (congrArg (fun q => q ≫ MonoidalClosed.uncurry fm) hTensor).trans
          (Category.id_comp _)
      exact hLeft.trans hRight.symm)
  let inv : F ⟶ R := GradedNatTrans.unitOfComponents (fun i => 𝟙 (F.toEnrichedFunctor.obj i))
    (fun i j => by
      let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj i
      let Y : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj j
      let H : PointedCGWH.{u, max v w} := i ⟶[PointedCGWH.{u, max v w}] j
      let rm : H ⟶ (ihom X).obj Y := R.toEnrichedFunctor.map i j
      let fm : H ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map i j
      have h : rm = fm := enrich_restrictCopowerDiagram_map.{u, v, w} F i j
      have hu : MonoidalClosed.uncurry rm = MonoidalClosed.uncurry fm :=
        congrArg MonoidalClosed.uncurry h
      have hLeft : MonoidalClosed.uncurry fm ≫ 𝟙 Y = MonoidalClosed.uncurry rm :=
        (Category.comp_id _).trans hu.symm
      have hTensor : 𝟙 X ⊗ₘ 𝟙 H = 𝟙 (X ⊗ H) := id_tensorHom_id X H
      have hRight : (𝟙 X ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry rm = MonoidalClosed.uncurry rm :=
        (congrArg (fun q => q ≫ MonoidalClosed.uncurry rm) hTensor).trans
          (Category.id_comp _)
      exact hLeft.trans hRight.symm)
  have hh (i : CopowerIndex.{u, v, w} I) :
      EnrichedFunctorCat.component hom i = 𝟙 (F.toEnrichedFunctor.obj i) :=
    GradedNatTrans.unitOfComponents_component _ _ i
  have hi (i : CopowerIndex.{u, v, w} I) :
      EnrichedFunctorCat.component inv i = 𝟙 (F.toEnrichedFunctor.obj i) :=
    GradedNatTrans.unitOfComponents_component _ _ i
  refine { hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply EnrichedFunctorCat.hom_ext
    intro i
    let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj i
    have hComp : EnrichedFunctorCat.component (hom ≫ inv) i = 𝟙 X ≫ 𝟙 X :=
      (EnrichedFunctorCat.component_comp hom inv i).trans
        (congrArg₂ (fun a : X ⟶ X => fun b : X ⟶ X => a ≫ b) (hh i) (hi i))
    have hId : EnrichedFunctorCat.component (𝟙 R) i = 𝟙 X :=
      EnrichedFunctorCat.component_id R i
    exact hComp.trans ((Category.id_comp (𝟙 X)).trans hId.symm)
  · apply EnrichedFunctorCat.hom_ext
    intro i
    let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj i
    have hComp : EnrichedFunctorCat.component (inv ≫ hom) i = 𝟙 X ≫ 𝟙 X :=
      (EnrichedFunctorCat.component_comp inv hom i).trans
        (congrArg₂ (fun a : X ⟶ X => fun b : X ⟶ X => a ≫ b) (hi i) (hh i))
    have hId : EnrichedFunctorCat.component (𝟙 F) i = 𝟙 X :=
      EnrichedFunctorCat.component_id F i
    exact hComp.trans ((Category.id_comp (𝟙 X)).trans hId.symm)

/-- The original ordinary reconstruction unit is literally identity at every level. -/
theorem originalDiagramUnitIso_hom_app (F : I ⥤ PointedCGWH.{u, max v w}) (i : I) :
    (originalDiagramUnitIso.{u, v, w} F).hom.app i = 𝟙 (F.obj i) := rfl

/-- The genuine reconstructed Hom counit is literally identity at every level. -/
theorem copowerDiagramCounitIso_hom_component
    (F : EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)) (i : I) :
    EnrichedFunctorCat.component (copowerDiagramCounitIso.{u, v, w} F).hom
      (copowerIndexObj.{u, v, w} I i) =
      𝟙 (F.toEnrichedFunctor.obj (copowerIndexObj.{u, v, w} I i)) := by
  dsimp only [copowerDiagramCounitIso]
  exact GradedNatTrans.unitOfComponents_component _ _ _

/-- Original level identities form the full natural reconstruction unit. -/
def originalDiagramUnitNatIso :
    𝟭 (I ⥤ PointedCGWH.{u, max v w}) ≅
      enrichOriginalDiagramFunctor.{u, v, w} ⋙ restrictCopowerDiagramFunctor.{u, v, w} :=
  NatIso.ofComponents (originalDiagramUnitIso.{u, v, w}) (by
    intro F G a
    apply NatTrans.ext
    funext i
    let f : F.obj i ⟶ G.obj i := a.app i
    have hUF : (originalDiagramUnitIso.{u, v, w} F).hom.app i = 𝟙 (F.obj i) :=
      originalDiagramUnitIso_hom_app.{u, v, w} F i
    have hUG : (originalDiagramUnitIso.{u, v, w} G).hom.app i = 𝟙 (G.obj i) :=
      originalDiagramUnitIso_hom_app.{u, v, w} G i
    have hMap : EnrichedFunctorCat.component (enrichOriginalDiagramMap.{u, v, w} a)
        (copowerIndexObj.{u, v, w} I i) = f := enrichOriginalDiagramMap_component.{u, v, w} a i
    have hL : f ≫ (originalDiagramUnitIso.{u, v, w} G).hom.app i = f :=
      (congrArg (fun q : G.obj i ⟶ G.obj i => f ≫ q) hUG).trans (Category.comp_id f)
    have hR : (originalDiagramUnitIso.{u, v, w} F).hom.app i ≫
        EnrichedFunctorCat.component (enrichOriginalDiagramMap.{u, v, w} a)
          (copowerIndexObj.{u, v, w} I i) = f :=
      (congrArg₂ (fun p : F.obj i ⟶ F.obj i => fun q : F.obj i ⟶ G.obj i => p ≫ q)
        hUF hMap).trans (Category.id_comp f)
    exact hL.trans hR.symm)

/-- The complete genuine reconstructed Hom maps form the full natural counit. -/
def copowerDiagramCounitNatIso :
    restrictCopowerDiagramFunctor.{u, v, w} ⋙ enrichOriginalDiagramFunctor.{u, v, w} ≅
      𝟭 (EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I)) :=
  NatIso.ofComponents (copowerDiagramCounitIso.{u, v, w}) (by
    intro F G a
    apply EnrichedFunctorCat.hom_ext
    intro i
    let i0 : I := i
    let X : PointedCGWH.{u, max v w} := F.toEnrichedFunctor.obj i
    let Y : PointedCGWH.{u, max v w} := G.toEnrichedFunctor.obj i
    let f : X ⟶ Y := EnrichedFunctorCat.component a i
    have hMap : EnrichedFunctorCat.component
        (enrichOriginalDiagramMap.{u, v, w} (restrictCopowerDiagramMap.{u, v, w} a)) i = f :=
      (enrichOriginalDiagramMap_component.{u, v, w}
        (restrictCopowerDiagramMap.{u, v, w} a) i0).trans
          (restrictCopowerDiagramMap_component.{u, v, w} a i0)
    have hF : EnrichedFunctorCat.component (copowerDiagramCounitIso.{u, v, w} F).hom i =
        𝟙 X := copowerDiagramCounitIso_hom_component.{u, v, w} F i0
    have hG : EnrichedFunctorCat.component (copowerDiagramCounitIso.{u, v, w} G).hom i =
        𝟙 Y := copowerDiagramCounitIso_hom_component.{u, v, w} G i0
    have hL : EnrichedFunctorCat.component
        (enrichOriginalDiagramMap.{u, v, w} (restrictCopowerDiagramMap.{u, v, w} a) ≫
          (copowerDiagramCounitIso.{u, v, w} G).hom) i = f :=
      (EnrichedFunctorCat.component_comp _ _ i).trans
        ((congrArg₂ (fun p : X ⟶ Y => fun q : Y ⟶ Y => p ≫ q) hMap hG).trans
          (Category.comp_id f))
    have hR : EnrichedFunctorCat.component ((copowerDiagramCounitIso.{u, v, w} F).hom ≫ a) i = f :=
      (EnrichedFunctorCat.component_comp _ _ i).trans
        ((congrArg₂ (fun p : X ⟶ X => fun q : X ⟶ Y => p ≫ q) hF rfl).trans
          (Category.id_comp f))
    exact hL.trans hR.symm)

/-- Actual original diagrams and genuine full native copower-enriched diagrams are equivalent. -/
def copowerDiagramEquivalence :
    (I ⥤ PointedCGWH.{u, max v w}) ≌
      EnrichedFunctorCat PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I) where
  functor := enrichOriginalDiagramFunctor.{u, v, w}
  inverse := restrictCopowerDiagramFunctor.{u, v, w}
  unitIso := originalDiagramUnitNatIso.{u, v, w}
  counitIso := copowerDiagramCounitNatIso.{u, v, w}
  functor_unitIso_comp F := by
    apply EnrichedFunctorCat.hom_ext
    intro i
    let i0 : I := i
    let X : PointedCGWH.{u, max v w} := F.obj i0
    have hU : EnrichedFunctorCat.component
        (enrichOriginalDiagramMap.{u, v, w} (originalDiagramUnitIso.{u, v, w} F).hom) i =
        𝟙 X :=
      (enrichOriginalDiagramMap_component.{u, v, w}
        (originalDiagramUnitIso.{u, v, w} F).hom i0).trans
          (originalDiagramUnitIso_hom_app.{u, v, w} F i0)
    have hC : EnrichedFunctorCat.component
        (copowerDiagramCounitIso.{u, v, w} (enrichOriginalDiagram.{u, v, w} F)).hom i =
        𝟙 X := copowerDiagramCounitIso_hom_component.{u, v, w}
          (enrichOriginalDiagram.{u, v, w} F) i0
    have hLeft : EnrichedFunctorCat.component
        (enrichOriginalDiagramMap.{u, v, w} (originalDiagramUnitIso.{u, v, w} F).hom ≫
          (copowerDiagramCounitIso.{u, v, w} (enrichOriginalDiagram.{u, v, w} F)).hom) i =
        𝟙 X :=
      (EnrichedFunctorCat.component_comp _ _ i).trans
        ((congrArg₂ (fun p : X ⟶ X => fun q : X ⟶ X => p ≫ q) hU hC).trans
          (Category.id_comp (𝟙 X)))
    have hRight : EnrichedFunctorCat.component (𝟙 (enrichOriginalDiagram.{u, v, w} F)) i =
        𝟙 X := EnrichedFunctorCat.component_id _ i
    exact hLeft.trans hRight.symm

end PointedCGWH
