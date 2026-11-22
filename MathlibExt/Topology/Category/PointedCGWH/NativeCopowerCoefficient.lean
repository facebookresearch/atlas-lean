/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerMonoidalData
public import MathlibExt.Topology.Category.PointedCGWH.CopowerDiagramComparison
public import MathlibExt.CategoryTheory.Enriched.Monoidal.Functor
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereSequence

/-!
# Enriching monoidal pointed diagrams by copowers

Enriches an ordinary pointed-space diagram along its copower index category. Lax and strong monoidal structures lift with the same unit and tensor maps. For the sphere diagram, these maps agree with the unit and multiplication of its Day monoid.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uI

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open scoped CategoryTheory.MonoidalClosed

namespace PointedCGWH

attribute [local instance] copowerUnderlyingEnrichedOrdinary

variable {I : Type uI} [Category.{w} I]

/-- The same full original diagram on the associated copower category. -/
abbrev enrichOriginalMonoidalDiagram (F : I ⥤ PointedCGWH.{u, max v w}) :
    EnrichedFunctor PointedCGWH.{u, max v w} (CopowerUnderlying.{u, v, w} I)
      PointedCGWH.{u, max v w} :=
  (enrichOriginalDiagram.{u, v, w} F).toEnrichedFunctor

/-- The unit-graded map of an original arrow keeps that original diagram map. -/
private theorem originalCoefficientMap
    (F : I ⥤ PointedCGWH.{u, max v w}) {i j : I} (f : i ⟶ j) :
    (eHomEquiv PointedCGWH.{u, max v w}).symm
        (eHomEquiv PointedCGWH.{u, max v w} ((copowerRestriction.{u, v, w} I).map f) ≫
          (enrichOriginalMonoidalDiagram.{u, v, w} F).map
            ((copowerRestriction.{u, v, w} I).obj i)
            ((copowerRestriction.{u, v, w} I).obj j)) = F.map f := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let E : V := basedDiscreteObj.{u, v, w} (i ⟶ j)
  let H : V := (ihom (F.obj i)).obj (F.obj j)
  let m : E ⟶ H := originalDiagramHomMap.{u, v, w} F i j
  let l : U ⟶ E := basedDiscreteIncl.{u, v, w} (i ⟶ j) f
  let eh : (F.obj i ⟶ F.obj j) ≃ (U ⟶ H) := eHomEquiv V
  have hRestriction : eHomEquiv V ((copowerRestriction.{u, v, w} I).map f) = l :=
    copowerRestriction_map.{u, v, w} I f
  have hGenerator : l ≫ m = eh (F.map f) :=
    originalDiagramHomMap_generator.{u, v, w} F f
  have hWhole : eHomEquiv V ((copowerRestriction.{u, v, w} I).map f) ≫ m =
      eh (F.map f) :=
    (congrArg (fun z : U ⟶ E => z ≫ m) hRestriction).trans hGenerator
  change eh.symm (eHomEquiv V ((copowerRestriction.{u, v, w} I).map f) ≫ m) = F.map f
  exact (congrArg eh.symm hWhole).trans (eh.symm_apply_apply (F.map f))

section MonoidalIndex

variable [MonoidalCategory I]

attribute [local instance] copowerUnderlyingMonoidal

variable (F : I ⥤ PointedCGWH.{u, max v w}) [F.LaxMonoidal]

/-- The original tensorator is natural on the complete native Hom objects. -/
theorem enrichOriginalMonoidalDiagram_mu_naturality (i i' j j' : I) :
    (originalDiagramHomMap.{u, v, w} F i i' ⊗ₘ
        originalDiagramHomMap.{u, v, w} F j j') ≫
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, max v w}).tensorMap
        (F.obj i) (F.obj i') (F.obj j) (F.obj j') ≫
      eHomWhiskerLeft PointedCGWH.{u, max v w} (F.obj i ⊗ F.obj j) (μ F i' j') =
    copowerTensorHom.{u, v, w} I i i' j j' ≫
      originalDiagramHomMap.{u, v, w} F (i ⊗ j) (i' ⊗ j') ≫
      eHomWhiskerRight PointedCGWH.{u, max v w} (μ F i j) (F.obj (i' ⊗ j')) := by
  apply basedDiscretePair_hom_ext.{u, v, w} (i ⟶ i') (j ⟶ j')
  intro f g
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let E : V := basedDiscreteObj.{u, v, w} (i ⟶ i')
  let G : V := basedDiscreteObj.{u, v, w} (j ⟶ j')
  let D : V := basedDiscreteObj.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j'))
  let A : V := F.obj i ⊗ F.obj j
  let A' : V := F.obj i' ⊗ F.obj j'
  let B : V := F.obj (i ⊗ j)
  let B' : V := F.obj (i' ⊗ j')
  let Hf : V := (ihom (F.obj i)).obj (F.obj i')
  let Hg : V := (ihom (F.obj j)).obj (F.obj j')
  let Ht : V := (ihom A).obj A'
  let Hm : V := (ihom B).obj B'
  let H : V := (ihom A).obj B'
  let p : U ⟶ E ⊗ G := basedDiscretePairIncl.{u, v, w} (i ⟶ i') (j ⟶ j') f g
  let lf : U ⟶ E := basedDiscreteIncl.{u, v, w} (i ⟶ i') f
  let lg : U ⟶ G := basedDiscreteIncl.{u, v, w} (j ⟶ j') g
  let lt : U ⟶ D := basedDiscreteIncl.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j')) (f ⊗ₘ g)
  let mf : E ⟶ Hf := originalDiagramHomMap.{u, v, w} F i i'
  let mg : G ⟶ Hg := originalDiagramHomMap.{u, v, w} F j j'
  let mt : D ⟶ Hm := originalDiagramHomMap.{u, v, w} F (i ⊗ j) (i' ⊗ j')
  let ef : U ⟶ Hf := eHomEquiv V (F.map f)
  let eg : U ⟶ Hg := eHomEquiv V (F.map g)
  let et : U ⟶ Ht := eHomEquiv V (F.map f ⊗ₘ F.map g)
  let em : U ⟶ Hm := eHomEquiv V (F.map (f ⊗ₘ g))
  let t : E ⊗ G ⟶ D := copowerTensorHom.{u, v, w} I i i' j j'
  let td : Hf ⊗ Hg ⟶ Ht :=
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
      (F.obj i) (F.obj i') (F.obj j) (F.obj j')
  let wl : Ht ⟶ H := eHomWhiskerLeft V A (μ F i' j')
  let wr : Hm ⟶ H := eHomWhiskerRight V (μ F i j) B'
  let delta : U ⟶ U ⊗ U := (λ_ U).inv
  have hF : lf ≫ mf = ef := originalDiagramHomMap_generator.{u, v, w} F f
  have hG : lg ≫ mg = eg := originalDiagramHomMap_generator.{u, v, w} F g
  have hPair : p = delta ≫ (lf ⊗ₘ lg) := rfl
  have hTensor : (lf ⊗ₘ lg) ≫ (mf ⊗ₘ mg) = ef ⊗ₘ eg :=
    (tensorHom_comp_tensorHom lf lg mf mg).trans
      (congrArg₂ (fun a b => a ⊗ₘ b) hF hG)
  have hPairMap : p ≫ (mf ⊗ₘ mg) = delta ≫ (ef ⊗ₘ eg) :=
    (congrArg (fun z : U ⟶ E ⊗ G => z ≫ (mf ⊗ₘ mg)) hPair).trans
      ((Category.assoc delta (lf ⊗ₘ lg) (mf ⊗ₘ mg)).trans
        (congrArg (fun z => delta ≫ z) hTensor))
  have hNativeTensor : delta ≫ (ef ⊗ₘ eg) ≫ td = et :=
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap_eHomEquiv
      (F.map f) (F.map g)
  have hLeftPre : p ≫ ((mf ⊗ₘ mg) ≫ td) = et :=
    (Category.assoc p (mf ⊗ₘ mg) td).symm.trans
      ((congrArg (fun z => z ≫ td) hPairMap).trans
        ((Category.assoc delta (ef ⊗ₘ eg) td).trans hNativeTensor))
  have hLeftWhisker : et ≫ wl = eHomEquiv V ((F.map f ⊗ₘ F.map g) ≫ μ F i' j') :=
    eHomEquiv_comp_eHomWhiskerLeft (V := V) (C := V)
      (F.map f ⊗ₘ F.map g) (μ F i' j')
  have hLeft : p ≫ ((mf ⊗ₘ mg) ≫ td ≫ wl) =
      eHomEquiv V ((F.map f ⊗ₘ F.map g) ≫ μ F i' j') := by
    simpa only [Category.assoc] using
      (Category.assoc p ((mf ⊗ₘ mg) ≫ td) wl).symm.trans
        ((congrArg (fun z => z ≫ wl) hLeftPre).trans hLeftWhisker)
  have hSourceTensor : p ≫ t = lt := copowerTensorHom_generator.{u, v, w} I f g
  have hTargetGenerator : lt ≫ mt = em :=
    originalDiagramHomMap_generator.{u, v, w} F (f ⊗ₘ g)
  have hRightPre : p ≫ (t ≫ mt) = em :=
    (Category.assoc p t mt).symm.trans
      ((congrArg (fun z : U ⟶ D => z ≫ mt) hSourceTensor).trans hTargetGenerator)
  have hRightWhisker : em ≫ wr = eHomEquiv V (μ F i j ≫ F.map (f ⊗ₘ g)) :=
    eHomEquiv_comp_eHomWhiskerRight (V := V) (C := V)
      (μ F i j) (F.map (f ⊗ₘ g))
  have hRight : p ≫ (t ≫ mt ≫ wr) =
      eHomEquiv V (μ F i j ≫ F.map (f ⊗ₘ g)) := by
    simpa only [Category.assoc] using (Category.assoc p (t ≫ mt) wr).symm.trans
      ((congrArg (fun z => z ≫ wr) hRightPre).trans hRightWhisker)
  let eh : (A ⟶ B') ≃ (U ⟶ H) := eHomEquiv V
  have hOriginal : eh ((F.map f ⊗ₘ F.map g) ≫ μ F i' j') =
      eh (μ F i j ≫ F.map (f ⊗ₘ g)) := congrArg eh (μ_natural F f g)
  change p ≫ ((mf ⊗ₘ mg) ≫ td ≫ wl) = p ≫ (t ≫ mt ≫ wr)
  exact hLeft.trans (hOriginal.trans hRight.symm)

/-- Lift the actual ordinary lax unit and tensorator to full enriched monoidal data. -/
def enrichOriginalMonoidalLaxData :
    EnrichedFunctor.LaxMonoidalData (copowerUnderlyingMonoidalData.{u, v, w} I)
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, max v w})
      (enrichOriginalMonoidalDiagram.{u, v, w} F) where
  epsilon := ε F
  mu X Y := μ F (show I from X) (show I from Y)
  mu_naturality X X' Y Y' :=
    enrichOriginalMonoidalDiagram_mu_naturality.{u, v, w} F
      (show I from X) (show I from X') (show I from Y) (show I from Y')
  unit X := by
    let i : I := X
    constructor
    · let V := PointedCGWH.{u, max v w}
      let A : V := F.obj (𝟙_ I ⊗ i)
      let B : V := F.obj i
      let q : A ⟶ B := (eHomEquiv V).symm
        (eHomEquiv V ((copowerRestriction.{u, v, w} I).map (λ_ i).hom) ≫
          (enrichOriginalMonoidalDiagram.{u, v, w} F).map
            ((copowerRestriction.{u, v, w} I).obj (𝟙_ I ⊗ i))
            ((copowerRestriction.{u, v, w} I).obj i))
      have hq : q = F.map (λ_ i).hom :=
        originalCoefficientMap.{u, v, w} F (λ_ i).hom
      have hOriginal : (λ_ B).hom = ε F ▷ B ≫ μ F (𝟙_ I) i ≫ F.map (λ_ i).hom :=
        left_unitality F i
      have hMapped : ε F ▷ B ≫ μ F (𝟙_ I) i ≫ F.map (λ_ i).hom =
          ε F ▷ B ≫ μ F (𝟙_ I) i ≫ q :=
        congrArg (fun z : A ⟶ B => ε F ▷ B ≫ μ F (𝟙_ I) i ≫ z) hq.symm
      change (λ_ B).hom = ε F ▷ B ≫ μ F (𝟙_ I) i ≫ q
      exact hOriginal.trans hMapped
    · let V := PointedCGWH.{u, max v w}
      let A : V := F.obj (i ⊗ 𝟙_ I)
      let B : V := F.obj i
      let q : A ⟶ B := (eHomEquiv V).symm
        (eHomEquiv V ((copowerRestriction.{u, v, w} I).map (ρ_ i).hom) ≫
          (enrichOriginalMonoidalDiagram.{u, v, w} F).map
            ((copowerRestriction.{u, v, w} I).obj (i ⊗ 𝟙_ I))
            ((copowerRestriction.{u, v, w} I).obj i))
      have hq : q = F.map (ρ_ i).hom :=
        originalCoefficientMap.{u, v, w} F (ρ_ i).hom
      have hOriginal : (ρ_ B).hom = B ◁ ε F ≫ μ F i (𝟙_ I) ≫ F.map (ρ_ i).hom :=
        right_unitality F i
      have hMapped : B ◁ ε F ≫ μ F i (𝟙_ I) ≫ F.map (ρ_ i).hom =
          B ◁ ε F ≫ μ F i (𝟙_ I) ≫ q :=
        congrArg (fun z : A ⟶ B => B ◁ ε F ≫ μ F i (𝟙_ I) ≫ z) hq.symm
      change (ρ_ B).hom = B ◁ ε F ≫ μ F i (𝟙_ I) ≫ q
      exact hOriginal.trans hMapped
  assoc X Y Z := by
    let i : I := X
    let j : I := Y
    let k : I := Z
    let V := PointedCGWH.{u, max v w}
    let A : V := F.obj ((i ⊗ j) ⊗ k)
    let B : V := F.obj (i ⊗ (j ⊗ k))
    let q : A ⟶ B := (eHomEquiv V).symm
      (eHomEquiv V ((copowerRestriction.{u, v, w} I).map (α_ i j k).hom) ≫
        (enrichOriginalMonoidalDiagram.{u, v, w} F).map
          ((copowerRestriction.{u, v, w} I).obj ((i ⊗ j) ⊗ k))
          ((copowerRestriction.{u, v, w} I).obj (i ⊗ (j ⊗ k))))
    have hq : q = F.map (α_ i j k).hom :=
      originalCoefficientMap.{u, v, w} F (α_ i j k).hom
    have hMapped : μ F i j ▷ F.obj k ≫ μ F (i ⊗ j) k ≫ q =
        μ F i j ▷ F.obj k ≫ μ F (i ⊗ j) k ≫ F.map (α_ i j k).hom :=
      congrArg (fun z : A ⟶ B => μ F i j ▷ F.obj k ≫ μ F (i ⊗ j) k ≫ z) hq
    have hOriginal : μ F i j ▷ F.obj k ≫ μ F (i ⊗ j) k ≫ F.map (α_ i j k).hom =
        (α_ (F.obj i) (F.obj j) (F.obj k)).hom ≫
          F.obj i ◁ μ F j k ≫ μ F i (j ⊗ k) :=
      Functor.LaxMonoidal.associativity F i j k
    change μ F i j ▷ F.obj k ≫ μ F (i ⊗ j) k ≫ q =
      (α_ (F.obj i) (F.obj j) (F.obj k)).hom ≫ F.obj i ◁ μ F j k ≫ μ F i (j ⊗ k)
    exact hMapped.trans hOriginal

/-- The lifted unit is the literal original lax unit. -/
theorem enrichOriginalMonoidalLaxData_epsilon :
    (enrichOriginalMonoidalLaxData.{u, v, w} F).epsilon = ε F := rfl

/-- Every lifted tensorator is the literal original lax tensorator. -/
theorem enrichOriginalMonoidalLaxData_mu (i j : I) :
    (enrichOriginalMonoidalLaxData.{u, v, w} F).mu
        ((copowerRestriction.{u, v, w} I).obj i)
        ((copowerRestriction.{u, v, w} I).obj j) = μ F i j := rfl

end MonoidalIndex

section Strong

variable [MonoidalCategory I] (F : I ⥤ PointedCGWH.{u, max v w}) [F.Monoidal]

attribute [local instance] copowerUnderlyingMonoidal

/-- The existing ordinary strongness witnesses also prove enriched strongness. -/
theorem enrichOriginalMonoidalStrongData :
    EnrichedFunctor.StrongMonoidalData (enrichOriginalMonoidalLaxData.{u, v, w} F) where
  unitIso := by
    change IsIso (ε F)
    infer_instance
  tensorIso X Y := by
    change IsIso (μ F (show I from X) (show I from Y))
    infer_instance

end Strong

section Sphere

private abbrev sphereFunctorBraided : sphereSequence.{u, v}.functor.Braided :=
  CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}

attribute [local instance] sphereFunctorBraided copowerUnderlyingMonoidal

/-- The actual original sphere coefficient as a full copower-enriched functor. -/
abbrev sphereCopowerEnrichedFunctor :
    EnrichedFunctor PointedCGWH.{u, v}
      (CopowerUnderlying.{u, v, 0} CategoryTheory.Operad.SmallFinBijGroupoid)
      PointedCGWH.{u, v} :=
  enrichOriginalMonoidalDiagram.{u, v, 0} sphereSequence.functor

/-- Enriched sphere multiplication and unit are the original sphere functor's maps. -/
def sphereCopowerLaxData :
    EnrichedFunctor.LaxMonoidalData
      (copowerUnderlyingMonoidalData.{u, v, 0} CategoryTheory.Operad.SmallFinBijGroupoid)
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v})
      sphereCopowerEnrichedFunctor.{u, v} := by
  letI : sphereSequence.{u, v}.functor.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}
  exact enrichOriginalMonoidalLaxData.{u, v, 0} sphereSequence.functor

/-- Strongness uses the actual tensor-power unit and multiplication isomorphisms. -/
theorem sphereCopowerStrongData :
    EnrichedFunctor.StrongMonoidalData sphereCopowerLaxData.{u, v} := by
  let _ : sphereSequence.{u, v}.functor.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}
  change EnrichedFunctor.StrongMonoidalData
    (enrichOriginalMonoidalLaxData.{u, v, 0} sphereSequence.functor)
  exact enrichOriginalMonoidalStrongData.{u, v, 0} sphereSequence.functor

/-- The original Day sphere unit is the literal lifted enriched sphere unit. -/
theorem sphereCopowerLaxData_one :
    DayFunctor.ν CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v} ≫
        sphereSequenceMonObj.one.natTrans.app (𝟙_ CategoryTheory.Operad.SmallFinBijGroupoid) =
      sphereCopowerLaxData.{u, v}.epsilon := by
  let _ : sphereSequence.{u, v}.functor.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}
  change DayFunctor.ν CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v} ≫
    sphereSequenceMonObj.one.natTrans.app (𝟙_ CategoryTheory.Operad.SmallFinBijGroupoid) =
      ε sphereSequence.functor
  exact sphereSequence_one_app

/-- The original Day sphere multiplication is the same lifted coefficient tensorator. -/
theorem sphereCopowerLaxData_mul (A B : CategoryTheory.Operad.SmallFinBijGroupoid) :
    (DayFunctor.η sphereSequence.{u, v} sphereSequence).app (A, B) ≫
        sphereSequenceMonObj.mul.natTrans.app (A ⊗ B) =
      sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} CategoryTheory.Operad.SmallFinBijGroupoid).obj A)
          ((copowerRestriction.{u, v, 0} CategoryTheory.Operad.SmallFinBijGroupoid).obj B) := by
  let _ : sphereSequence.{u, v}.functor.Braided :=
    CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided sphereOne.{u, v}
  change (DayFunctor.η sphereSequence.{u, v} sphereSequence).app (A, B) ≫
    sphereSequenceMonObj.mul.natTrans.app (A ⊗ B) = μ sphereSequence.functor A B
  exact sphereSequence_mul_app A B

end Sphere

end PointedCGWH
