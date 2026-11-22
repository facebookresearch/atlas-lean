/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerTensorHom
public import MathlibExt.Topology.Category.PointedCGWH.Points
public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Copower enrichment and its monoidal structure

An ordinary category acquires the native copower enrichment and its
associated enriched ordinary category. If it is monoidal, its tensor extends
to all tensor-unit-point arrows of `CopowerUnderlying`, with associator and
unitors induced from the original category. The tensor identities,
naturality, pentagon and triangle construct `copowerUnderlyingMonoidal`.
The same Hom tensor maps give `copowerUnderlyingMonoidalData`, including
full enriched tensor and unitor naturality.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uI r

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Functor.LaxMonoidal

namespace PointedCGWH

private abbrev gamma : Type w ⥤ PointedCGWH.{u, max v w} :=
  basedDiscreteFunctor.{u, v, w}

private abbrev gammaBraided : gamma.{u, v, w}.LaxBraided :=
  basedDiscreteBraided.{u, v, w}.toLaxBraided

attribute [local instance] gammaBraided

private abbrev pointFunctor : PointedCGWH.{u, r} ⥤ Type r :=
  coyoneda.obj (op (𝟙_ PointedCGWH.{u, r}))

/-- The chosen point functor keeps the actual unit-point pairing. -/
@[instance_reducible]
private def pointFunctorBraided : pointFunctor.{u, r}.LaxBraided where
  toLaxMonoidal := (inferInstance : (pointFunctor.{u, r}).LaxMonoidal)
  braided X Y := by
    let U : PointedCGWH.{u, r} := 𝟙_ PointedCGWH.{u, r}
    ext p
    change ((λ_ U).inv ≫ (p.1 ⊗ₘ p.2)) ≫ (β_ X Y).hom =
      (λ_ U).inv ≫ (p.2 ⊗ₘ p.1)
    have hUnit : (λ_ U).inv ≫ (β_ U U).hom = (λ_ U).inv := by
      rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc]
      exact unitors_inv_equal.symm
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => (λ_ U).inv ≫ q)
        (BraidedCategory.braiding_naturality p.1 p.2)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun q => q ≫ (p.2 ⊗ₘ p.1)) hUnit)))

attribute [local instance] pointFunctorBraided

private theorem pointPairAssociativity {X Y Z : PointedCGWH.{u, r}}
    (x : 𝟙_ PointedCGWH.{u, r} ⟶ X)
    (y : 𝟙_ PointedCGWH.{u, r} ⟶ Y)
    (z : 𝟙_ PointedCGWH.{u, r} ⟶ Z) :
    pointPair (pointPair x y) z ≫ (α_ X Y Z).hom = pointPair x (pointPair y z) := by
  have h := Functor.LaxMonoidal.associativity pointFunctor.{u, r} X Y Z
  have hPoint := congrArg
    (fun k : ((pointFunctor.{u, r}.obj X ⊗ pointFunctor.{u, r}.obj Y) ⊗
        pointFunctor.{u, r}.obj Z) ⟶ pointFunctor.{u, r}.obj (X ⊗ (Y ⊗ Z)) =>
      k (show ((pointFunctor.{u, r}.obj X ⊗ pointFunctor.{u, r}.obj Y) ⊗
        pointFunctor.{u, r}.obj Z) from ((x, y), z))) h
  change pointPair (pointPair x y) z ≫ (α_ X Y Z).hom =
    pointPair x (pointPair y z) at hPoint
  exact hPoint

private theorem pointPairInterchange {X Y Z W : PointedCGWH.{u, r}}
    (x : 𝟙_ PointedCGWH.{u, r} ⟶ X)
    (y : 𝟙_ PointedCGWH.{u, r} ⟶ Y)
    (z : 𝟙_ PointedCGWH.{u, r} ⟶ Z)
    (t : 𝟙_ PointedCGWH.{u, r} ⟶ W) :
    pointPair (pointPair x y) (pointPair z t) ≫ MonoidalCategory.tensorμ X Y Z W =
      pointPair (pointPair x z) (pointPair y t) := by
  have h := MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ
    pointFunctor.{u, r} X Y Z W
  have hPoint := congrArg
    (fun k : ((pointFunctor.{u, r}.obj X ⊗ pointFunctor.{u, r}.obj Y) ⊗
        (pointFunctor.{u, r}.obj Z ⊗ pointFunctor.{u, r}.obj W)) ⟶
          pointFunctor.{u, r}.obj ((X ⊗ Z) ⊗ (Y ⊗ W)) =>
      k (show ((pointFunctor.{u, r}.obj X ⊗ pointFunctor.{u, r}.obj Y) ⊗
        (pointFunctor.{u, r}.obj Z ⊗ pointFunctor.{u, r}.obj W)) from
          ((x, y), (z, t)))) h
  change pointPair (pointPair x z) (pointPair y t) =
    pointPair (pointPair x y) (pointPair z t) ≫
      MonoidalCategory.tensorμ X Y Z W at hPoint
  exact hPoint.symm

/-- The actual lax unit and a constant Type leg give the complete left transport. -/
private theorem laxUnitConstantLeft
    (F : Type w ⥤ PointedCGWH.{u, r}) [F.LaxMonoidal]
    {A B R : Type w} (c : 𝟙_ (Type w) ⟶ A) (q : A ⊗ B ⟶ R) :
    (λ_ (F.obj B)).inv ≫ (ε F ≫ F.map c) ▷ F.obj B ≫
        μ F A B ≫ F.map q =
      F.map ((λ_ B).inv ≫ c ▷ B ≫ q) := by
  have hWhisker : (ε F ≫ F.map c) ▷ F.obj B =
      ε F ▷ F.obj B ≫ F.map c ▷ F.obj B :=
    comp_whiskerRight (ε F) (F.map c) (F.obj B)
  have hNatural : F.map c ▷ F.obj B ≫ μ F A B =
      μ F (𝟙_ (Type w)) B ≫ F.map (c ▷ B) :=
    μ_natural_left F c B
  have hUnit : (λ_ (F.obj B)).inv ≫ ε F ▷ F.obj B ≫
      μ F (𝟙_ (Type w)) B = F.map (λ_ B).inv :=
    left_unitality_inv F B
  calc
    _ = (λ_ (F.obj B)).inv ≫ ε F ▷ F.obj B ≫ F.map c ▷ F.obj B ≫
        μ F A B ≫ F.map q := by
      simpa only [Category.assoc] using congrArg
        (fun z => (λ_ (F.obj B)).inv ≫ z ≫ μ F A B ≫ F.map q) hWhisker
    _ = (λ_ (F.obj B)).inv ≫ ε F ▷ F.obj B ≫
        μ F (𝟙_ (Type w)) B ≫ F.map (c ▷ B) ≫ F.map q := by
      simpa only [Category.assoc] using congrArg
        (fun z => (λ_ (F.obj B)).inv ≫ ε F ▷ F.obj B ≫ z ≫ F.map q) hNatural
    _ = F.map (λ_ B).inv ≫ F.map (c ▷ B) ≫ F.map q := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ F.map (c ▷ B) ≫ F.map q) hUnit
    _ = _ := by rw [F.map_comp, F.map_comp]

/-- The same actual lax unit gives the complete right transport. -/
private theorem laxUnitConstantRight
    (F : Type w ⥤ PointedCGWH.{u, r}) [F.LaxMonoidal]
    {A B R : Type w} (c : 𝟙_ (Type w) ⟶ B) (q : A ⊗ B ⟶ R) :
    (ρ_ (F.obj A)).inv ≫ F.obj A ◁ (ε F ≫ F.map c) ≫
        μ F A B ≫ F.map q =
      F.map ((ρ_ A).inv ≫ A ◁ c ≫ q) := by
  have hWhisker : F.obj A ◁ (ε F ≫ F.map c) =
      F.obj A ◁ ε F ≫ F.obj A ◁ F.map c :=
    MonoidalCategory.whiskerLeft_comp (F.obj A) (ε F) (F.map c)
  have hNatural : F.obj A ◁ F.map c ≫ μ F A B =
      μ F A (𝟙_ (Type w)) ≫ F.map (A ◁ c) :=
    μ_natural_right F A c
  have hUnit : (ρ_ (F.obj A)).inv ≫ F.obj A ◁ ε F ≫
      μ F A (𝟙_ (Type w)) = F.map (ρ_ A).inv :=
    right_unitality_inv F A
  calc
    _ = (ρ_ (F.obj A)).inv ≫ F.obj A ◁ ε F ≫ F.obj A ◁ F.map c ≫
        μ F A B ≫ F.map q := by
      simpa only [Category.assoc] using congrArg
        (fun z => (ρ_ (F.obj A)).inv ≫ z ≫ μ F A B ≫ F.map q) hWhisker
    _ = (ρ_ (F.obj A)).inv ≫ F.obj A ◁ ε F ≫
        μ F A (𝟙_ (Type w)) ≫ F.map (A ◁ c) ≫ F.map q := by
      simpa only [Category.assoc] using congrArg
        (fun z => (ρ_ (F.obj A)).inv ≫ F.obj A ◁ ε F ≫ z ≫ F.map q) hNatural
    _ = F.map (ρ_ A).inv ≫ F.map (A ◁ c) ≫ F.map q := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ F.map (A ◁ c) ≫ F.map q) hUnit
    _ = _ := by rw [F.map_comp, F.map_comp]

section OriginalCategory

variable (I : Type uI) [Category.{w} I]

/-- The existing associated category has all native unit-points as ordinary arrows. -/
@[instance_reducible]
def copowerUnderlyingEnrichedOrdinary :
    EnrichedOrdinaryCategory PointedCGWH.{u, max v w} (CopowerUnderlying.{u, v, w} I) := by
  change EnrichedOrdinaryCategory PointedCGWH.{u, max v w}
    (ForgetEnrichment PointedCGWH.{u, max v w} (CopowerIndex.{u, v, w} I))
  infer_instance

attribute [local instance] copowerUnderlyingEnrichedOrdinary

private abbrev oldObj (X : CopowerUnderlying.{u, v, w} I) : I := X

private theorem restrictionPoint {i j : I} (f : i ⟶ j) :
    eHomEquiv PointedCGWH.{u, max v w} ((copowerRestriction.{u, v, w} I).map f) =
      basedDiscreteIncl.{u, v, w} (i ⟶ j) f :=
  copowerRestriction_map.{u, v, w} I f

private def compLabels (i j k : I) : ((i ⟶ j) × (j ⟶ k)) ⟶ (i ⟶ k) :=
  ↾fun p => p.1 ≫ p.2

/-- Precomposition by an original arrow acts on the entire native Hom object. -/
private theorem originalPrecomp {i j k : I} (f : i ⟶ j) :
    (λ_ (basedDiscreteObj.{u, v, w} (j ⟶ k))).inv ≫
        basedDiscreteIncl.{u, v, w} (i ⟶ j) f ▷
          basedDiscreteObj.{u, v, w} (j ⟶ k) ≫
        eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
          (copowerIndexObj.{u, v, w} I j) (copowerIndexObj.{u, v, w} I k) =
      gamma.{u, v, w}.map (↾fun g : j ⟶ k => f ≫ g) := by
  let F := gamma.{u, v, w}
  let A : Type w := i ⟶ j
  let H : Type w := j ⟶ k
  let R : Type w := i ⟶ k
  let c : 𝟙_ (Type w) ⟶ A := ↾fun _ => f
  let q : A ⊗ H ⟶ R := compLabels I i j k
  let l : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj A :=
    basedDiscreteIncl.{u, v, w} (i ⟶ j) f
  have hIncl : l = ε F ≫ F.map c :=
    (basedDiscreteIncl_naturality.{u, v, w} (fun _ : PUnit.{w + 1} => f)
      PUnit.unit).symm
  have hLabels : (λ_ H).inv ≫ c ▷ H ≫ q = (↾fun g : j ⟶ k => f ≫ g) := by
    ext g
    rfl
  have hReplace : (λ_ (F.obj H)).inv ≫ l ▷ F.obj H ≫ μ F A H ≫ F.map q =
      (λ_ (F.obj H)).inv ≫ (ε F ≫ F.map c) ▷ F.obj H ≫ μ F A H ≫ F.map q :=
    congrArg (fun z : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj A =>
      (λ_ (F.obj H)).inv ≫ z ▷ F.obj H ≫ μ F A H ≫ F.map q) hIncl
  change (λ_ (F.obj H)).inv ≫ l ▷ F.obj H ≫ μ F A H ≫ F.map q =
    F.map (↾fun g : j ⟶ k => f ≫ g)
  exact hReplace.trans ((laxUnitConstantLeft F c q).trans (congrArg F.map hLabels))

/-- Postcomposition by an original arrow acts on the entire native Hom object. -/
private theorem originalPostcomp {i j k : I} (g : j ⟶ k) :
    (ρ_ (basedDiscreteObj.{u, v, w} (i ⟶ j))).inv ≫
        basedDiscreteObj.{u, v, w} (i ⟶ j) ◁
          basedDiscreteIncl.{u, v, w} (j ⟶ k) g ≫
        eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
          (copowerIndexObj.{u, v, w} I j) (copowerIndexObj.{u, v, w} I k) =
      gamma.{u, v, w}.map (↾fun f : i ⟶ j => f ≫ g) := by
  let F := gamma.{u, v, w}
  let H : Type w := i ⟶ j
  let B : Type w := j ⟶ k
  let R : Type w := i ⟶ k
  let c : 𝟙_ (Type w) ⟶ B := ↾fun _ => g
  let q : H ⊗ B ⟶ R := compLabels I i j k
  let l : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj B :=
    basedDiscreteIncl.{u, v, w} (j ⟶ k) g
  have hIncl : l = ε F ≫ F.map c :=
    (basedDiscreteIncl_naturality.{u, v, w} (fun _ : PUnit.{w + 1} => g)
      PUnit.unit).symm
  have hLabels : (ρ_ H).inv ≫ H ◁ c ≫ q = (↾fun f : i ⟶ j => f ≫ g) := by
    ext f
    rfl
  have hReplace : (ρ_ (F.obj H)).inv ≫ F.obj H ◁ l ≫ μ F H B ≫ F.map q =
      (ρ_ (F.obj H)).inv ≫ F.obj H ◁ (ε F ≫ F.map c) ≫ μ F H B ≫ F.map q :=
    congrArg (fun z : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj B =>
      (ρ_ (F.obj H)).inv ≫ F.obj H ◁ z ≫ μ F H B ≫ F.map q) hIncl
  change (ρ_ (F.obj H)).inv ≫ F.obj H ◁ l ≫ μ F H B ≫ F.map q =
    F.map (↾fun f : i ⟶ j => f ≫ g)
  exact hReplace.trans ((laxUnitConstantRight F c q).trans (congrArg F.map hLabels))

private theorem restrictionPrecomp {i j k : I} (f : i ⟶ j) :
    eHomWhiskerRight PointedCGWH.{u, max v w}
        ((copowerRestriction.{u, v, w} I).map f) ((copowerRestriction.{u, v, w} I).obj k) =
      gamma.{u, v, w}.map (↾fun g : j ⟶ k => f ≫ g) :=
  originalPrecomp.{u, v, w} I f

private theorem restrictionPostcomp {i j k : I} (g : j ⟶ k) :
    eHomWhiskerLeft PointedCGWH.{u, max v w} ((copowerRestriction.{u, v, w} I).obj i)
        ((copowerRestriction.{u, v, w} I).map g) =
      gamma.{u, v, w}.map (↾fun f : i ⟶ j => f ≫ g) :=
  originalPostcomp.{u, v, w} I g

end OriginalCategory

attribute [local instance] copowerUnderlyingEnrichedOrdinary

section OriginalMonoidal

variable (I : Type uI) [Category.{w} I] [MonoidalCategory I]

private def tensorLabels (i i' j j' : I) :
    ((i ⟶ i') × (j ⟶ j')) ⟶ ((i ⊗ j) ⟶ (i' ⊗ j')) :=
  ↾fun p => p.1 ⊗ₘ p.2

private theorem tensorHomIdentity (i j : I) :
    (λ_ (𝟙_ PointedCGWH.{u, max v w})).inv ≫
        (eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i) ⊗ₘ
          eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I j)) ≫
        copowerTensorHom.{u, v, w} I i i j j =
      eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I (i ⊗ j)) := by
  rw [copowerIndex_id, copowerIndex_id, copowerIndex_id]
  have h := copowerTensorHom_generator.{u, v, w} I (𝟙 i) (𝟙 j)
  have hId := congrArg (basedDiscreteIncl.{u, v, w} ((i ⊗ j) ⟶ (i ⊗ j)))
    (id_tensorHom_id i j)
  exact (Category.assoc _ _ _).symm.trans (h.trans hId)

/-- The native tensorator interchange proves composition on whole Hom objects. -/
theorem copowerTensorHom_comp (i i' i'' j j' j'' : I) :
    MonoidalCategory.tensorμ
        (basedDiscreteObj.{u, v, w} (i ⟶ i'))
        (basedDiscreteObj.{u, v, w} (j ⟶ j'))
        (basedDiscreteObj.{u, v, w} (i' ⟶ i''))
        (basedDiscreteObj.{u, v, w} (j' ⟶ j'')) ≫
      (eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I i)
          (copowerIndexObj.{u, v, w} I i') (copowerIndexObj.{u, v, w} I i'') ⊗ₘ
        eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I j)
          (copowerIndexObj.{u, v, w} I j') (copowerIndexObj.{u, v, w} I j'')) ≫
      copowerTensorHom.{u, v, w} I i i'' j j'' =
    (copowerTensorHom.{u, v, w} I i i' j j' ⊗ₘ
      copowerTensorHom.{u, v, w} I i' i'' j' j'') ≫
      eComp PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I (i ⊗ j))
        (copowerIndexObj.{u, v, w} I (i' ⊗ j'))
        (copowerIndexObj.{u, v, w} I (i'' ⊗ j'')) := by
  let F := gamma.{u, v, w}
  let A : Type w := i ⟶ i'
  let B : Type w := j ⟶ j'
  let C : Type w := i' ⟶ i''
  let D : Type w := j' ⟶ j''
  let E : Type w := i ⟶ i''
  let G : Type w := j ⟶ j''
  let H₀ : Type w := (i ⊗ j) ⟶ (i' ⊗ j')
  let H₁ : Type w := (i' ⊗ j') ⟶ (i'' ⊗ j'')
  let R : Type w := (i ⊗ j) ⟶ (i'' ⊗ j'')
  let cI : A ⊗ C ⟶ E := compLabels I i i' i''
  let cJ : B ⊗ D ⟶ G := compLabels I j j' j''
  let t0 : A ⊗ B ⟶ H₀ := tensorLabels I i i' j j'
  let t1 : C ⊗ D ⟶ H₁ := tensorLabels I i' i'' j' j''
  let t2 : E ⊗ G ⟶ R := tensorLabels I i i'' j j''
  let cT : H₀ ⊗ H₁ ⟶ R := compLabels I (i ⊗ j) (i' ⊗ j') (i'' ⊗ j'')
  let m := MonoidalCategory.tensorμ (F.obj A) (F.obj B) (F.obj C) (F.obj D)
  let p : ((F.obj A ⊗ F.obj B) ⊗ (F.obj C ⊗ F.obj D)) ⟶
      F.obj ((A ⊗ B) ⊗ (C ⊗ D)) :=
    (μ F A B ⊗ₘ μ F C D) ≫ μ F (A ⊗ B) (C ⊗ D)
  let lhs : ((F.obj A ⊗ F.obj B) ⊗ (F.obj C ⊗ F.obj D)) ⟶ F.obj R :=
    m ≫ ((μ F A C ≫ F.map cI) ⊗ₘ (μ F B D ≫ F.map cJ)) ≫
      (μ F E G ≫ F.map t2)
  let rhs : ((F.obj A ⊗ F.obj B) ⊗ (F.obj C ⊗ F.obj D)) ⟶ F.obj R :=
    ((μ F A B ≫ F.map t0) ⊗ₘ (μ F C D ≫ F.map t1)) ≫
      (μ F H₀ H₁ ≫ F.map cT)
  have hLabels : MonoidalCategory.tensorμ A B C D ≫ (cI ⊗ₘ cJ) ≫ t2 =
      (t0 ⊗ₘ t1) ≫ cT := by
    ext z
    change (z.1.1 ≫ z.2.1) ⊗ₘ (z.1.2 ≫ z.2.2) =
      (z.1.1 ⊗ₘ z.1.2) ≫ (z.2.1 ⊗ₘ z.2.2)
    exact (tensorHom_comp_tensorHom z.1.1 z.1.2 z.2.1 z.2.2).symm
  have hSeparateL : ((μ F A C ≫ F.map cI) ⊗ₘ (μ F B D ≫ F.map cJ)) =
      (μ F A C ⊗ₘ μ F B D) ≫ (F.map cI ⊗ₘ F.map cJ) :=
    (tensorHom_comp_tensorHom (μ F A C) (μ F B D) (F.map cI) (F.map cJ)).symm
  have hNaturalL : (F.map cI ⊗ₘ F.map cJ) ≫ μ F E G =
      μ F (A ⊗ C) (B ⊗ D) ≫ F.map (cI ⊗ₘ cJ) :=
    μ_natural F cI cJ
  have hKernel : m ≫ (μ F A C ⊗ₘ μ F B D) ≫ μ F (A ⊗ C) (B ⊗ D) =
      p ≫ F.map (MonoidalCategory.tensorμ A B C D) := by
    simpa only [m, p, Category.assoc] using
      MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ F A B C D
  have hMapL : F.map (MonoidalCategory.tensorμ A B C D) ≫
      F.map (cI ⊗ₘ cJ) ≫ F.map t2 =
        F.map (MonoidalCategory.tensorμ A B C D ≫ (cI ⊗ₘ cJ) ≫ t2) := by
    rw [F.map_comp, F.map_comp]
  have hLeft : lhs =
      p ≫ F.map (MonoidalCategory.tensorμ A B C D ≫ (cI ⊗ₘ cJ) ≫ t2) := by
    calc
      lhs = m ≫ (μ F A C ⊗ₘ μ F B D) ≫
          (F.map cI ⊗ₘ F.map cJ) ≫ μ F E G ≫ F.map t2 := by
        simpa only [lhs, Category.assoc] using congrArg
          (fun z => m ≫ z ≫ μ F E G ≫ F.map t2) hSeparateL
      _ = m ≫ (μ F A C ⊗ₘ μ F B D) ≫
          μ F (A ⊗ C) (B ⊗ D) ≫ F.map (cI ⊗ₘ cJ) ≫ F.map t2 := by
        simpa only [Category.assoc] using congrArg
          (fun z => m ≫ (μ F A C ⊗ₘ μ F B D) ≫ z ≫ F.map t2) hNaturalL
      _ = p ≫ F.map (MonoidalCategory.tensorμ A B C D) ≫
          F.map (cI ⊗ₘ cJ) ≫ F.map t2 := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ F.map (cI ⊗ₘ cJ) ≫ F.map t2) hKernel
      _ = _ := congrArg (fun z => p ≫ z) hMapL
  have hSeparateR : ((μ F A B ≫ F.map t0) ⊗ₘ (μ F C D ≫ F.map t1)) =
      (μ F A B ⊗ₘ μ F C D) ≫ (F.map t0 ⊗ₘ F.map t1) :=
    (tensorHom_comp_tensorHom (μ F A B) (μ F C D) (F.map t0) (F.map t1)).symm
  have hNaturalR : (F.map t0 ⊗ₘ F.map t1) ≫ μ F H₀ H₁ =
      μ F (A ⊗ B) (C ⊗ D) ≫ F.map (t0 ⊗ₘ t1) :=
    μ_natural F t0 t1
  have hMapR : F.map (t0 ⊗ₘ t1) ≫ F.map cT = F.map ((t0 ⊗ₘ t1) ≫ cT) :=
    (F.map_comp (t0 ⊗ₘ t1) cT).symm
  have hRight : rhs = p ≫ F.map ((t0 ⊗ₘ t1) ≫ cT) := by
    calc
      rhs = (μ F A B ⊗ₘ μ F C D) ≫
          (F.map t0 ⊗ₘ F.map t1) ≫ μ F H₀ H₁ ≫ F.map cT := by
        simpa only [rhs, Category.assoc] using congrArg
          (fun z => z ≫ μ F H₀ H₁ ≫ F.map cT) hSeparateR
      _ = p ≫ F.map (t0 ⊗ₘ t1) ≫ F.map cT := by
        simpa only [p, Category.assoc] using congrArg
          (fun z => (μ F A B ⊗ₘ μ F C D) ≫ z ≫ F.map cT) hNaturalR
      _ = _ := congrArg (fun z => p ≫ z) hMapR
  change lhs = rhs
  exact hLeft.trans ((congrArg (fun z => p ≫ F.map z) hLabels).trans hRight.symm)

private theorem tensorHomAssociativity (i i' j j' k k' : I) :
    copowerTensorHom.{u, v, w} I i i' j j' ▷
        basedDiscreteObj.{u, v, w} (k ⟶ k') ≫
      copowerTensorHom.{u, v, w} I (i ⊗ j) (i' ⊗ j') k k' ≫
      gamma.{u, v, w}.map
        (↾fun f : ((i ⊗ j) ⊗ k) ⟶ ((i' ⊗ j') ⊗ k') =>
          f ≫ (α_ i' j' k').hom) =
    (α_ (basedDiscreteObj.{u, v, w} (i ⟶ i'))
        (basedDiscreteObj.{u, v, w} (j ⟶ j'))
        (basedDiscreteObj.{u, v, w} (k ⟶ k'))).hom ≫
      basedDiscreteObj.{u, v, w} (i ⟶ i') ◁
        copowerTensorHom.{u, v, w} I j j' k k' ≫
      copowerTensorHom.{u, v, w} I i i' (j ⊗ k) (j' ⊗ k') ≫
      gamma.{u, v, w}.map
        (↾fun f : (i ⊗ (j ⊗ k)) ⟶ (i' ⊗ (j' ⊗ k')) =>
          (α_ i j k).hom ≫ f) := by
  let F := gamma.{u, v, w}
  let A : Type w := i ⟶ i'
  let B : Type w := j ⟶ j'
  let C : Type w := k ⟶ k'
  let E : Type w := (i ⊗ j) ⟶ (i' ⊗ j')
  let G : Type w := (j ⊗ k) ⟶ (j' ⊗ k')
  let TL : Type w := ((i ⊗ j) ⊗ k) ⟶ ((i' ⊗ j') ⊗ k')
  let TR : Type w := (i ⊗ (j ⊗ k)) ⟶ (i' ⊗ (j' ⊗ k'))
  let H : Type w := ((i ⊗ j) ⊗ k) ⟶ (i' ⊗ (j' ⊗ k'))
  let tAB : A ⊗ B ⟶ E := tensorLabels I i i' j j'
  let tBC : B ⊗ C ⟶ G := tensorLabels I j j' k k'
  let tL : E ⊗ C ⟶ TL := tensorLabels I (i ⊗ j) (i' ⊗ j') k k'
  let tR : A ⊗ G ⟶ TR := tensorLabels I i i' (j ⊗ k) (j' ⊗ k')
  let post : TL ⟶ H := ↾fun f => f ≫ (α_ i' j' k').hom
  let pre : TR ⟶ H := ↾fun f => (α_ i j k).hom ≫ f
  let p : ((F.obj A ⊗ F.obj B) ⊗ F.obj C) ⟶ F.obj (A ⊗ (B ⊗ C)) :=
    (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
      F.obj A ◁ μ F B C ≫ μ F A (B ⊗ C)
  let lhs : ((F.obj A ⊗ F.obj B) ⊗ F.obj C) ⟶ F.obj H :=
    (μ F A B ≫ F.map tAB) ▷ F.obj C ≫
      (μ F E C ≫ F.map tL) ≫ F.map post
  let rhs : ((F.obj A ⊗ F.obj B) ⊗ F.obj C) ⟶ F.obj H :=
    (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
      F.obj A ◁ (μ F B C ≫ F.map tBC) ≫
      (μ F A G ≫ F.map tR) ≫ F.map pre
  have hLabels : (α_ A B C).inv ≫ tAB ▷ C ≫ tL ≫ post =
      A ◁ tBC ≫ tR ≫ pre := by
    ext z
    change ((z.1 ⊗ₘ z.2.1) ⊗ₘ z.2.2) ≫ (α_ i' j' k').hom =
      (α_ i j k).hom ≫ (z.1 ⊗ₘ (z.2.1 ⊗ₘ z.2.2))
    exact associator_naturality z.1 z.2.1 z.2.2
  have hWhiskerL : (μ F A B ≫ F.map tAB) ▷ F.obj C =
      μ F A B ▷ F.obj C ≫ F.map tAB ▷ F.obj C :=
    comp_whiskerRight (μ F A B) (F.map tAB) (F.obj C)
  have hNaturalL : F.map tAB ▷ F.obj C ≫ μ F E C =
      μ F (A ⊗ B) C ≫ F.map (tAB ▷ C) :=
    μ_natural_left F tAB C
  have hKernel : μ F A B ▷ F.obj C ≫ μ F (A ⊗ B) C =
      p ≫ F.map (α_ A B C).inv := by
    simpa only [p, Category.assoc] using μ_whiskerRight_comp_μ F A B C
  have hMapL : F.map (α_ A B C).inv ≫ F.map (tAB ▷ C) ≫
      F.map tL ≫ F.map post =
        F.map ((α_ A B C).inv ≫ tAB ▷ C ≫ tL ≫ post) := by
    rw [F.map_comp, F.map_comp, F.map_comp]
  have hLeft : lhs = p ≫ F.map ((α_ A B C).inv ≫ tAB ▷ C ≫ tL ≫ post) := by
    calc
      lhs = μ F A B ▷ F.obj C ≫ F.map tAB ▷ F.obj C ≫
          μ F E C ≫ F.map tL ≫ F.map post := by
        simpa only [lhs, Category.assoc] using congrArg
          (fun z => z ≫ μ F E C ≫ F.map tL ≫ F.map post) hWhiskerL
      _ = μ F A B ▷ F.obj C ≫ μ F (A ⊗ B) C ≫
          F.map (tAB ▷ C) ≫ F.map tL ≫ F.map post := by
        simpa only [Category.assoc] using congrArg
          (fun z => μ F A B ▷ F.obj C ≫ z ≫ F.map tL ≫ F.map post) hNaturalL
      _ = p ≫ F.map (α_ A B C).inv ≫
          F.map (tAB ▷ C) ≫ F.map tL ≫ F.map post := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ F.map (tAB ▷ C) ≫ F.map tL ≫ F.map post) hKernel
      _ = _ := congrArg (fun z => p ≫ z) hMapL
  have hWhiskerR : F.obj A ◁ (μ F B C ≫ F.map tBC) =
      F.obj A ◁ μ F B C ≫ F.obj A ◁ F.map tBC :=
    MonoidalCategory.whiskerLeft_comp (F.obj A) (μ F B C) (F.map tBC)
  have hNaturalR : F.obj A ◁ F.map tBC ≫ μ F A G =
      μ F A (B ⊗ C) ≫ F.map (A ◁ tBC) :=
    μ_natural_right F A tBC
  have hMapR : F.map (A ◁ tBC) ≫ F.map tR ≫ F.map pre =
      F.map (A ◁ tBC ≫ tR ≫ pre) := by
    rw [F.map_comp, F.map_comp]
  have hRight : rhs = p ≫ F.map (A ◁ tBC ≫ tR ≫ pre) := by
    calc
      rhs = (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
          F.obj A ◁ μ F B C ≫ F.obj A ◁ F.map tBC ≫
          μ F A G ≫ F.map tR ≫ F.map pre := by
        simpa only [rhs, Category.assoc] using congrArg
          (fun z => (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
            z ≫ μ F A G ≫ F.map tR ≫ F.map pre) hWhiskerR
      _ = p ≫ F.map (A ◁ tBC) ≫ F.map tR ≫ F.map pre := by
        simpa only [p, Category.assoc] using congrArg
          (fun z => (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
            F.obj A ◁ μ F B C ≫ z ≫ F.map tR ≫ F.map pre) hNaturalR
      _ = _ := congrArg (fun z => p ≫ z) hMapR
  change lhs = rhs
  exact hLeft.trans ((congrArg (fun z => p ≫ F.map z) hLabels).trans hRight.symm)

private theorem tensorHomLeftUnit (i i' : I) :
    (λ_ (basedDiscreteObj.{u, v, w} (i ⟶ i'))).inv ≫
      (eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I (𝟙_ I)) ⊗ₘ
        𝟙 (basedDiscreteObj.{u, v, w} (i ⟶ i'))) ≫
      copowerTensorHom.{u, v, w} I (𝟙_ I) (𝟙_ I) i i' ≫
      gamma.{u, v, w}.map
        (↾fun f : (𝟙_ I ⊗ i) ⟶ (𝟙_ I ⊗ i') => f ≫ (λ_ i').hom) =
    gamma.{u, v, w}.map (↾fun f : i ⟶ i' => (λ_ i).hom ≫ f) := by
  let F := gamma.{u, v, w}
  let A : Type w := (𝟙_ I) ⟶ (𝟙_ I)
  let H : Type w := i ⟶ i'
  let T : Type w := (𝟙_ I ⊗ i) ⟶ (𝟙_ I ⊗ i')
  let R : Type w := (𝟙_ I ⊗ i) ⟶ i'
  let c : 𝟙_ (Type w) ⟶ A := ↾fun _ => 𝟙 (𝟙_ I)
  let t : A ⊗ H ⟶ T := tensorLabels I (𝟙_ I) (𝟙_ I) i i'
  let post : T ⟶ R := ↾fun f => f ≫ (λ_ i').hom
  let pre : H ⟶ R := ↾fun f => (λ_ i).hom ≫ f
  let e : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj A :=
    eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I (𝟙_ I))
  have hId : e = ε F ≫ F.map c := rfl
  have hLabels : (λ_ H).inv ≫ c ▷ H ≫ (t ≫ post) = pre := by
    ext f
    change (𝟙 (𝟙_ I) ⊗ₘ f) ≫ (λ_ i').hom = (λ_ i).hom ≫ f
    exact (congrArg (fun z => z ≫ (λ_ i').hom) (id_tensorHom (𝟙_ I) f)).trans
      (leftUnitor_naturality f)
  have hMap : F.map t ≫ F.map post = F.map (t ≫ post) :=
    (F.map_comp t post).symm
  have hTensor : e ⊗ₘ 𝟙 (F.obj H) = (ε F ≫ F.map c) ▷ F.obj H :=
    (tensorHom_id e (F.obj H)).trans
      (congrArg (fun z : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj A =>
        z ▷ F.obj H) hId)
  change (λ_ (F.obj H)).inv ≫ (e ⊗ₘ 𝟙 (F.obj H)) ≫
    (μ F A H ≫ F.map t) ≫ F.map post = F.map pre
  have hFirst : (λ_ (F.obj H)).inv ≫ (e ⊗ₘ 𝟙 (F.obj H)) ≫
      (μ F A H ≫ F.map t) ≫ F.map post =
      (λ_ (F.obj H)).inv ≫ (e ⊗ₘ 𝟙 (F.obj H)) ≫ μ F A H ≫ F.map (t ≫ post) := by
    simpa only [Category.assoc] using congrArg
      (fun z => (λ_ (F.obj H)).inv ≫ (e ⊗ₘ 𝟙 (F.obj H)) ≫ μ F A H ≫ z) hMap
  have hSecond := congrArg
    (fun z => (λ_ (F.obj H)).inv ≫ z ≫ μ F A H ≫ F.map (t ≫ post)) hTensor
  exact hFirst.trans (hSecond.trans
    ((laxUnitConstantLeft F c (t ≫ post)).trans (congrArg F.map hLabels)))

private theorem tensorHomRightUnit (i i' : I) :
    (ρ_ (basedDiscreteObj.{u, v, w} (i ⟶ i'))).inv ≫
      (𝟙 (basedDiscreteObj.{u, v, w} (i ⟶ i')) ⊗ₘ
        eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I (𝟙_ I))) ≫
      copowerTensorHom.{u, v, w} I i i' (𝟙_ I) (𝟙_ I) ≫
      gamma.{u, v, w}.map
        (↾fun f : (i ⊗ 𝟙_ I) ⟶ (i' ⊗ 𝟙_ I) => f ≫ (ρ_ i').hom) =
    gamma.{u, v, w}.map (↾fun f : i ⟶ i' => (ρ_ i).hom ≫ f) := by
  let F := gamma.{u, v, w}
  let H : Type w := i ⟶ i'
  let B : Type w := (𝟙_ I) ⟶ (𝟙_ I)
  let T : Type w := (i ⊗ 𝟙_ I) ⟶ (i' ⊗ 𝟙_ I)
  let R : Type w := (i ⊗ 𝟙_ I) ⟶ i'
  let c : 𝟙_ (Type w) ⟶ B := ↾fun _ => 𝟙 (𝟙_ I)
  let t : H ⊗ B ⟶ T := tensorLabels I i i' (𝟙_ I) (𝟙_ I)
  let post : T ⟶ R := ↾fun f => f ≫ (ρ_ i').hom
  let pre : H ⟶ R := ↾fun f => (ρ_ i).hom ≫ f
  let e : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj B :=
    eId PointedCGWH.{u, max v w} (copowerIndexObj.{u, v, w} I (𝟙_ I))
  have hId : e = ε F ≫ F.map c := rfl
  have hLabels : (ρ_ H).inv ≫ H ◁ c ≫ (t ≫ post) = pre := by
    ext f
    change (f ⊗ₘ 𝟙 (𝟙_ I)) ≫ (ρ_ i').hom = (ρ_ i).hom ≫ f
    exact (congrArg (fun z => z ≫ (ρ_ i').hom) (tensorHom_id f (𝟙_ I))).trans
      (rightUnitor_naturality f)
  have hMap : F.map t ≫ F.map post = F.map (t ≫ post) :=
    (F.map_comp t post).symm
  have hTensor : 𝟙 (F.obj H) ⊗ₘ e = F.obj H ◁ (ε F ≫ F.map c) :=
    (id_tensorHom (F.obj H) e).trans
      (congrArg (fun z : 𝟙_ PointedCGWH.{u, max v w} ⟶ F.obj B =>
        F.obj H ◁ z) hId)
  change (ρ_ (F.obj H)).inv ≫ (𝟙 (F.obj H) ⊗ₘ e) ≫
    (μ F H B ≫ F.map t) ≫ F.map post = F.map pre
  have hFirst : (ρ_ (F.obj H)).inv ≫ (𝟙 (F.obj H) ⊗ₘ e) ≫
      (μ F H B ≫ F.map t) ≫ F.map post =
      (ρ_ (F.obj H)).inv ≫ (𝟙 (F.obj H) ⊗ₘ e) ≫ μ F H B ≫ F.map (t ≫ post) := by
    simpa only [Category.assoc] using congrArg
      (fun z => (ρ_ (F.obj H)).inv ≫ (𝟙 (F.obj H) ⊗ₘ e) ≫ μ F H B ≫ z) hMap
  have hSecond := congrArg
    (fun z => (ρ_ (F.obj H)).inv ≫ z ≫ μ F H B ≫ F.map (t ≫ post)) hTensor
  exact hFirst.trans (hSecond.trans
    ((laxUnitConstantRight F c (t ≫ post)).trans (congrArg F.map hLabels)))

/-- Tensor native unit-point arrows with the original copower tensorator. -/
abbrev copowerUnderlyingTensorHom
    {X₁ Y₁ X₂ Y₂ : CopowerUnderlying.{u, v, w} I}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (copowerRestriction.{u, v, w} I).obj ((show I from X₁) ⊗ (show I from X₂)) ⟶
      (copowerRestriction.{u, v, w} I).obj ((show I from Y₁) ⊗ (show I from Y₂)) :=
  ForgetEnrichment.homOf PointedCGWH.{u, max v w}
    (((λ_ (𝟙_ PointedCGWH.{u, max v w})).inv ≫
      (eHomEquiv PointedCGWH.{u, max v w} f ⊗ₘ
        eHomEquiv PointedCGWH.{u, max v w} g)) ≫
      copowerTensorHom.{u, v, w} I
        (show I from X₁) (show I from Y₁) (show I from X₂) (show I from Y₂))

private theorem underlyingTensorPoint
    {X₁ Y₁ X₂ Y₂ : CopowerUnderlying.{u, v, w} I}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    eHomEquiv PointedCGWH.{u, max v w} (copowerUnderlyingTensorHom.{u, v, w} I f g) =
      pointPair (eHomEquiv PointedCGWH.{u, max v w} f)
          (eHomEquiv PointedCGWH.{u, max v w} g) ≫
        copowerTensorHom.{u, v, w} I
          (oldObj I X₁) (oldObj I Y₁) (oldObj I X₂) (oldObj I Y₂) := rfl

/-- The original native tensor objects, arrows and restriction coherence maps. -/
abbrev copowerUnderlyingMonoidalStruct :
    MonoidalCategoryStruct (CopowerUnderlying.{u, v, w} I) where
  tensorObj X Y := (copowerRestriction.{u, v, w} I).obj ((show I from X) ⊗ (show I from Y))
  whiskerLeft := fun X {_ _} f => copowerUnderlyingTensorHom.{u, v, w} I (𝟙 X) f
  whiskerRight := fun {_ _} f Y => copowerUnderlyingTensorHom.{u, v, w} I f (𝟙 Y)
  tensorHom := fun {_ _ _ _} f g => copowerUnderlyingTensorHom.{u, v, w} I f g
  tensorUnit := (copowerRestriction.{u, v, w} I).obj (𝟙_ I)
  associator X Y Z :=
    (copowerRestriction.{u, v, w} I).mapIso
      (α_ (show I from X) (show I from Y) (show I from Z))
  leftUnitor X := (copowerRestriction.{u, v, w} I).mapIso (λ_ (show I from X))
  rightUnitor X := (copowerRestriction.{u, v, w} I).mapIso (ρ_ (show I from X))

attribute [local instance] copowerUnderlyingMonoidalStruct

private theorem restrictionTensor {i i' j j' : I} (f : i ⟶ i') (g : j ⟶ j') :
    (copowerRestriction.{u, v, w} I).map f ⊗ₘ
        (copowerRestriction.{u, v, w} I).map g =
      (copowerRestriction.{u, v, w} I).map (f ⊗ₘ g) := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let R := copowerRestriction.{u, v, w} I
  let f₀ := R.map f
  let g₀ := R.map g
  let A : V := basedDiscreteObj.{u, v, w} (i ⟶ i')
  let B : V := basedDiscreteObj.{u, v, w} (j ⟶ j')
  let H : V := basedDiscreteObj.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j'))
  let t : A ⊗ B ⟶ H := copowerTensorHom.{u, v, w} I i i' j j'
  let lf : U ⟶ A := basedDiscreteIncl.{u, v, w} (i ⟶ i') f
  let lg : U ⟶ B := basedDiscreteIncl.{u, v, w} (j ⟶ j') g
  let lt : U ⟶ H := basedDiscreteIncl.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j')) (f ⊗ₘ g)
  let p : U ⟶ A ⊗ B := basedDiscretePairIncl.{u, v, w} (i ⟶ i') (j ⟶ j') f g
  have hf : eHomEquiv V f₀ = lf := restrictionPoint.{u, v, w} I f
  have hg : eHomEquiv V g₀ = lg := restrictionPoint.{u, v, w} I g
  have ht : eHomEquiv V (R.map (f ⊗ₘ g)) = lt :=
    restrictionPoint.{u, v, w} I (f ⊗ₘ g)
  have hPoint : eHomEquiv V (f₀ ⊗ₘ g₀) =
      pointPair (eHomEquiv V f₀) (eHomEquiv V g₀) ≫ t :=
    underlyingTensorPoint.{u, v, w} I f₀ g₀
  have hPair : pointPair (eHomEquiv V f₀) (eHomEquiv V g₀) = p :=
    congrArg₂ (fun a b => pointPair a b) hf hg
  have hGenerator : p ≫ t = lt := copowerTensorHom_generator.{u, v, w} I f g
  apply (eHomEquiv V).injective
  exact hPoint.trans
    ((congrArg (fun z : U ⟶ A ⊗ B => z ≫ t) hPair).trans
      (hGenerator.trans ht.symm))

/-- The native tensor of identity arrows is the identity of the tensor object. -/
theorem copowerUnderlyingTensorHom_id (X Y : CopowerUnderlying.{u, v, w} I) :
    (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let A : V := X ⟶[V] X
  let B : V := Y ⟶[V] Y
  let H : V := (X ⊗ Y) ⟶[V] (X ⊗ Y)
  let t : A ⊗ B ⟶ H := copowerTensorHom.{u, v, w} I
    (oldObj I X) (oldObj I X) (oldObj I Y) (oldObj I Y)
  let ex : U ⟶ A := eId V X
  let ey : U ⟶ B := eId V Y
  let e : U ⟶ H := eId V (X ⊗ Y)
  have hx : eHomEquiv V (𝟙 X) = ex := eHomEquiv_id V X
  have hy : eHomEquiv V (𝟙 Y) = ey := eHomEquiv_id V Y
  have he : eHomEquiv V (𝟙 (X ⊗ Y)) = e := eHomEquiv_id V (X ⊗ Y)
  have hPoint : eHomEquiv V ((𝟙 X) ⊗ₘ (𝟙 Y)) =
      pointPair (eHomEquiv V (𝟙 X)) (eHomEquiv V (𝟙 Y)) ≫ t :=
    underlyingTensorPoint.{u, v, w} I (𝟙 X) (𝟙 Y)
  have hPair : pointPair (eHomEquiv V (𝟙 X)) (eHomEquiv V (𝟙 Y)) =
      pointPair ex ey := congrArg₂ (fun a b => pointPair a b) hx hy
  have hNative : (λ_ U).inv ≫ (ex ⊗ₘ ey) ≫ t = e :=
    tensorHomIdentity.{u, v, w} I (oldObj I X) (oldObj I Y)
  have hLast : pointPair ex ey ≫ t = e :=
    (Category.assoc (λ_ U).inv (ex ⊗ₘ ey) t).trans hNative
  apply (eHomEquiv V).injective
  exact hPoint.trans
    ((congrArg (fun z : U ⟶ A ⊗ B => z ≫ t) hPair).trans (hLast.trans he.symm))

/-- Tensor native arrows compatibly with composition on whole Hom objects. -/
theorem copowerUnderlyingTensorHom_comp
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CopowerUnderlying.{u, v, w} I}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  apply (eHomEquiv PointedCGWH.{u, max v w}).injective
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let A : V := X₁ ⟶[V] Y₁
  let B : V := X₂ ⟶[V] Y₂
  let C : V := Y₁ ⟶[V] Z₁
  let D : V := Y₂ ⟶[V] Z₂
  let E : V := X₁ ⟶[V] Z₁
  let G : V := X₂ ⟶[V] Z₂
  let T₀ : V := (X₁ ⊗ X₂) ⟶[V] (Y₁ ⊗ Y₂)
  let T₁ : V := (Y₁ ⊗ Y₂) ⟶[V] (Z₁ ⊗ Z₂)
  let T₂ : V := (X₁ ⊗ X₂) ⟶[V] (Z₁ ⊗ Z₂)
  let a : U ⟶ A := eHomEquiv V f₁
  let b : U ⟶ B := eHomEquiv V f₂
  let c : U ⟶ C := eHomEquiv V g₁
  let d : U ⟶ D := eHomEquiv V g₂
  let t₀ : A ⊗ B ⟶ T₀ := copowerTensorHom.{u, v, w} I
    (oldObj I X₁) (oldObj I Y₁) (oldObj I X₂) (oldObj I Y₂)
  let t₁ : C ⊗ D ⟶ T₁ := copowerTensorHom.{u, v, w} I
    (oldObj I Y₁) (oldObj I Z₁) (oldObj I Y₂) (oldObj I Z₂)
  let t₂ : E ⊗ G ⟶ T₂ := copowerTensorHom.{u, v, w} I
    (oldObj I X₁) (oldObj I Z₁) (oldObj I X₂) (oldObj I Z₂)
  let c₁ : A ⊗ C ⟶ E := eComp V X₁ Y₁ Z₁
  let c₂ : B ⊗ D ⟶ G := eComp V X₂ Y₂ Z₂
  let cT : T₀ ⊗ T₁ ⟶ T₂ := eComp V (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)
  let m : (A ⊗ B) ⊗ (C ⊗ D) ⟶ (A ⊗ C) ⊗ (B ⊗ D) :=
    MonoidalCategory.tensorμ A B C D
  let p : U ⟶ (A ⊗ B) ⊗ (C ⊗ D) := pointPair (pointPair a b) (pointPair c d)
  let q : U ⟶ (A ⊗ C) ⊗ (B ⊗ D) := pointPair (pointPair a c) (pointPair b d)
  have hTensor : m ≫ (c₁ ⊗ₘ c₂) ≫ t₂ = (t₀ ⊗ₘ t₁) ≫ cT :=
    copowerTensorHom_comp.{u, v, w} I
      (oldObj I X₁) (oldObj I Y₁) (oldObj I Z₁)
      (oldObj I X₂) (oldObj I Y₂) (oldObj I Z₂)
  have hShuffle : p ≫ m = q := pointPairInterchange a b c d
  have hPairL : pointPair (pointPair a b ≫ t₀) (pointPair c d ≫ t₁) =
      p ≫ (t₀ ⊗ₘ t₁) :=
    (pointPairNatural (pointPair a b) (pointPair c d) t₀ t₁).symm
  have hPairR : q ≫ (c₁ ⊗ₘ c₂) =
      pointPair (pointPair a c ≫ c₁) (pointPair b d ≫ c₂) :=
    pointPairNatural (pointPair a c) (pointPair b d) c₁ c₂
  have hFirst : pointPair (pointPair a b ≫ t₀) (pointPair c d ≫ t₁) ≫ cT =
      p ≫ ((t₀ ⊗ₘ t₁) ≫ cT) :=
    (congrArg (fun z : U ⟶ T₀ ⊗ T₁ => z ≫ cT) hPairL).trans
      (Category.assoc p (t₀ ⊗ₘ t₁) cT)
  have hMiddle : p ≫ ((t₀ ⊗ₘ t₁) ≫ cT) =
      p ≫ (m ≫ (c₁ ⊗ₘ c₂) ≫ t₂) :=
    congrArg (fun z : (A ⊗ B) ⊗ (C ⊗ D) ⟶ T₂ => p ≫ z) hTensor.symm
  have hThird : p ≫ (m ≫ (c₁ ⊗ₘ c₂) ≫ t₂) = q ≫ (c₁ ⊗ₘ c₂) ≫ t₂ :=
    (Category.assoc p m ((c₁ ⊗ₘ c₂) ≫ t₂)).symm.trans
      (congrArg (fun z : U ⟶ (A ⊗ C) ⊗ (B ⊗ D) => z ≫ (c₁ ⊗ₘ c₂) ≫ t₂) hShuffle)
  have hLast : q ≫ (c₁ ⊗ₘ c₂) ≫ t₂ =
      pointPair (pointPair a c ≫ c₁) (pointPair b d ≫ c₂) ≫ t₂ :=
    (Category.assoc q (c₁ ⊗ₘ c₂) t₂).symm.trans
      (congrArg (fun z : U ⟶ E ⊗ G => z ≫ t₂) hPairR)
  simp only [eHomEquiv_comp]
  change pointPair (pointPair a b ≫ t₀) (pointPair c d ≫ t₁) ≫ cT =
    pointPair (pointPair a c ≫ c₁) (pointPair b d ≫ c₂) ≫ t₂
  exact hFirst.trans (hMiddle.trans (hThird.trans hLast))

private theorem underlyingTensorPointLeft
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : CopowerUnderlying.{u, v, w} I}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    eHomEquiv PointedCGWH.{u, max v w} ((f ⊗ₘ g) ⊗ₘ h) =
      pointPair (pointPair (eHomEquiv PointedCGWH.{u, max v w} f)
          (eHomEquiv PointedCGWH.{u, max v w} g))
          (eHomEquiv PointedCGWH.{u, max v w} h) ≫
        copowerTensorHom.{u, v, w} I
          (oldObj I X₁) (oldObj I Y₁) (oldObj I X₂) (oldObj I Y₂) ▷
          (X₃ ⟶[PointedCGWH.{u, max v w}] Y₃) ≫
        copowerTensorHom.{u, v, w} I
          (oldObj I X₁ ⊗ oldObj I X₂) (oldObj I Y₁ ⊗ oldObj I Y₂)
          (oldObj I X₃) (oldObj I Y₃) := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let A : V := X₁ ⟶[V] Y₁
  let B : V := X₂ ⟶[V] Y₂
  let C : V := X₃ ⟶[V] Y₃
  let D : V := (X₁ ⊗ X₂) ⟶[V] (Y₁ ⊗ Y₂)
  let H : V := ((X₁ ⊗ X₂) ⊗ X₃) ⟶[V] ((Y₁ ⊗ Y₂) ⊗ Y₃)
  let a : U ⟶ A := eHomEquiv V f
  let b : U ⟶ B := eHomEquiv V g
  let c : U ⟶ C := eHomEquiv V h
  let t : A ⊗ B ⟶ D := copowerTensorHom.{u, v, w} I
    (oldObj I X₁) (oldObj I Y₁) (oldObj I X₂) (oldObj I Y₂)
  let t' : D ⊗ C ⟶ H := copowerTensorHom.{u, v, w} I
    (oldObj I X₁ ⊗ oldObj I X₂) (oldObj I Y₁ ⊗ oldObj I Y₂)
    (oldObj I X₃) (oldObj I Y₃)
  let p : U ⟶ (A ⊗ B) ⊗ C := pointPair (pointPair a b) c
  have hInner : eHomEquiv V (f ⊗ₘ g) = pointPair a b ≫ t :=
    underlyingTensorPoint.{u, v, w} I f g
  have hOuter : eHomEquiv V ((f ⊗ₘ g) ⊗ₘ h) =
      pointPair (eHomEquiv V (f ⊗ₘ g)) c ≫ t' :=
    underlyingTensorPoint.{u, v, w} I (f ⊗ₘ g) h
  have hReplace : pointPair (eHomEquiv V (f ⊗ₘ g)) c ≫ t' =
      pointPair (pointPair a b ≫ t) c ≫ t' :=
    congrArg (fun z : U ⟶ D => pointPair z c ≫ t') hInner
  have hNatural : p ≫ t ▷ C = pointPair (pointPair a b ≫ t) c :=
    (congrArg (fun z => p ≫ z) (tensorHom_id t C).symm).trans
      ((pointPairNatural (pointPair a b) c t (𝟙 C)).trans
        (congrArg (fun z => pointPair (pointPair a b ≫ t) z) (Category.comp_id c)))
  have hLast : pointPair (pointPair a b ≫ t) c ≫ t' = p ≫ t ▷ C ≫ t' :=
    (congrArg (fun z : U ⟶ D ⊗ C => z ≫ t') hNatural.symm).trans
      (Category.assoc p (t ▷ C) t')
  exact hOuter.trans (hReplace.trans hLast)

private theorem underlyingTensorPointRight
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : CopowerUnderlying.{u, v, w} I}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    eHomEquiv PointedCGWH.{u, max v w} (f ⊗ₘ (g ⊗ₘ h)) =
      pointPair (eHomEquiv PointedCGWH.{u, max v w} f)
          (pointPair (eHomEquiv PointedCGWH.{u, max v w} g)
            (eHomEquiv PointedCGWH.{u, max v w} h)) ≫
        (X₁ ⟶[PointedCGWH.{u, max v w}] Y₁) ◁
          copowerTensorHom.{u, v, w} I
            (oldObj I X₂) (oldObj I Y₂) (oldObj I X₃) (oldObj I Y₃) ≫
        copowerTensorHom.{u, v, w} I
          (oldObj I X₁) (oldObj I Y₁)
          (oldObj I X₂ ⊗ oldObj I X₃) (oldObj I Y₂ ⊗ oldObj I Y₃) := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let A : V := X₁ ⟶[V] Y₁
  let B : V := X₂ ⟶[V] Y₂
  let C : V := X₃ ⟶[V] Y₃
  let D : V := (X₂ ⊗ X₃) ⟶[V] (Y₂ ⊗ Y₃)
  let H : V := (X₁ ⊗ (X₂ ⊗ X₃)) ⟶[V] (Y₁ ⊗ (Y₂ ⊗ Y₃))
  let a : U ⟶ A := eHomEquiv V f
  let b : U ⟶ B := eHomEquiv V g
  let c : U ⟶ C := eHomEquiv V h
  let t : B ⊗ C ⟶ D := copowerTensorHom.{u, v, w} I
    (oldObj I X₂) (oldObj I Y₂) (oldObj I X₃) (oldObj I Y₃)
  let t' : A ⊗ D ⟶ H := copowerTensorHom.{u, v, w} I
    (oldObj I X₁) (oldObj I Y₁)
    (oldObj I X₂ ⊗ oldObj I X₃) (oldObj I Y₂ ⊗ oldObj I Y₃)
  let p : U ⟶ A ⊗ (B ⊗ C) := pointPair a (pointPair b c)
  have hInner : eHomEquiv V (g ⊗ₘ h) = pointPair b c ≫ t :=
    underlyingTensorPoint.{u, v, w} I g h
  have hOuter : eHomEquiv V (f ⊗ₘ (g ⊗ₘ h)) =
      pointPair a (eHomEquiv V (g ⊗ₘ h)) ≫ t' :=
    underlyingTensorPoint.{u, v, w} I f (g ⊗ₘ h)
  have hReplace : pointPair a (eHomEquiv V (g ⊗ₘ h)) ≫ t' =
      pointPair a (pointPair b c ≫ t) ≫ t' :=
    congrArg (fun z : U ⟶ D => pointPair a z ≫ t') hInner
  have hNatural : p ≫ A ◁ t = pointPair a (pointPair b c ≫ t) :=
    (congrArg (fun z => p ≫ z) (id_tensorHom A t).symm).trans
      ((pointPairNatural a (pointPair b c) (𝟙 A) t).trans
        (congrArg (fun z => pointPair z (pointPair b c ≫ t)) (Category.comp_id a)))
  have hLast : pointPair a (pointPair b c ≫ t) ≫ t' = p ≫ A ◁ t ≫ t' :=
    (congrArg (fun z : U ⟶ A ⊗ D => z ≫ t') hNatural.symm).trans
      (Category.assoc p (A ◁ t) t')
  exact hOuter.trans (hReplace.trans hLast)

/-- The original restriction associator is natural on all native arrows. -/
theorem copowerUnderlyingAssociator_naturality
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : CopowerUnderlying.{u, v, w} I}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫
        (copowerRestriction.{u, v, w} I).map
          (α_ ((show I from Y₁)) ((show I from Y₂)) ((show I from Y₃))).hom =
      (copowerRestriction.{u, v, w} I).map
          (α_ ((show I from X₁)) ((show I from X₂)) ((show I from X₃))).hom ≫
        (f ⊗ₘ (g ⊗ₘ h)) := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let K := CopowerUnderlying.{u, v, w} I
  let A₀ : K := (X₁ ⊗ X₂) ⊗ X₃
  let A₁ : K := (Y₁ ⊗ Y₂) ⊗ Y₃
  let B₀ : K := X₁ ⊗ (X₂ ⊗ X₃)
  let B₁ : K := Y₁ ⊗ (Y₂ ⊗ Y₃)
  let l : A₀ ⟶ A₁ := (f ⊗ₘ g) ⊗ₘ h
  let r : B₀ ⟶ B₁ := f ⊗ₘ (g ⊗ₘ h)
  let a₀ : A₀ ⟶ B₀ := (copowerRestriction.{u, v, w} I).map
    (α_ (oldObj I X₁) (oldObj I X₂) (oldObj I X₃)).hom
  let a₁ : A₁ ⟶ B₁ := (copowerRestriction.{u, v, w} I).map
    (α_ (oldObj I Y₁) (oldObj I Y₂) (oldObj I Y₃)).hom
  let H₁ : V := X₁ ⟶[V] Y₁
  let H₂ : V := X₂ ⟶[V] Y₂
  let H₃ : V := X₃ ⟶[V] Y₃
  let HL : V := A₀ ⟶[V] A₁
  let HR : V := B₀ ⟶[V] B₁
  let HT : V := A₀ ⟶[V] B₁
  let tL : (H₁ ⊗ H₂) ⊗ H₃ ⟶ HL :=
    copowerTensorHom.{u, v, w} I
      (oldObj I X₁) (oldObj I Y₁) (oldObj I X₂) (oldObj I Y₂) ▷ H₃ ≫
    copowerTensorHom.{u, v, w} I
      (oldObj I X₁ ⊗ oldObj I X₂) (oldObj I Y₁ ⊗ oldObj I Y₂)
      (oldObj I X₃) (oldObj I Y₃)
  let tR : H₁ ⊗ (H₂ ⊗ H₃) ⟶ HR :=
    H₁ ◁ copowerTensorHom.{u, v, w} I
      (oldObj I X₂) (oldObj I Y₂) (oldObj I X₃) (oldObj I Y₃) ≫
    copowerTensorHom.{u, v, w} I
      (oldObj I X₁) (oldObj I Y₁)
      (oldObj I X₂ ⊗ oldObj I X₃) (oldObj I Y₂ ⊗ oldObj I Y₃)
  let post : HL ⟶ HT := gamma.{u, v, w}.map
    (↾fun z : ((oldObj I X₁ ⊗ oldObj I X₂) ⊗ oldObj I X₃) ⟶
        ((oldObj I Y₁ ⊗ oldObj I Y₂) ⊗ oldObj I Y₃) =>
      z ≫ (α_ (oldObj I Y₁) (oldObj I Y₂) (oldObj I Y₃)).hom)
  let pre : HR ⟶ HT := gamma.{u, v, w}.map
    (↾fun z : (oldObj I X₁ ⊗ (oldObj I X₂ ⊗ oldObj I X₃)) ⟶
        (oldObj I Y₁ ⊗ (oldObj I Y₂ ⊗ oldObj I Y₃)) =>
      (α_ (oldObj I X₁) (oldObj I X₂) (oldObj I X₃)).hom ≫ z)
  let x : U ⟶ H₁ := eHomEquiv V f
  let y : U ⟶ H₂ := eHomEquiv V g
  let z : U ⟶ H₃ := eHomEquiv V h
  let p : U ⟶ (H₁ ⊗ H₂) ⊗ H₃ := pointPair (pointPair x y) z
  let q : U ⟶ H₁ ⊗ (H₂ ⊗ H₃) := pointPair x (pointPair y z)
  have hTensorL : eHomEquiv V l = p ≫ tL :=
    underlyingTensorPointLeft.{u, v, w} I f g h
  have hTensorR : eHomEquiv V r = q ≫ tR :=
    underlyingTensorPointRight.{u, v, w} I f g h
  have hPost : eHomWhiskerLeft V A₀ a₁ = post :=
    restrictionPostcomp.{u, v, w} I
      (α_ (oldObj I Y₁) (oldObj I Y₂) (oldObj I Y₃)).hom
  have hPre : eHomWhiskerRight V a₀ B₁ = pre :=
    restrictionPrecomp.{u, v, w} I
      (α_ (oldObj I X₁) (oldObj I X₂) (oldObj I X₃)).hom
  have hFull : tL ≫ post = (α_ H₁ H₂ H₃).hom ≫ tR ≫ pre :=
    tensorHomAssociativity.{u, v, w} I
      (oldObj I X₁) (oldObj I Y₁) (oldObj I X₂) (oldObj I Y₂)
      (oldObj I X₃) (oldObj I Y₃)
  have hPair : p ≫ (α_ H₁ H₂ H₃).hom = q := pointPairAssociativity x y z
  have hLeft : eHomEquiv V (l ≫ a₁) = p ≫ tL ≫ post :=
    (eHomEquiv_comp_eHomWhiskerLeft (V := V) (C := K) l a₁).symm.trans
      ((congrArg₂ (fun a b => a ≫ b) hTensorL hPost).trans (Category.assoc p tL post))
  have hRight : eHomEquiv V (a₀ ≫ r) = q ≫ tR ≫ pre :=
    (eHomEquiv_comp_eHomWhiskerRight (V := V) (C := K) a₀ r).symm.trans
      ((congrArg₂ (fun a b => a ≫ b) hTensorR hPre).trans (Category.assoc q tR pre))
  have hMiddle : p ≫ tL ≫ post =
      p ≫ (α_ H₁ H₂ H₃).hom ≫ tR ≫ pre := by
    simpa only [Category.assoc] using congrArg
      (fun a : (H₁ ⊗ H₂) ⊗ H₃ ⟶ HT => p ≫ a) hFull
  have hLast : p ≫ (α_ H₁ H₂ H₃).hom ≫ tR ≫ pre = q ≫ tR ≫ pre := by
    simpa only [Category.assoc] using congrArg (fun a => a ≫ tR ≫ pre) hPair
  apply (eHomEquiv V).injective
  exact hLeft.trans (hMiddle.trans (hLast.trans hRight.symm))

/-- The original restriction left unitor is natural on all native arrows. -/
theorem copowerUnderlyingLeftUnitor_naturality
    {X Y : CopowerUnderlying.{u, v, w} I} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (CopowerUnderlying.{u, v, w} I)) ⊗ₘ f) ≫
        (copowerRestriction.{u, v, w} I).map (λ_ ((show I from Y))).hom =
      (copowerRestriction.{u, v, w} I).map (λ_ ((show I from X))).hom ≫ f := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let K := CopowerUnderlying.{u, v, w} I
  let UC : K := 𝟙_ K
  let A₀ : K := UC ⊗ X
  let A₁ : K := UC ⊗ Y
  let l : A₀ ⟶ A₁ := 𝟙 UC ⊗ₘ f
  let a₀ : A₀ ⟶ X := (copowerRestriction.{u, v, w} I).map (λ_ (oldObj I X)).hom
  let a₁ : A₁ ⟶ Y := (copowerRestriction.{u, v, w} I).map (λ_ (oldObj I Y)).hom
  let H : V := X ⟶[V] Y
  let E : V := UC ⟶[V] UC
  let HL : V := A₀ ⟶[V] A₁
  let HT : V := A₀ ⟶[V] Y
  let e : U ⟶ E := eId V UC
  let p : U ⟶ H := eHomEquiv V f
  let t : E ⊗ H ⟶ HL := copowerTensorHom.{u, v, w} I
    (𝟙_ I) (𝟙_ I) (oldObj I X) (oldObj I Y)
  let L : H ⟶ HL := (λ_ H).inv ≫ (e ⊗ₘ 𝟙 H) ≫ t
  let post : HL ⟶ HT := gamma.{u, v, w}.map
    (↾fun z : (𝟙_ I ⊗ oldObj I X) ⟶ (𝟙_ I ⊗ oldObj I Y) =>
      z ≫ (λ_ (oldObj I Y)).hom)
  let pre : H ⟶ HT := gamma.{u, v, w}.map
    (↾fun z : oldObj I X ⟶ oldObj I Y => (λ_ (oldObj I X)).hom ≫ z)
  have hTensor : eHomEquiv V l = pointPair (eHomEquiv V (𝟙 UC)) p ≫ t :=
    underlyingTensorPoint.{u, v, w} I (𝟙 UC) f
  have hId : eHomEquiv V (𝟙 UC) = e := eHomEquiv_id V UC
  have hPoint : eHomEquiv V l = pointPair e p ≫ t :=
    hTensor.trans (congrArg (fun z => pointPair z p ≫ t) hId)
  have hPair : pointPair e p = p ≫ (λ_ H).inv ≫ (e ⊗ₘ 𝟙 H) :=
    (leftUnitor_inv_comp_tensorHom e p).trans
      (congrArg (fun z => p ≫ (λ_ H).inv ≫ z) (tensorHom_id e H).symm)
  have hShift : pointPair e p ≫ t = p ≫ L := by
    simpa only [L, Category.assoc] using congrArg (fun z : U ⟶ E ⊗ H => z ≫ t) hPair
  have hFull : L ≫ post = pre :=
    tensorHomLeftUnit.{u, v, w} I (oldObj I X) (oldObj I Y)
  have hPost : eHomWhiskerLeft V A₀ a₁ = post :=
    restrictionPostcomp.{u, v, w} I (λ_ (oldObj I Y)).hom
  have hPre : eHomWhiskerRight V a₀ Y = pre :=
    restrictionPrecomp.{u, v, w} I (λ_ (oldObj I X)).hom
  have hLeft : eHomEquiv V (l ≫ a₁) = p ≫ L ≫ post :=
    (eHomEquiv_comp_eHomWhiskerLeft (V := V) (C := K) l a₁).symm.trans
      ((congrArg₂ (fun a b => a ≫ b) (hPoint.trans hShift) hPost).trans
        (Category.assoc p L post))
  have hRight : eHomEquiv V (a₀ ≫ f) = p ≫ pre :=
    (eHomEquiv_comp_eHomWhiskerRight (V := V) (C := K) a₀ f).symm.trans
      (congrArg (fun z => p ≫ z) hPre)
  have hMiddle : p ≫ L ≫ post = p ≫ pre := by
    simpa only [Category.assoc] using congrArg (fun z : H ⟶ HT => p ≫ z) hFull
  apply (eHomEquiv V).injective
  exact hLeft.trans (hMiddle.trans hRight.symm)

/-- The original restriction right unitor is natural on all native arrows. -/
theorem copowerUnderlyingRightUnitor_naturality
    {X Y : CopowerUnderlying.{u, v, w} I} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ (CopowerUnderlying.{u, v, w} I))) ≫
        (copowerRestriction.{u, v, w} I).map (ρ_ ((show I from Y))).hom =
      (copowerRestriction.{u, v, w} I).map (ρ_ ((show I from X))).hom ≫ f := by
  let V := PointedCGWH.{u, max v w}
  let U : V := 𝟙_ V
  let K := CopowerUnderlying.{u, v, w} I
  let UC : K := 𝟙_ K
  let A₀ : K := X ⊗ UC
  let A₁ : K := Y ⊗ UC
  let l : A₀ ⟶ A₁ := f ⊗ₘ 𝟙 UC
  let a₀ : A₀ ⟶ X := (copowerRestriction.{u, v, w} I).map (ρ_ (oldObj I X)).hom
  let a₁ : A₁ ⟶ Y := (copowerRestriction.{u, v, w} I).map (ρ_ (oldObj I Y)).hom
  let H : V := X ⟶[V] Y
  let E : V := UC ⟶[V] UC
  let HL : V := A₀ ⟶[V] A₁
  let HT : V := A₀ ⟶[V] Y
  let e : U ⟶ E := eId V UC
  let p : U ⟶ H := eHomEquiv V f
  let t : H ⊗ E ⟶ HL := copowerTensorHom.{u, v, w} I
    (oldObj I X) (oldObj I Y) (𝟙_ I) (𝟙_ I)
  let L : H ⟶ HL := (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫ t
  let post : HL ⟶ HT := gamma.{u, v, w}.map
    (↾fun z : (oldObj I X ⊗ 𝟙_ I) ⟶ (oldObj I Y ⊗ 𝟙_ I) =>
      z ≫ (ρ_ (oldObj I Y)).hom)
  let pre : H ⟶ HT := gamma.{u, v, w}.map
    (↾fun z : oldObj I X ⟶ oldObj I Y => (ρ_ (oldObj I X)).hom ≫ z)
  have hTensor : eHomEquiv V l = pointPair p (eHomEquiv V (𝟙 UC)) ≫ t :=
    underlyingTensorPoint.{u, v, w} I f (𝟙 UC)
  have hId : eHomEquiv V (𝟙 UC) = e := eHomEquiv_id V UC
  have hPoint : eHomEquiv V l = pointPair p e ≫ t :=
    hTensor.trans (congrArg (fun z => pointPair p z ≫ t) hId)
  have hPair : pointPair p e = p ≫ (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) := by
    have hUnit : (λ_ U).inv = (ρ_ U).inv := unitors_inv_equal
    exact (congrArg (fun z : U ⟶ U ⊗ U => z ≫ (p ⊗ₘ e)) hUnit).trans
      ((rightUnitor_inv_comp_tensorHom p e).trans
        (congrArg (fun z => p ≫ (ρ_ H).inv ≫ z) (id_tensorHom H e).symm))
  have hShift : pointPair p e ≫ t = p ≫ L := by
    simpa only [L, Category.assoc] using congrArg (fun z : U ⟶ H ⊗ E => z ≫ t) hPair
  have hFull : L ≫ post = pre :=
    tensorHomRightUnit.{u, v, w} I (oldObj I X) (oldObj I Y)
  have hPost : eHomWhiskerLeft V A₀ a₁ = post :=
    restrictionPostcomp.{u, v, w} I (ρ_ (oldObj I Y)).hom
  have hPre : eHomWhiskerRight V a₀ Y = pre :=
    restrictionPrecomp.{u, v, w} I (ρ_ (oldObj I X)).hom
  have hLeft : eHomEquiv V (l ≫ a₁) = p ≫ L ≫ post :=
    (eHomEquiv_comp_eHomWhiskerLeft (V := V) (C := K) l a₁).symm.trans
      ((congrArg₂ (fun a b => a ≫ b) (hPoint.trans hShift) hPost).trans
        (Category.assoc p L post))
  have hRight : eHomEquiv V (a₀ ≫ f) = p ≫ pre :=
    (eHomEquiv_comp_eHomWhiskerRight (V := V) (C := K) a₀ f).symm.trans
      (congrArg (fun z => p ≫ z) hPre)
  have hMiddle : p ≫ L ≫ post = p ≫ pre := by
    simpa only [Category.assoc] using congrArg (fun z : H ⟶ HT => p ≫ z) hFull
  apply (eHomEquiv V).injective
  exact hLeft.trans (hMiddle.trans hRight.symm)

/-- The original restriction associators satisfy the native pentagon. -/
theorem copowerUnderlyingPentagon (W X Y Z : CopowerUnderlying.{u, v, w} I) :
    let R := copowerRestriction.{u, v, w} I
    let w : I := (show I from W)
    let x : I := (show I from X)
    let y : I := (show I from Y)
    let z : I := (show I from Z)
    (R.map (α_ w x y).hom ⊗ₘ 𝟙 Z) ≫ R.map (α_ w (x ⊗ y) z).hom ≫
        (𝟙 W ⊗ₘ R.map (α_ x y z).hom) =
      R.map (α_ (w ⊗ x) y z).hom ≫ R.map (α_ w x (y ⊗ z)).hom := by
  let R := copowerRestriction.{u, v, w} I
  let w : I := oldObj I W
  let x : I := oldObj I X
  let y : I := oldObj I Y
  let z : I := oldObj I Z
  have h : ((α_ w x y).hom ⊗ₘ 𝟙 z) ≫ (α_ w (x ⊗ y) z).hom ≫
      (𝟙 w ⊗ₘ (α_ x y z).hom) =
        (α_ (w ⊗ x) y z).hom ≫ (α_ w x (y ⊗ z)).hom := by
    simpa only [tensorHom_id, id_tensorHom] using pentagon w x y z
  have hMapped : R.map ((α_ w x y).hom ⊗ₘ 𝟙 z) ≫
      R.map (α_ w (x ⊗ y) z).hom ≫ R.map (𝟙 w ⊗ₘ (α_ x y z).hom) =
        R.map (α_ (w ⊗ x) y z).hom ≫ R.map (α_ w x (y ⊗ z)).hom := by
    simpa only [Functor.map_comp] using congrArg R.map h
  have hLeft : R.map ((α_ w x y).hom ⊗ₘ 𝟙 z) =
      R.map (α_ w x y).hom ⊗ₘ 𝟙 Z :=
    (restrictionTensor.{u, v, w} I (α_ w x y).hom (𝟙 z)).symm.trans
      (congrArg (fun a => R.map (α_ w x y).hom ⊗ₘ a) (R.map_id z))
  have hRight : R.map (𝟙 w ⊗ₘ (α_ x y z).hom) =
      𝟙 W ⊗ₘ R.map (α_ x y z).hom :=
    (restrictionTensor.{u, v, w} I (𝟙 w) (α_ x y z).hom).symm.trans
      (congrArg (fun a => a ⊗ₘ R.map (α_ x y z).hom) (R.map_id w))
  have hFirst := congrArg
    (fun a => a ≫ R.map (α_ w (x ⊗ y) z).hom ≫ R.map (𝟙 w ⊗ₘ (α_ x y z).hom)) hLeft
  have hLast := congrArg
    (fun a => (R.map (α_ w x y).hom ⊗ₘ 𝟙 Z) ≫ R.map (α_ w (x ⊗ y) z).hom ≫ a) hRight
  exact (hFirst.trans hLast).symm.trans hMapped

/-- The original restriction associator and unitors satisfy the native triangle. -/
theorem copowerUnderlyingTriangle (X Y : CopowerUnderlying.{u, v, w} I) :
    (α_ X (𝟙_ (CopowerUnderlying.{u, v, w} I)) Y).hom ≫ (𝟙 X ⊗ₘ (λ_ Y).hom) =
      (ρ_ X).hom ⊗ₘ 𝟙 Y := by
  let R := copowerRestriction.{u, v, w} I
  let x : I := oldObj I X
  let y : I := oldObj I Y
  have h : (α_ x (𝟙_ I) y).hom ≫ (𝟙 x ⊗ₘ (λ_ y).hom) =
      (ρ_ x).hom ⊗ₘ 𝟙 y := by
    simpa only [tensorHom_id, id_tensorHom] using triangle x y
  have hMapped : R.map (α_ x (𝟙_ I) y).hom ≫
      R.map (𝟙 x ⊗ₘ (λ_ y).hom) = R.map ((ρ_ x).hom ⊗ₘ 𝟙 y) :=
    (R.map_comp (α_ x (𝟙_ I) y).hom (𝟙 x ⊗ₘ (λ_ y).hom)).symm.trans
      (congrArg R.map h)
  have hLeft : R.map (𝟙 x ⊗ₘ (λ_ y).hom) = R.map (𝟙 x) ⊗ₘ R.map (λ_ y).hom :=
    (restrictionTensor.{u, v, w} I (𝟙 x) (λ_ y).hom).symm
  have hRight : R.map ((ρ_ x).hom ⊗ₘ 𝟙 y) = R.map (ρ_ x).hom ⊗ₘ R.map (𝟙 y) :=
    (restrictionTensor.{u, v, w} I (ρ_ x).hom (𝟙 y)).symm
  have hX : R.map (𝟙 x) = 𝟙 X := R.map_id x
  have hY : R.map (𝟙 y) = 𝟙 Y := R.map_id y
  change R.map (α_ x (𝟙_ I) y).hom ≫ (𝟙 X ⊗ₘ R.map (λ_ y).hom) =
    R.map (ρ_ x).hom ⊗ₘ 𝟙 Y
  exact (congrArg (fun z => R.map (α_ x (𝟙_ I) y).hom ≫ z)
    (hLeft.trans (congrArg (fun z => z ⊗ₘ R.map (λ_ y).hom) hX))).symm.trans
      (hMapped.trans (hRight.trans (congrArg (fun z => R.map (ρ_ x).hom ⊗ₘ z) hY)))

/-- The standard monoidal structure acts on all native unit-point arrows. -/
@[instance_reducible]
def copowerUnderlyingMonoidal : MonoidalCategory (CopowerUnderlying.{u, v, w} I) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := copowerUnderlyingTensorHom_id.{u, v, w} I)
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun {_ _} _ _ => rfl)
    (tensorHom_comp_tensorHom := copowerUnderlyingTensorHom_comp.{u, v, w} I)
    (associator_naturality := copowerUnderlyingAssociator_naturality.{u, v, w} I)
    (leftUnitor_naturality := copowerUnderlyingLeftUnitor_naturality.{u, v, w} I)
    (rightUnitor_naturality := copowerUnderlyingRightUnitor_naturality.{u, v, w} I)
    (pentagon := copowerUnderlyingPentagon.{u, v, w} I)
    (triangle := copowerUnderlyingTriangle.{u, v, w} I)

attribute [local instance] copowerUnderlyingMonoidal

/-- Original tensor arrows retain the literal restriction map. -/
theorem copowerUnderlyingMonoidal_tensor_original {i i' j j' : I}
    (f : i ⟶ i') (g : j ⟶ j') :
    (copowerRestriction.{u, v, w} I).map f ⊗ₘ
        (copowerRestriction.{u, v, w} I).map g =
      (copowerRestriction.{u, v, w} I).map (f ⊗ₘ g) :=
  restrictionTensor.{u, v, w} I f g

/-- Full enriched monoidal data using the original native Hom tensor on the associated category. -/
def copowerUnderlyingMonoidalData :
    EnrichedMonoidalCategoryData PointedCGWH.{u, max v w} (CopowerUnderlying.{u, v, w} I) where
  tensorMap X X' Y Y' := copowerTensorHom.{u, v, w} I
    ((show I from X)) ((show I from X')) ((show I from Y)) ((show I from Y'))
  tensorMap_comp X X' X'' Y Y' Y'' :=
    copowerTensorHom_comp.{u, v, w} I
      ((show I from X)) ((show I from X')) ((show I from X''))
      ((show I from Y)) ((show I from Y')) ((show I from Y''))
  tensorMap_eHomEquiv {X X' Y Y'} f g := by
    change (λ_ (𝟙_ PointedCGWH.{u, max v w})).inv ≫
        (eHomEquiv PointedCGWH.{u, max v w} f ⊗ₘ
          eHomEquiv PointedCGWH.{u, max v w} g) ≫
        copowerTensorHom.{u, v, w} I
          ((show I from X)) ((show I from X')) ((show I from Y)) ((show I from Y')) =
      pointPair (eHomEquiv PointedCGWH.{u, max v w} f)
          (eHomEquiv PointedCGWH.{u, max v w} g) ≫
        copowerTensorHom.{u, v, w} I
          ((show I from X)) ((show I from X')) ((show I from Y)) ((show I from Y'))
    exact (Category.assoc _ _ _).symm
  associatorNaturality X X' Y Y' Z Z' := by
    let V := PointedCGWH.{u, max v w}
    let U : V := 𝟙_ V
    let H : V := ((X ⟶[V] X') ⊗ (Y ⟶[V] Y')) ⊗ (Z ⟶[V] Z')
    let L : H ⟶ (((X ⊗ Y) ⊗ Z) ⟶[V] ((X' ⊗ Y') ⊗ Z')) :=
      copowerTensorHom.{u, v, w} I
        ((show I from X)) ((show I from X')) ((show I from Y)) ((show I from Y')) ▷ (Z ⟶[V] Z') ≫
      copowerTensorHom.{u, v, w} I
        ((show I from X) ⊗ (show I from Y)) ((show I from X') ⊗ (show I from Y'))
        ((show I from Z)) ((show I from Z'))
    let R : H ⟶ ((X ⊗ (Y ⊗ Z)) ⟶[V] (X' ⊗ (Y' ⊗ Z'))) :=
      (α_ (X ⟶[V] X') (Y ⟶[V] Y') (Z ⟶[V] Z')).hom ≫
      (X ⟶[V] X') ◁ copowerTensorHom.{u, v, w} I
        ((show I from Y)) ((show I from Y')) ((show I from Z)) ((show I from Z')) ≫
      copowerTensorHom.{u, v, w} I
        ((show I from X)) ((show I from X'))
        ((show I from Y) ⊗ (show I from Z)) ((show I from Y') ⊗ (show I from Z'))
    let a : U ⟶ (((X ⊗ Y) ⊗ Z) ⟶[V] (X ⊗ (Y ⊗ Z))) :=
      basedDiscreteIncl.{u, v, w}
        ((((show I from X) ⊗ (show I from Y)) ⊗ (show I from Z)) ⟶
          ((show I from X) ⊗ ((show I from Y) ⊗ (show I from Z))))
        (α_ ((show I from X)) ((show I from Y)) ((show I from Z))).hom
    let a' : U ⟶ (((X' ⊗ Y') ⊗ Z') ⟶[V] (X' ⊗ (Y' ⊗ Z'))) :=
      basedDiscreteIncl.{u, v, w}
        ((((show I from X') ⊗ (show I from Y')) ⊗ (show I from Z')) ⟶
          ((show I from X') ⊗ ((show I from Y') ⊗ (show I from Z'))))
        (α_ ((show I from X')) ((show I from Y')) ((show I from Z'))).hom
    change (β_ U H).hom ≫ (L ⊗ₘ a') ≫
        eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z') (X' ⊗ (Y' ⊗ Z')) =
      (a ⊗ₘ R) ≫ eComp V ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) (X' ⊗ (Y' ⊗ Z'))
    have hUnitBraid : (λ_ H).inv ≫ (β_ U H).hom = (ρ_ H).inv :=
      leftUnitor_inv_braiding H
    have hFirst : (λ_ H).inv ≫ ((β_ U H).hom ≫ (L ⊗ₘ a') ≫
        eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z') (X' ⊗ (Y' ⊗ Z'))) =
        (ρ_ H).inv ≫ (L ⊗ₘ a') ≫
          eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z') (X' ⊗ (Y' ⊗ Z')) :=
      (Category.assoc (λ_ H).inv (β_ U H).hom
        ((L ⊗ₘ a') ≫ eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z') (X' ⊗ (Y' ⊗ Z')))).symm.trans
        (congrArg (fun q : H ⟶ H ⊗ U =>
          q ≫ (L ⊗ₘ a') ≫ eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z') (X' ⊗ (Y' ⊗ Z'))) hUnitBraid)
    let HL : V := ((X ⊗ Y) ⊗ Z) ⟶[V] ((X' ⊗ Y') ⊗ Z')
    let HR : V := (X ⊗ (Y ⊗ Z)) ⟶[V] (X' ⊗ (Y' ⊗ Z'))
    let AS : V := ((X ⊗ Y) ⊗ Z) ⟶[V] (X ⊗ (Y ⊗ Z))
    let AT : V := ((X' ⊗ Y') ⊗ Z') ⟶[V] (X' ⊗ (Y' ⊗ Z'))
    let T : V := ((X ⊗ Y) ⊗ Z) ⟶[V] (X' ⊗ (Y' ⊗ Z'))
    let cL : HL ⊗ AT ⟶ T := eComp V ((X ⊗ Y) ⊗ Z) ((X' ⊗ Y') ⊗ Z') (X' ⊗ (Y' ⊗ Z'))
    let cR : AS ⊗ HR ⟶ T := eComp V ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) (X' ⊗ (Y' ⊗ Z'))
    let post : HL ⟶ T := gamma.{u, v, w}.map
      (↾fun q : (((show I from X) ⊗ (show I from Y)) ⊗ (show I from Z)) ⟶
          (((show I from X') ⊗ (show I from Y')) ⊗ (show I from Z')) =>
        q ≫ (α_ ((show I from X')) ((show I from Y')) ((show I from Z'))).hom)
    let pre : HR ⟶ T := gamma.{u, v, w}.map
      (↾fun q : ((show I from X) ⊗ ((show I from Y) ⊗ (show I from Z))) ⟶
          ((show I from X') ⊗ ((show I from Y') ⊗ (show I from Z'))) =>
        (α_ ((show I from X)) ((show I from Y)) ((show I from Z))).hom ≫ q)
    have hPost : (ρ_ HL).inv ≫ HL ◁ a' ≫ cL = post :=
      originalPostcomp.{u, v, w} I (α_ ((show I from X')) ((show I from Y')) ((show I from Z'))).hom
    have hPre : (λ_ HR).inv ≫ a ▷ HR ≫ cR = pre :=
      originalPrecomp.{u, v, w} I (α_ ((show I from X)) ((show I from Y)) ((show I from Z))).hom
    have hFull : L ≫ post = (R) ≫ pre :=
      tensorHomAssociativity.{u, v, w} I
        ((show I from X)) ((show I from X')) ((show I from Y)) ((show I from Y'))
        ((show I from Z)) ((show I from Z'))
    have hLeftPair : (ρ_ H).inv ≫ (L ⊗ₘ a') ≫ cL =
        L ≫ ((ρ_ HL).inv ≫ HL ◁ a' ≫ cL) := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⟶ HL ⊗ AT => q ≫ cL) (rightUnitor_inv_comp_tensorHom L a')
    have hRightPair : (λ_ H).inv ≫ (a ⊗ₘ (R)) ≫ cR =
        (R) ≫ ((λ_ HR).inv ≫ a ▷ HR ≫ cR) := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⟶ AS ⊗ HR => q ≫ cR) (leftUnitor_inv_comp_tensorHom a (R))
    have hLeft : (ρ_ H).inv ≫ (L ⊗ₘ a') ≫ cL = L ≫ post :=
      hLeftPair.trans (congrArg (fun q : HL ⟶ T => L ≫ q) hPost)
    have hRight : (λ_ H).inv ≫ (a ⊗ₘ (R)) ≫ cR = (R) ≫ pre :=
      hRightPair.trans (congrArg (fun q : HR ⟶ T => (R) ≫ q) hPre)
    apply (cancel_epi (λ_ H).inv).1
    exact hFirst.trans (hLeft.trans (hFull.trans hRight.symm))
  leftUnitorNaturality X X' := by
    let V := PointedCGWH.{u, max v w}
    let U : V := 𝟙_ V
    let H : V := X ⟶[V] X'
    let L : H ⟶ ((𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) ⟶[V]
        (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X')) :=
      (λ_ H).inv ≫
        (eId V (𝟙_ (CopowerUnderlying.{u, v, w} I)) ⊗ₘ 𝟙 H) ≫
        copowerTensorHom.{u, v, w} I (𝟙_ I) (𝟙_ I) ((show I from X)) ((show I from X'))
    let a : U ⟶ ((𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) ⟶[V] X) :=
      basedDiscreteIncl.{u, v, w} ((𝟙_ I ⊗ (show I from X)) ⟶ (show I from X))
        (λ_ ((show I from X))).hom
    let a' : U ⟶ ((𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') ⟶[V] X') :=
      basedDiscreteIncl.{u, v, w} ((𝟙_ I ⊗ (show I from X')) ⟶ (show I from X'))
        (λ_ ((show I from X'))).hom
    change (β_ U H).hom ≫ (L ⊗ₘ a') ≫
        eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X)
          (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') X' =
      (a ⊗ₘ 𝟙 H) ≫ eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) X X'
    have hUnitBraid : (λ_ H).inv ≫ (β_ U H).hom = (ρ_ H).inv :=
      leftUnitor_inv_braiding H
    have hFirst : (λ_ H).inv ≫ ((β_ U H).hom ≫ (L ⊗ₘ a') ≫
        eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X)
          (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') X') =
        (ρ_ H).inv ≫ (L ⊗ₘ a') ≫
          eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X)
          (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') X' :=
      (Category.assoc (λ_ H).inv (β_ U H).hom
        ((L ⊗ₘ a') ≫ eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X)
          (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') X')).symm.trans
        (congrArg (fun q : H ⟶ H ⊗ U =>
          q ≫ (L ⊗ₘ a') ≫ eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X)
          (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') X') hUnitBraid)
    let HL : V := (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) ⟶[V]
        (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X')
    let HR : V := H
    let AS : V := (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) ⟶[V] X
    let AT : V := (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') ⟶[V] X'
    let T : V := (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) ⟶[V] X'
    let cL : HL ⊗ AT ⟶ T := eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X)
        (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X') X'
    let cR : AS ⊗ HR ⟶ T := eComp V (𝟙_ (CopowerUnderlying.{u, v, w} I) ⊗ X) X X'
    let post : HL ⟶ T := gamma.{u, v, w}.map
      (↾fun q : (𝟙_ I ⊗ (show I from X)) ⟶ (𝟙_ I ⊗ (show I from X')) =>
        q ≫ (λ_ ((show I from X'))).hom)
    let pre : HR ⟶ T := gamma.{u, v, w}.map
      (↾fun q : (show I from X) ⟶ (show I from X') => (λ_ ((show I from X))).hom ≫ q)
    have hPost : (ρ_ HL).inv ≫ HL ◁ a' ≫ cL = post :=
      originalPostcomp.{u, v, w} I (λ_ ((show I from X'))).hom
    have hPre : (λ_ HR).inv ≫ a ▷ HR ≫ cR = pre :=
      originalPrecomp.{u, v, w} I (λ_ ((show I from X))).hom
    have hFull : L ≫ post = (𝟙 H) ≫ pre :=
      (tensorHomLeftUnit.{u, v, w} I ((show I from X)) ((show I from X'))).trans
        (Category.id_comp pre).symm
    have hLeftPair : (ρ_ H).inv ≫ (L ⊗ₘ a') ≫ cL =
        L ≫ ((ρ_ HL).inv ≫ HL ◁ a' ≫ cL) := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⟶ HL ⊗ AT => q ≫ cL) (rightUnitor_inv_comp_tensorHom L a')
    have hRightPair : (λ_ H).inv ≫ (a ⊗ₘ (𝟙 H)) ≫ cR =
        (𝟙 H) ≫ ((λ_ HR).inv ≫ a ▷ HR ≫ cR) := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⟶ AS ⊗ HR => q ≫ cR) (leftUnitor_inv_comp_tensorHom a (𝟙 H))
    have hLeft : (ρ_ H).inv ≫ (L ⊗ₘ a') ≫ cL = L ≫ post :=
      hLeftPair.trans (congrArg (fun q : HL ⟶ T => L ≫ q) hPost)
    have hRight : (λ_ H).inv ≫ (a ⊗ₘ (𝟙 H)) ≫ cR = (𝟙 H) ≫ pre :=
      hRightPair.trans (congrArg (fun q : HR ⟶ T => (𝟙 H) ≫ q) hPre)
    apply (cancel_epi (λ_ H).inv).1
    exact hFirst.trans (hLeft.trans (hFull.trans hRight.symm))
  rightUnitorNaturality X X' := by
    let V := PointedCGWH.{u, max v w}
    let U : V := 𝟙_ V
    let H : V := X ⟶[V] X'
    let L : H ⟶ ((X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V]
        (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))) :=
      (ρ_ H).inv ≫
        (𝟙 H ⊗ₘ eId V (𝟙_ (CopowerUnderlying.{u, v, w} I))) ≫
        copowerTensorHom.{u, v, w} I ((show I from X)) ((show I from X')) (𝟙_ I) (𝟙_ I)
    let a : U ⟶ ((X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V] X) :=
      basedDiscreteIncl.{u, v, w} (((show I from X) ⊗ 𝟙_ I) ⟶ (show I from X))
        (ρ_ ((show I from X))).hom
    let a' : U ⟶ ((X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V] X') :=
      basedDiscreteIncl.{u, v, w} (((show I from X') ⊗ 𝟙_ I) ⟶ (show I from X'))
        (ρ_ ((show I from X'))).hom
    change (β_ U H).hom ≫ (L ⊗ₘ a') ≫
        eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
          (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X' =
      (a ⊗ₘ 𝟙 H) ≫ eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X X'
    have hUnitBraid : (λ_ H).inv ≫ (β_ U H).hom = (ρ_ H).inv :=
      leftUnitor_inv_braiding H
    have hFirst : (λ_ H).inv ≫ ((β_ U H).hom ≫ (L ⊗ₘ a') ≫
        eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
          (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X') =
        (ρ_ H).inv ≫ (L ⊗ₘ a') ≫
          eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
          (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X' :=
      (Category.assoc (λ_ H).inv (β_ U H).hom
        ((L ⊗ₘ a') ≫ eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
          (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X')).symm.trans
        (congrArg (fun q : H ⟶ H ⊗ U =>
          q ≫ (L ⊗ₘ a') ≫ eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
          (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X') hUnitBraid)
    let HL : V := (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V]
        (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
    let HR : V := H
    let AS : V := (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V] X
    let AT : V := (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V] X'
    let T : V := (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) ⟶[V] X'
    let cL : HL ⊗ AT ⟶ T := eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I))
        (X' ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X'
    let cR : AS ⊗ HR ⟶ T := eComp V (X ⊗ 𝟙_ (CopowerUnderlying.{u, v, w} I)) X X'
    let post : HL ⟶ T := gamma.{u, v, w}.map
      (↾fun q : ((show I from X) ⊗ 𝟙_ I) ⟶ ((show I from X') ⊗ 𝟙_ I) =>
        q ≫ (ρ_ ((show I from X'))).hom)
    let pre : HR ⟶ T := gamma.{u, v, w}.map
      (↾fun q : (show I from X) ⟶ (show I from X') => (ρ_ ((show I from X))).hom ≫ q)
    have hPost : (ρ_ HL).inv ≫ HL ◁ a' ≫ cL = post :=
      originalPostcomp.{u, v, w} I (ρ_ ((show I from X'))).hom
    have hPre : (λ_ HR).inv ≫ a ▷ HR ≫ cR = pre :=
      originalPrecomp.{u, v, w} I (ρ_ ((show I from X))).hom
    have hFull : L ≫ post = (𝟙 H) ≫ pre :=
      (tensorHomRightUnit.{u, v, w} I ((show I from X)) ((show I from X'))).trans
        (Category.id_comp pre).symm
    have hLeftPair : (ρ_ H).inv ≫ (L ⊗ₘ a') ≫ cL =
        L ≫ ((ρ_ HL).inv ≫ HL ◁ a' ≫ cL) := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⟶ HL ⊗ AT => q ≫ cL) (rightUnitor_inv_comp_tensorHom L a')
    have hRightPair : (λ_ H).inv ≫ (a ⊗ₘ (𝟙 H)) ≫ cR =
        (𝟙 H) ≫ ((λ_ HR).inv ≫ a ▷ HR ≫ cR) := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⟶ AS ⊗ HR => q ≫ cR) (leftUnitor_inv_comp_tensorHom a (𝟙 H))
    have hLeft : (ρ_ H).inv ≫ (L ⊗ₘ a') ≫ cL = L ≫ post :=
      hLeftPair.trans (congrArg (fun q : HL ⟶ T => L ≫ q) hPost)
    have hRight : (λ_ H).inv ≫ (a ⊗ₘ (𝟙 H)) ≫ cR = (𝟙 H) ≫ pre :=
      hRightPair.trans (congrArg (fun q : HR ⟶ T => (𝟙 H) ≫ q) hPre)
    apply (cancel_epi (λ_ H).inv).1
    exact hFirst.trans (hLeft.trans (hFull.trans hRight.symm))

/-- The standard enriched tensor uses the same entire native Hom map. -/
theorem copowerUnderlyingMonoidalData_tensorMap (i i' j j' : I) :
    (copowerUnderlyingMonoidalData.{u, v, w} I).tensorMap
        ((copowerRestriction.{u, v, w} I).obj i)
        ((copowerRestriction.{u, v, w} I).obj i')
        ((copowerRestriction.{u, v, w} I).obj j)
        ((copowerRestriction.{u, v, w} I).obj j') =
      copowerTensorHom.{u, v, w} I i i' j j' := rfl

end OriginalMonoidal

end PointedCGWH
