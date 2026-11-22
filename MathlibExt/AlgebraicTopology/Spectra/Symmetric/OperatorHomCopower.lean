/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
public import MathlibExt.CategoryTheory.Operad.FinBijBlockSubgroup
public import MathlibExt.CategoryTheory.Action.FreeActionCopower
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition

/-!
# Actual native symmetric operator Hom coends and finite sphere copowers

The full original coefficient-first weighted coend is compared, through its
actual labelled sphere generators and balancing maps, to the coefficient
colimit of finite block decompositions. Its entire inverse is the actual
original coend generator cocone. A free first-block action then gives the
finite orbit copower of the original residual sphere power.

The sphere action is retained on every coefficient; no trivial action or
CW/cofibrancy premise is supplied. The original orthogonal topology remains
a separate obligation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v uI
open CategoryTheory Limits MonoidalCategory BraidedCategory Opposite
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH PointedCGWH.SymmetricModulePresentation
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped MonoidalClosed

namespace PointedCGWH.SymmetricOperatorHom

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual whole original sphere coefficient functor. -/
abbrev sphere : I ⥤ PointedCGWH.{u, v} := PointedCGWH.sphereSequence.{u, v}.functor

private instance nativeSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

private theorem copowerConditionOfPointRelations
    {T : Type uI} [Category.{0} T]
    (W : EnrichedFunctor PointedCGWH.{u, v} (CopowerUnderlying.{u, v, 0} T)ᵒᵖ
      PointedCGWH.{u, v})
    (F : EnrichedFunctor PointedCGWH.{u, v} (CopowerUnderlying.{u, v, 0} T)
      PointedCGWH.{u, v})
    {Z : PointedCGWH.{u, v}}
    (legs : ∀ a, W.obj (Opposite.op a) ⊗ F.obj a ⟶ Z)
    (h : ∀ (a b : CopowerUnderlying.{u, v, 0} T)
      (r : (show T from a) ⟶ (show T from b)),
      let e : (𝟙_ PointedCGWH.{u, v}) ⟶ (a ⟶[PointedCGWH.{u, v}] b) :=
        basedDiscreteIncl.{u, v, 0} ((show T from a) ⟶ (show T from b)) r
      (((ρ_ (W.obj (Opposite.op b))).inv ≫
          W.obj (Opposite.op b) ◁ e ≫
          MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a))) ⊗ₘ
            𝟙 (F.obj a)) ≫ legs a =
        (W.obj (Opposite.op b) ◁
          ((ρ_ (F.obj a)).inv ≫ F.obj a ◁ e ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ legs b) :
    ∀ a b,
      ((α_ (W.obj (Opposite.op b)) (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ
            𝟙 (F.obj a))) ≫ legs a =
        (W.obj (Opposite.op b) ◁
          ((β_ (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ legs b := by
  intro a b
  let E : Type := (show T from a) ⟶ (show T from b)
  let U : PointedCGWH.{u, v} := W.obj (Opposite.op b)
  let U' : PointedCGWH.{u, v} := W.obj (Opposite.op a)
  let H : PointedCGWH.{u, v} := a ⟶[PointedCGWH.{u, v}] b
  let X : PointedCGWH.{u, v} := F.obj a
  let Y : PointedCGWH.{u, v} := F.obj b
  let p : U ⊗ H ⟶ U' :=
    MonoidalClosed.uncurry (W.map (Opposite.op b) (Opposite.op a))
  let q : X ⊗ H ⟶ Y := MonoidalClosed.uncurry (F.map a b)
  let wf : U ⊗ (H ⊗ X) ⟶ U' ⊗ X := (α_ U H X).inv ≫ (p ⊗ₘ 𝟙 X)
  let df : U ⊗ (H ⊗ X) ⟶ U ⊗ Y := U ◁ ((β_ H X).hom ≫ q)
  have hGenerator (r : E) :
      (U ◁ discreteSmashIncl.{u, v, 0} E X r) ≫ (wf ≫ legs a) =
        (U ◁ discreteSmashIncl.{u, v, 0} E X r) ≫ (df ≫ legs b) := by
    let e : (𝟙_ PointedCGWH.{u, v}) ⟶ H := basedDiscreteIncl.{u, v, 0} E r
    let pre : U ⊗ X ⟶ U ⊗ (H ⊗ X) :=
      U ◁ ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X))
    let wa : U ⟶ U' := (ρ_ U).inv ≫ U ◁ e ≫ p
    let fa : X ⟶ Y := (ρ_ X).inv ≫ X ◁ e ≫ q
    have hNatural :
        U ◁ (e ⊗ₘ 𝟙 X) ≫ (α_ U H X).inv =
          (α_ U (𝟙_ PointedCGWH.{u, v}) X).inv ≫ ((U ◁ e) ▷ X) := by
      simpa only [id_tensorHom, tensorHom_id] using
        associator_inv_naturality (𝟙 U) e (𝟙 X)
    have hTriangle :
        U ◁ (λ_ X).inv ≫ (α_ U (𝟙_ PointedCGWH.{u, v}) X).inv =
          (ρ_ U).inv ▷ X := by
      monoidal
    have hLeft : pre ≫ wf = wa ⊗ₘ 𝟙 X := by
      calc
        pre ≫ wf = U ◁ (λ_ X).inv ≫
            (U ◁ (e ⊗ₘ 𝟙 X) ≫ (α_ U H X).inv) ≫ (p ⊗ₘ 𝟙 X) := by
          simp only [pre, wf, whiskerLeft_comp, Category.assoc]
        _ = U ◁ (λ_ X).inv ≫ (α_ U (𝟙_ PointedCGWH.{u, v}) X).inv ≫
            ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X) := by
          simpa only [Category.assoc] using congrArg
            (fun t : U ⊗ ((𝟙_ PointedCGWH.{u, v}) ⊗ X) ⟶ (U ⊗ H) ⊗ X =>
              U ◁ (λ_ X).inv ≫ t ≫ (p ⊗ₘ 𝟙 X)) hNatural
        _ = ((ρ_ U).inv ▷ X) ≫ ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X) := by
          simpa only [Category.assoc] using congrArg
            (fun t : U ⊗ X ⟶ (U ⊗ (𝟙_ PointedCGWH.{u, v})) ⊗ X =>
              t ≫ ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X)) hTriangle
        _ = wa ⊗ₘ 𝟙 X := by
          simpa only [wa, comp_whiskerRight, Category.assoc] using
            whiskerRight_comp_tensorHom ((ρ_ U).inv ≫ U ◁ e) p (𝟙 X)
    have hUnitCross :
        ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) ≫ (β_ H X).hom =
          (ρ_ X).inv ≫ X ◁ e := by
      simpa only [id_tensorHom, Category.assoc,
        CategoryTheory.braiding_tensorUnit_left, Iso.inv_hom_id_assoc] using
        congrArg
          (fun t : (𝟙_ PointedCGWH.{u, v}) ⊗ X ⟶ X ⊗ H => (λ_ X).inv ≫ t)
          (BraidedCategory.braiding_naturality e (𝟙 X))
    have hRight : pre ≫ df = U ◁ fa := by
      calc
        pre ≫ df = U ◁ (((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) ≫ (β_ H X).hom ≫ q) := by
          simp only [pre, df, whiskerLeft_comp, Category.assoc]
        _ = U ◁ (((ρ_ X).inv ≫ X ◁ e) ≫ q) :=
          (congrArg (fun t : X ⟶ Y => U ◁ t)
            (Category.assoc ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) (β_ H X).hom q).symm).trans
              (congrArg (fun t : X ⟶ X ⊗ H => U ◁ (t ≫ q)) hUnitCross)
        _ = U ◁ fa := by simp only [fa, Category.assoc]
    have hPoint : (wa ⊗ₘ 𝟙 X) ≫ legs a = (U ◁ fa) ≫ legs b := h a b r
    have hL : pre ≫ (wf ≫ legs a) = (wa ⊗ₘ 𝟙 X) ≫ legs a :=
      (Category.assoc pre wf (legs a)).symm.trans
        (congrArg (fun t : U ⊗ X ⟶ U' ⊗ X => t ≫ legs a) hLeft)
    have hR : pre ≫ (df ≫ legs b) = (U ◁ fa) ≫ legs b :=
      (Category.assoc pre df (legs b)).symm.trans
        (congrArg (fun t : U ⊗ X ⟶ U ⊗ Y => t ≫ legs b) hRight)
    change pre ≫ (wf ≫ legs a) = pre ≫ (df ≫ legs b)
    exact hL.trans (hPoint.trans hR.symm)
  let G : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := tensorLeft U
  have hColimit :
      CategoryTheory.Limits.IsColimit
        (G.mapCocone (discreteSmashCofan.{u, v, 0} E X)) :=
    CategoryTheory.Limits.isColimitOfPreserves G
      (discreteSmashCofanIsColimit.{u, v, 0} E X)
  change wf ≫ legs a = df ≫ legs b
  apply hColimit.hom_ext
  intro r
  change (U ◁ discreteSmashIncl.{u, v, 0} E X r.as) ≫ (wf ≫ legs a) =
    (U ◁ discreteSmashIncl.{u, v, 0} E X r.as) ≫ (df ≫ legs b)
  exact hGenerator r.as


section NativePointMaps

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal

private theorem restrictionPrecomposition (a b k : I) (r : a ⟶ b) :
    eHomWhiskerRight PointedCGWH.{u, v}
        ((copowerRestriction.{u, v, 0} I).map r)
        ((copowerRestriction.{u, v, 0} I).obj k) =
      basedDiscreteFunctor.{u, v, 0}.map (↾fun f : b ⟶ k => r ≫ f) := by
  let V := PointedCGWH.{u, v}
  let C := CopowerUnderlying.{u, v, 0} I
  let R := copowerRestriction.{u, v, 0} I
  let E : Type := b ⟶ k
  let H : V := basedDiscreteObj.{u, v, 0} E
  let H' : V := basedDiscreteObj.{u, v, 0} (a ⟶ k)
  let t : H ⟶ H' := eHomWhiskerRight V (R.map r) (R.obj k)
  let p : H ⟶ H' := basedDiscreteFunctor.{u, v, 0}.map (↾fun f : E => r ≫ f)
  change t = p
  apply (basedDiscreteCofanIsColimit.{u, v, 0} E).hom_ext
  intro f
  let g : b ⟶ k := f.as
  let i : 𝟙_ V ⟶ H := basedDiscreteIncl.{u, v, 0} E g
  let i' : 𝟙_ V ⟶ H' := basedDiscreteIncl.{u, v, 0} (a ⟶ k) (r ≫ g)
  have hG : eHomEquiv V (R.map g) = i := copowerRestriction_map.{u, v, 0} I g
  have hRG : eHomEquiv V (R.map (r ≫ g)) = i' :=
    copowerRestriction_map.{u, v, 0} I (r ≫ g)
  have hCompose : eHomEquiv V (R.map r ≫ R.map g) = i' :=
    (congrArg (fun q : R.obj a ⟶ R.obj k => eHomEquiv V q)
      (R.map_comp r g).symm).trans hRG
  have hWhisker : eHomEquiv V (R.map g) ≫ t =
      eHomEquiv V (R.map r ≫ R.map g) :=
    eHomEquiv_comp_eHomWhiskerRight (V := V) (C := C) (R.map r) (R.map g)
  have hL : i ≫ t = i' :=
    (congrArg (fun q : (𝟙_ V) ⟶ H => q ≫ t) hG.symm).trans
      (hWhisker.trans hCompose)
  have hR : i ≫ p = i' :=
    basedDiscreteIncl_naturality.{u, v, 0} (fun f : E => r ≫ f) g
  change i ≫ t = i ≫ p
  exact hL.trans hR.symm

private theorem spherePointMap {a b : I} (r : a ⟶ b) :
    (ρ_ (sphereSequence.{u, v}.functor.obj a)).inv ≫
        sphereSequence.{u, v}.functor.obj a ◁ basedDiscreteIncl.{u, v, 0} (a ⟶ b) r ≫
        MonoidalClosed.uncurry
          (sphereCopowerEnrichedFunctor.{u, v}.map
            ((copowerRestriction.{u, v, 0} I).obj a)
            ((copowerRestriction.{u, v, 0} I).obj b)) =
      sphereSequence.{u, v}.functor.map r := by
  let V := PointedCGWH.{u, v}
  let A : V := sphereSequence.{u, v}.functor.obj a
  let B : V := sphereSequence.{u, v}.functor.obj b
  let H : V := basedDiscreteObj.{u, v, 0} (a ⟶ b)
  let e : (𝟙_ V) ⟶ H := basedDiscreteIncl.{u, v, 0} (a ⟶ b) r
  let p : H ⟶ (ihom A).obj B :=
    sphereCopowerEnrichedFunctor.{u, v}.map
      ((copowerRestriction.{u, v, 0} I).obj a)
      ((copowerRestriction.{u, v, 0} I).obj b)
  let q : A ⟶ B := sphereSequence.{u, v}.functor.map r
  have hGen : e ≫ p = eHomEquiv V q :=
    originalDiagramHomMap_generator.{u, v, 0} sphereSequence.{u, v}.functor r
  have hInverse :
      MonoidalClosed.uncurry' (eHomEquiv V q) = q :=
    (MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm V
      (eHomEquiv V q)).symm.trans ((eHomEquiv V).symm_apply_apply q)
  have h : MonoidalClosed.uncurry' (e ≫ p) = q :=
    (congrArg
      (fun t : (𝟙_ V) ⟶ (ihom A).obj B => MonoidalClosed.uncurry' t) hGen).trans
        hInverse
  dsimp only [MonoidalClosed.uncurry'] at h
  rw [MonoidalClosed.uncurry_natural_left] at h
  change (ρ_ A).inv ≫ A ◁ e ≫ MonoidalClosed.uncurry p = q
  simpa only [Category.assoc] using h

private theorem weightPointMap (n k a b : I) (r : a ⟶ b) :
    let W := Enriched.SphereOperator.weight
      (copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((copowerRestriction.{u, v, 0} I).obj n)
      ((copowerRestriction.{u, v, 0} I).obj k)
    (ρ_ (W.obj (Opposite.op ((copowerRestriction.{u, v, 0} I).obj b)))).inv ≫
        W.obj (Opposite.op ((copowerRestriction.{u, v, 0} I).obj b)) ◁
          basedDiscreteIncl.{u, v, 0} (a ⟶ b) r ≫
        MonoidalClosed.uncurry
          (W.map (Opposite.op ((copowerRestriction.{u, v, 0} I).obj b))
            (Opposite.op ((copowerRestriction.{u, v, 0} I).obj a))) =
      basedDiscreteFunctor.{u, v, 0}.map
        (↾fun f : (b ⊗ n) ⟶ k => (r ⊗ₘ 𝟙 n) ≫ f) := by
  let V := PointedCGWH.{u, v}
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  let W := Enriched.SphereOperator.weight d (R.obj n) (R.obj k)
  have hPoint : eHomEquiv V (R.map r) =
      basedDiscreteIncl.{u, v, 0} (a ⟶ b) r := copowerRestriction_map.{u, v, 0} I r
  have hTensor : R.map r ⊗ₘ 𝟙 (R.obj n) = R.map (r ⊗ₘ 𝟙 n) :=
    (congrArg (fun q : R.obj n ⟶ R.obj n => R.map r ⊗ₘ q) (R.map_id n).symm).trans
      (copowerUnderlyingMonoidal_tensor_original.{u, v, 0} I r (𝟙 n))
  have h := Enriched.SphereOperator.weight_point_pre d (R.obj n) (R.obj k)
    (R.obj a) (R.obj b) (R.map r)
  rw [hPoint] at h
  have hWhisker :
      eHomWhiskerRight V (R.map r ⊗ₘ 𝟙 (R.obj n)) (R.obj k) =
        eHomWhiskerRight V (R.map (r ⊗ₘ 𝟙 n)) (R.obj k) :=
    congrArg
      (fun q : R.obj (a ⊗ n) ⟶ R.obj (b ⊗ n) => eHomWhiskerRight V q (R.obj k))
      hTensor
  exact h.trans (hWhisker.trans (restrictionPrecomposition (a ⊗ n) (b ⊗ n)
    k (r ⊗ₘ 𝟙 n)))

end NativePointMaps



/-- The entire actual original native operator Hom object. -/
abbrev nativeHom (n k : I) : PointedCGWH.{u, v} :=
  PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} k

/-- The original coefficient-first coend weight. -/
abbrev nativeWeight (n k : I) :=
  Enriched.SphereOperator.weight
    (copowerUnderlyingMonoidalData.{u, v, 0} I)
    ((copowerRestriction.{u, v, 0} I).obj n)
    ((copowerRestriction.{u, v, 0} I).obj k)

/-- The actual sphere coefficient diagram on all block decompositions. -/
def blockDiagram (n k : I) : BlockDecomposition n k ⥤ PointedCGWH.{u, v} :=
  CostructuredArrow.proj (tensorRight n) k ⋙ sphere.{u, v}

/-- All original block labels enter the same original native coend Hom. -/
def nativeBlockCocone (n k : I) : Cocone (blockDiagram n k) where
  pt := nativeHom n k
  ι :=
    { app := fun d => operatorGenerator d.left n k d.hom
      naturality := by
        intro d e g
        change sphere.{u, v}.map g.left ≫ operatorGenerator e.left n k e.hom =
          operatorGenerator d.left n k d.hom ≫ 𝟙 (nativeHom n k)
        have h := operatorGenerator_coefficient g.left n k e.hom
        have hw : (g.left ⊗ₘ 𝟙 n) ≫ e.hom = d.hom := by
          have hRight : (g.left ▷ n) ≫ e.hom = d.hom := CostructuredArrow.w g
          exact (congrArg (fun q => q ≫ e.hom) (tensorHom_id g.left n)).trans hRight
        exact (h.trans (congrArg (operatorGenerator d.left n k) hw)).trans
          (Category.comp_id (operatorGenerator d.left n k d.hom)).symm }

/-- The full inverse comparison descends the original generator cocone. -/
def blockToNative (n k : I) :
    colimit (blockDiagram n k) ⟶ nativeHom n k :=
  colimit.desc (blockDiagram n k) (nativeBlockCocone n k)

/-- The entire inverse retains every original block generator. -/
theorem blockToNative_generator_function :
    (fun (n k : I) (d : BlockDecomposition n k) =>
      colimit.ι (blockDiagram n k) d ≫ blockToNative n k) =
      fun (n k : I) (d : BlockDecomposition n k) =>
        operatorGenerator d.left n k d.hom := by
  funext n k d
  exact colimit.ι_desc (nativeBlockCocone n k) d

/-- The actual full discrete coefficient leg targets the original block colimit. -/
def blockLeg (n k a : I) :
    basedDiscreteObj.{u, v, 0} ((a ⊗ n) ⟶ k) ⊗ sphere.{u, v}.obj a ⟶
      colimit (blockDiagram n k) :=
  discreteSmashDesc.{u, v, 0} ((a ⊗ n) ⟶ k) (sphere.{u, v}.obj a)
    (fun f => colimit.ι (blockDiagram n k) (CostructuredArrow.mk f))

/-- Every full coefficient leg has its original block-label characteristic. -/
theorem blockLeg_generator (n k a : I) (f : (a ⊗ n) ⟶ k) :
    discreteSmashIncl.{u, v, 0} ((a ⊗ n) ⟶ k) (sphere.{u, v}.obj a) f ≫ blockLeg n k a =
      colimit.ι (blockDiagram n k) (CostructuredArrow.mk f) :=
  discreteSmashDesc_generator.{u, v, 0} ((a ⊗ n) ⟶ k) (sphere.{u, v}.obj a)
    (fun g => colimit.ι (blockDiagram n k) (CostructuredArrow.mk g)) f

private theorem discreteSmashIncl_index
    {E E' : Type} (h : E → E') (A : PointedCGWH.{u, v}) (e : E) :
    discreteSmashIncl.{u, v, 0} E A e ≫
        (basedDiscreteFunctor.{u, v, 0}.map (↾h) ▷ A) =
      discreteSmashIncl.{u, v, 0} E' A (h e) := by
  let U : PointedCGWH.{u, v} := 𝟙_ PointedCGWH.{u, v}
  let D : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} E
  let D' : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} E'
  let i : U ⟶ D := basedDiscreteIncl.{u, v, 0} E e
  let i' : U ⟶ D' := basedDiscreteIncl.{u, v, 0} E' (h e)
  let p : D ⟶ D' := basedDiscreteFunctor.{u, v, 0}.map (↾h)
  have hi : i ≫ p = i' := basedDiscreteIncl_naturality.{u, v, 0} h e
  have hp : p ⊗ₘ 𝟙 A = p ▷ A := MonoidalCategory.tensorHom_id p A
  have hTensor : (i ⊗ₘ 𝟙 A) ≫ (p ▷ A) = i' ⊗ₘ 𝟙 A :=
    (congrArg
      (fun t : D ⊗ A ⟶ D' ⊗ A => (i ⊗ₘ 𝟙 A) ≫ t) hp.symm).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom i (𝟙 A) p (𝟙 A)).trans
        (congrArg₂ (fun s t => s ⊗ₘ t) hi (Category.comp_id (𝟙 A))))
  change (λ_ A).inv ≫ (i ⊗ₘ 𝟙 A) ≫ (p ▷ A) =
    (λ_ A).inv ≫ (i' ⊗ₘ 𝟙 A)
  exact (Category.assoc (λ_ A).inv (i ⊗ₘ 𝟙 A) (p ▷ A)).trans
    (congrArg (fun t : U ⊗ A ⟶ D' ⊗ A => (λ_ A).inv ≫ t) hTensor)

private theorem discreteSmashIncl_coefficient
    (E : Type) {A B : PointedCGWH.{u, v}} (p : A ⟶ B) (e : E) :
    discreteSmashIncl.{u, v, 0} E A e ≫ (basedDiscreteObj.{u, v, 0} E ◁ p) =
      p ≫ discreteSmashIncl.{u, v, 0} E B e := by
  let U : PointedCGWH.{u, v} := 𝟙_ PointedCGWH.{u, v}
  let D : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} E
  let i : U ⟶ D := basedDiscreteIncl.{u, v, 0} E e
  have hp : 𝟙 D ⊗ₘ p = D ◁ p := MonoidalCategory.id_tensorHom D p
  have hTensor : (i ⊗ₘ 𝟙 A) ≫ (D ◁ p) = i ⊗ₘ p :=
    (congrArg
      (fun t : D ⊗ A ⟶ D ⊗ B => (i ⊗ₘ 𝟙 A) ≫ t) hp.symm).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom i (𝟙 A) (𝟙 D) p).trans
        (congrArg₂ (fun s t => s ⊗ₘ t) (Category.comp_id i) (Category.id_comp p)))
  change (λ_ A).inv ≫ (i ⊗ₘ 𝟙 A) ≫ (D ◁ p) =
    p ≫ (λ_ B).inv ≫ (i ⊗ₘ 𝟙 B)
  have hUnitor : (λ_ A).inv ≫ (i ⊗ₘ p) =
      p ≫ (λ_ B).inv ≫ (i ⊗ₘ 𝟙 B) := by
    simpa only [MonoidalCategory.tensorHom_id] using leftUnitor_inv_comp_tensorHom i p
  exact (Category.assoc (λ_ A).inv (i ⊗ₘ 𝟙 A) (D ◁ p)).trans
    ((congrArg (fun t : U ⊗ A ⟶ D ⊗ B => (λ_ A).inv ≫ t) hTensor).trans hUnitor)


/-- The whole original coefficient relation is derived from the actual block-colimit square. -/
theorem blockLeg_coefficient {a b : I} (r : a ⟶ b) (n k : I) :
    (basedDiscreteFunctor.{u, v, 0}.map
      (↾fun f : (b ⊗ n) ⟶ k => (r ⊗ₘ 𝟙 n) ≫ f) ▷ sphere.{u, v}.obj a) ≫ blockLeg n k a =
      (basedDiscreteObj.{u, v, 0} ((b ⊗ n) ⟶ k) ◁ sphere.{u, v}.map r) ≫ blockLeg n k b := by
  let A : PointedCGWH.{u, v} := sphere.{u, v}.obj a
  let B : PointedCGWH.{u, v} := sphere.{u, v}.obj b
  let E : Type := (b ⊗ n) ⟶ k
  let E' : Type := (a ⊗ n) ⟶ k
  let fIndex : E → E' := fun f => (r ⊗ₘ 𝟙 n) ≫ f
  let p : basedDiscreteObj.{u, v, 0} E ⟶ basedDiscreteObj.{u, v, 0} E' :=
    basedDiscreteFunctor.{u, v, 0}.map (↾fIndex)
  let q : A ⟶ B := sphere.{u, v}.map r
  let Z : PointedCGWH.{u, v} := colimit (blockDiagram n k)
  let g : discreteSmashObj.{u, v, 0} E' A ⟶ Z := blockLeg n k a
  let g' : discreteSmashObj.{u, v, 0} E B ⟶ Z := blockLeg n k b
  change (p ▷ A) ≫ g = (basedDiscreteObj.{u, v, 0} E ◁ q) ≫ g'
  apply discreteSmash_hom_ext.{u, v, 0} E A
  intro f
  let j : A ⟶ discreteSmashObj.{u, v, 0} E A :=
    discreteSmashIncl.{u, v, 0} E A f
  let j' : A ⟶ discreteSmashObj.{u, v, 0} E' A :=
    discreteSmashIncl.{u, v, 0} E' A (fIndex f)
  let jB : B ⟶ discreteSmashObj.{u, v, 0} E B :=
    discreteSmashIncl.{u, v, 0} E B f
  have hPre : j ≫ (p ▷ A) = j' := discreteSmashIncl_index fIndex A f
  have hCoefficient : j ≫ (basedDiscreteObj.{u, v, 0} E ◁ q) = q ≫ jB :=
    discreteSmashIncl_coefficient E q f
  have hFac : j' ≫ g =
      colimit.ι (blockDiagram n k) (CostructuredArrow.mk (fIndex f)) :=
    blockLeg_generator n k a (fIndex f)
  have hFac' : jB ≫ g' =
      colimit.ι (blockDiagram n k) (CostructuredArrow.mk f) :=
    blockLeg_generator n k b f
  let d : BlockDecomposition n k := CostructuredArrow.mk (fIndex f)
  let e : BlockDecomposition n k := CostructuredArrow.mk f
  let arrow : d ⟶ e := CostructuredArrow.homMk r (by
    change (r ▷ n) ≫ f = (r ⊗ₘ 𝟙 n) ≫ f
    exact congrArg (fun z => z ≫ f) (tensorHom_id r n).symm)
  have hw := colimit.w (blockDiagram n k) arrow
  change q ≫ colimit.ι (blockDiagram n k) e =
    colimit.ι (blockDiagram n k) d at hw
  have hL : j ≫ ((p ▷ A) ≫ g) = colimit.ι (blockDiagram n k) d :=
    (Category.assoc j (p ▷ A) g).symm.trans
      ((congrArg (fun t : A ⟶ discreteSmashObj.{u, v, 0} E' A => t ≫ g) hPre).trans hFac)
  have hR : j ≫ ((basedDiscreteObj.{u, v, 0} E ◁ q) ≫ g') =
      colimit.ι (blockDiagram n k) d :=
    (Category.assoc j (basedDiscreteObj.{u, v, 0} E ◁ q) g').symm.trans
      ((congrArg (fun t : A ⟶ discreteSmashObj.{u, v, 0} E B => t ≫ g') hCoefficient).trans
        ((Category.assoc q jB g').trans
          ((congrArg (fun t : B ⟶ Z => q ≫ t) hFac').trans hw)))
  exact hL.trans hR.symm


/-- Full enriched balancing keeps the original entire Hom objects and sphere action. -/
theorem blockLeg_balanced (n k : I) :
    let W := nativeWeight n k
    let F := sphereCopowerEnrichedFunctor.{u, v}
    ∀ a b : CopowerUnderlying.{u, v, 0} I,
      ((α_ (W.obj (op b)) (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))) ≫
          blockLeg n k (show I from a) =
        (W.obj (op b) ◁
          ((β_ (a ⟶[PointedCGWH.{u, v}] b) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a b))) ≫
          blockLeg n k (show I from b) := by
  let W := nativeWeight n k
  let F := sphereCopowerEnrichedFunctor.{u, v}
  apply copowerConditionOfPointRelations W F (fun a => blockLeg n k (show I from a))
  intro a b r
  let a₀ : I := a
  let b₀ : I := b
  let A : PointedCGWH.{u, v} := sphere.{u, v}.obj a₀
  let B : PointedCGWH.{u, v} := sphere.{u, v}.obj b₀
  let p : W.obj (op b) ⟶ W.obj (op a) :=
    basedDiscreteFunctor.{u, v, 0}.map
      (↾fun f : (b₀ ⊗ n) ⟶ k => (r ⊗ₘ 𝟙 n) ≫ f)
  have hW :
      (ρ_ (W.obj (op b))).inv ≫ W.obj (op b) ◁
        basedDiscreteIncl.{u, v, 0} (a₀ ⟶ b₀) r ≫
          MonoidalClosed.uncurry (W.map (op b) (op a)) = p :=
    weightPointMap n k a₀ b₀ r
  have hS :
      (ρ_ A).inv ≫ A ◁ basedDiscreteIncl.{u, v, 0} (a₀ ⟶ b₀) r ≫
        MonoidalClosed.uncurry (F.map a b) = sphere.{u, v}.map r :=
    spherePointMap r
  have hLeft := congrArg
    (fun z : W.obj (op b) ⟶ W.obj (op a) =>
      (z ⊗ₘ 𝟙 A) ≫ blockLeg n k a₀) hW
  have hRight := congrArg
    (fun z : A ⟶ B => (W.obj (op b) ◁ z) ≫ blockLeg n k b₀) hS
  have hCanonicalBase : (p ▷ A) ≫ blockLeg n k a₀ =
      (W.obj (op b) ◁ sphere.{u, v}.map r) ≫ blockLeg n k b₀ :=
    blockLeg_coefficient r n k
  have hCanonical : (p ⊗ₘ 𝟙 A) ≫ blockLeg n k a₀ =
      (W.obj (op b) ◁ sphere.{u, v}.map r) ≫ blockLeg n k b₀ :=
    (congrArg (fun z : W.obj (op b) ⊗ A ⟶ W.obj (op a) ⊗ A =>
      z ≫ blockLeg n k a₀) (tensorHom_id p A)).trans hCanonicalBase
  exact hLeft.trans (hCanonical.trans hRight.symm)


/-- The entire forward is the original weighted-coend descent on all full coefficient legs. -/
def nativeToBlock (n k : I) : nativeHom n k ⟶ colimit (blockDiagram n k) :=
  Enriched.weightedCoend.desc (nativeWeight n k) sphereCopowerEnrichedFunctor.{u, v}
    (fun a => blockLeg n k (show I from a)) (blockLeg_balanced n k)

/-- The actual forward retains the full original coend inclusion, before any point input. -/
theorem nativeToBlock_coend_generator_function :
    (fun (n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
      Enriched.weightedCoend.ι (nativeWeight n k) sphereCopowerEnrichedFunctor.{u, v} a ≫
        nativeToBlock n k) =
      fun (n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
        blockLeg n k (show I from a) := by
  funext n k a
  exact Enriched.weightedCoend.ι_desc (nativeWeight n k) sphereCopowerEnrichedFunctor.{u, v}
    (fun a => blockLeg n k (show I from a)) (blockLeg_balanced n k) a

/-- The actual original sphere generator is sent to its complete original block-colimit leg. -/
theorem nativeToBlock_generator (n k a : I) (f : (a ⊗ n) ⟶ k) :
    operatorGenerator.{u, v} a n k f ≫ nativeToBlock.{u, v} n k =
      colimit.ι (blockDiagram.{u, v} n k) (CostructuredArrow.mk f) := by
  let R := copowerRestriction.{u, v, 0} I
  let W := nativeWeight n k
  let F := sphereCopowerEnrichedFunctor.{u, v}
  let A : PointedCGWH.{u, v} := sphere.{u, v}.obj a
  let P : PointedCGWH.{u, v} := Enriched.weightedCoend.objects W F (R.obj a)
  let Z : PointedCGWH.{u, v} := colimit (blockDiagram n k)
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} ((a ⊗ n) ⟶ k) A f
  let i : P ⟶ nativeHom n k := Enriched.weightedCoend.ι W F (R.obj a)
  let t : nativeHom n k ⟶ Z := nativeToBlock n k
  have hCoend : i ≫ t = blockLeg n k a :=
    congrArg (fun Φ => Φ n k (R.obj a)) nativeToBlock_coend_generator_function
  have hBlock : j ≫ blockLeg n k a =
      colimit.ι (blockDiagram n k) (CostructuredArrow.mk f) :=
    blockLeg_generator n k a f
  change (j ≫ i) ≫ t = _
  exact (Category.assoc j i t).trans
    ((congrArg (fun q : P ⟶ Z => j ≫ q) hCoend).trans hBlock)


/-- Both full native coend comparison functions are inverse on the actual whole objects. -/
def nativeToBlockIso (n k : I) : nativeHom n k ≅ colimit (blockDiagram n k) where
  hom := nativeToBlock n k
  inv := blockToNative n k
  hom_inv_id := by
    apply Enriched.weightedCoend.hom_ext
    intro a
    let a₀ : I := a
    apply discreteSmash_hom_ext.{u, v, 0} ((a₀ ⊗ n) ⟶ k) (sphere.{u, v}.obj a₀)
    intro f
    change (operatorGenerator a₀ n k f ≫ nativeToBlock n k) ≫ blockToNative n k =
      operatorGenerator a₀ n k f
    rw [nativeToBlock_generator]
    exact colimit.ι_desc (nativeBlockCocone n k) (CostructuredArrow.mk f)
  inv_hom_id := by
    apply colimit.hom_ext
    intro d
    have hBack := congrArg (fun Φ => Φ n k d) blockToNative_generator_function
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ nativeToBlock n k) hBack).trans
        ((nativeToBlock_generator n k d.left d.hom).trans (Category.comp_id _).symm))

/-- The whole actual forward is the fixed full original weighted-coend descent. -/
theorem nativeToBlockIso_forward_function :
    (fun (n k : I) => (nativeToBlockIso n k).hom) = nativeToBlock := rfl

/-- The whole actual inverse is the full original sphere-generator colimit descent. -/
theorem nativeToBlockIso_inverse_function :
    (fun (n k : I) => (nativeToBlockIso n k).inv) = blockToNative := rfl

/-- The actual full sphere action of each complement automorphism. -/
def sphereBlockAction (R : I) : Aut R →* End (sphere.{u, v}.obj R) :=
  (Functor.mapEnd R sphere.{u, v}).comp (Aut.toEnd (X := R))

/-- The complete action VALUE retains the original sphere functor arrow. -/
theorem sphereBlockAction_function (R : I) :
    (fun a : Aut R => End.asHom (sphereBlockAction R a)) =
      fun a : Aut R => sphere.{u, v}.map a.asIso.hom := rfl

/-- The actual action diagram retains every original first-block automorphism and sphere map. -/
def normalizedDiagram (n m : ℕ) :
    letI := blockMulAction (card (m - n)) (card n) (card m)
    ActionCategory (Aut (card (m - n)))
      (card (m - n) ⊗ card n ≅ card m) ⥤ PointedCGWH.{u, v} := by
  letI := blockMulAction (card (m - n)) (card n) (card m)
  exact ActionCategory.coefficientDiagram (Aut (card (m - n)))
    (card (m - n) ⊗ card n ≅ card m)
    (sphere.{u, v}.obj (card (m - n))) (sphereBlockAction (card (m - n)))

/-- The exact original normalized forward cocone, preserving all actual sphere arrows. -/
def normalizedForwardCocone {n m : ℕ} (h : n ≤ m) :
    Cocone (blockDiagram.{u, v} (card n) (card m)) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let H := Aut R
  let E := R ⊗ N ≅ M
  let F := tensorRight N
  letI := blockMulAction R N M
  let J : ActionCategory H E ⥤ PointedCGWH.{u, v} := normalizedDiagram n m
  let k (d : BlockDecomposition N M) := cardComplementIso h d
  let norm (d : BlockDecomposition N M) := cardNormalizedBlock h d
  let a {d e : BlockDecomposition N M} (q : d ⟶ e) : H :=
    Aut.of (k d ≪≫ asIso q.left ≪≫ (k e).symm)
  have qInv {d e : BlockDecomposition N M} (q : d ⟶ e) :
      F.mapIso (asIso q.left).symm ≪≫ asIso d.hom = asIso e.hom := by
    apply Iso.ext
    change F.map (inv q.left) ≫ d.hom = e.hom
    rw [← CostructuredArrow.w q, ← Category.assoc, ← F.map_comp,
      IsIso.inv_hom_id, F.map_id, Category.id_comp]
  have ha {d e : BlockDecomposition N M} (q : d ⟶ e) :
      a q • norm d = norm e := by
    change F.mapIso (a q).asIso.symm ≪≫ norm d = norm e
    calc
      _ = F.mapIso (k e) ≪≫ (F.mapIso (asIso q.left).symm ≪≫ asIso d.hom) := by
        have hn : norm d = F.mapIso (k d) ≪≫ asIso d.hom := rfl
        rw [hn]
        dsimp only [a]
        simp only [Iso.trans_symm, Functor.mapIso_trans, Iso.trans_assoc,
          Functor.mapIso_symm, Iso.symm_self_id_assoc, Iso.symm_symm_eq]
      _ = F.mapIso (k e) ≪≫ asIso e.hom :=
        congrArg (fun z => F.mapIso (k e) ≪≫ z) (qInv q)
      _ = norm e := rfl
  have hcoeff {d e : BlockDecomposition N M} (q : d ⟶ e) :
      q.left ≫ (k e).inv = (k d).inv ≫ (a q).asIso.hom := by
    dsimp only [a]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc, asIso_hom]
  exact
    { pt := colimit J
      ι :=
        { app := fun d => sphere.{u, v}.map (k d).inv ≫ colimit.ι J (norm d : ActionCategory H E)
          naturality := by
            intro d e q
            have hc : sphere.{u, v}.map q.left ≫ sphere.{u, v}.map (k e).inv =
                sphere.{u, v}.map (k d).inv ≫ sphere.{u, v}.map (a q).asIso.hom := by
              rw [← sphere.{u, v}.map_comp, ← sphere.{u, v}.map_comp, hcoeff q]
            have hw := colimit.w J
              (show (norm d : ActionCategory H E) ⟶ (norm e : ActionCategory H E) from
                Functor.Elements.homMk (a q) (ha q))
            change sphere.{u, v}.map (a q).asIso.hom ≫ colimit.ι J (norm e : ActionCategory H E) =
              colimit.ι J (norm d : ActionCategory H E) at hw
            change sphere.{u, v}.map q.left ≫
                (sphere.{u, v}.map (k e).inv ≫ colimit.ι J (norm e : ActionCategory H E)) =
              (sphere.{u, v}.map (k d).inv ≫ colimit.ι J (norm d : ActionCategory H E)) ≫
                𝟙 (colimit J)
            exact (Category.assoc _ _ _).symm.trans
              ((congrArg (fun f => f ≫ colimit.ι J (norm e : ActionCategory H E)) hc).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun f => sphere.{u, v}.map (k d).inv ≫ f) hw).trans
                    (Category.comp_id _).symm))) } }

/-- The full inverse normalized cocone keeps every actual fixed-complement block label. -/
def normalizedBackwardCocone (n m : ℕ) :
    Cocone (normalizedDiagram.{u, v} n m) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let H := Aut R
  let E := R ⊗ N ≅ M
  let F := tensorRight N
  letI := blockMulAction R N M
  let J : ActionCategory H E ⥤ PointedCGWH.{u, v} := normalizedDiagram n m
  let D := blockDiagram N M
  have triangle {x y : ActionCategory H E} (f : x ⟶ y) :
      F.map f.hom.asIso.hom ≫ y.back.hom = x.back.hom := by
    have hmap := congrArg Iso.hom f.map_val
    change (F.mapIso (show R ≅ R from f.hom.asIso).symm ≪≫ x.back).hom =
      y.back.hom at hmap
    calc
      F.map f.hom.asIso.hom ≫ y.back.hom =
          F.map f.hom.asIso.hom ≫
            (F.mapIso (show R ≅ R from f.hom.asIso).symm ≪≫ x.back).hom := by
              rw [← hmap]
      _ = x.back.hom := by
        rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ← Category.assoc,
          ← F.map_comp, (show R ≅ R from f.hom.asIso).hom_inv_id,
          F.map_id, Category.id_comp]
  let arrow {x y : ActionCategory H E} (f : x ⟶ y) :
      (CostructuredArrow.mk x.back.hom : BlockDecomposition N M) ⟶
        (CostructuredArrow.mk y.back.hom : BlockDecomposition N M) :=
    CostructuredArrow.homMk f.hom.asIso.hom (triangle f)
  exact
    { pt := colimit D
      ι :=
        { app := fun x => colimit.ι D (CostructuredArrow.mk x.back.hom)
          naturality := by
            intro x y f
            have hw := colimit.w D (arrow f)
            change sphere.{u, v}.map f.hom.asIso.hom ≫ colimit.ι D
              (CostructuredArrow.mk y.back.hom) =
                colimit.ι D (CostructuredArrow.mk x.back.hom) at hw
            exact hw.trans (Category.comp_id _).symm } }

/-- Both complete normalized colimit functions are inverse on all original block coefficients. -/
def normalizedColimitIso {n m : ℕ} (h : n ≤ m) :
    colimit (blockDiagram.{u, v} (card n) (card m)) ≅
      colimit (normalizedDiagram.{u, v} n m) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let H := Aut R
  let E := R ⊗ N ≅ M
  let F := tensorRight N
  letI := blockMulAction R N M
  let J : ActionCategory H E ⥤ PointedCGWH.{u, v} := normalizedDiagram n m
  let D := blockDiagram N M
  let κ (d : BlockDecomposition N M) := cardComplementIso h d
  let norm (d : BlockDecomposition N M) := cardNormalizedBlock h d
  let forward : colimit D ⟶ colimit J :=
    colimit.desc D (normalizedForwardCocone h)
  let backward : colimit J ⟶ colimit D :=
    colimit.desc J (normalizedBackwardCocone n m)
  let normTo (d : BlockDecomposition N M) :
      CostructuredArrow.mk (norm d).hom ⟶ d :=
    CostructuredArrow.homMk (κ d).hom (by rfl)
  let dx (x : ActionCategory H E) : BlockDecomposition N M :=
    CostructuredArrow.mk x.back.hom
  let scalar (x : ActionCategory H E) : H := Aut.of ((κ (dx x)).symm)
  have scalar_action (x : ActionCategory H E) :
      scalar x • x.back = norm (dx x) := by
    apply Iso.ext
    rfl
  let scalarArrow {x : ActionCategory H E} :
      x ⟶ (norm (dx x) : ActionCategory H E) :=
    Functor.Elements.homMk (scalar x) (scalar_action x)
  have forwardLeg (d : BlockDecomposition N M) :
      colimit.ι D d ≫ forward =
        sphere.{u, v}.map (κ d).inv ≫ colimit.ι J (norm d : ActionCategory H E) :=
    colimit.ι_desc (normalizedForwardCocone h) d
  have backwardLeg (x : ActionCategory H E) :
      colimit.ι J x ≫ backward = colimit.ι D (dx x) :=
    colimit.ι_desc (normalizedBackwardCocone n m) x
  refine { hom := forward, inv := backward, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply colimit.hom_ext
    intro d
    have hw := colimit.w D (normTo d)
    change sphere.{u, v}.map (κ d).hom ≫ colimit.ι D d =
      colimit.ι D (CostructuredArrow.mk (norm d).hom) at hw
    have hCancel : sphere.{u, v}.map (κ d).inv ≫ sphere.{u, v}.map (κ d).hom =
        𝟙 (sphere.{u, v}.obj d.left) :=
      (sphere.{u, v}.map_comp (κ d).inv (κ d).hom).symm.trans
        ((congrArg sphere.{u, v}.map (κ d).inv_hom_id).trans
          (sphere.{u, v}.map_id d.left))
    have hNormalize : sphere.{u, v}.map (κ d).inv ≫
        colimit.ι D (CostructuredArrow.mk (norm d).hom) = colimit.ι D d :=
      (congrArg (fun q => sphere.{u, v}.map (κ d).inv ≫ q) hw.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ colimit.ι D d) hCancel).trans (Category.id_comp _)))
    have hFirst : colimit.ι D d ≫ (forward ≫ backward) =
        (sphere.{u, v}.map (κ d).inv ≫ colimit.ι J
          (norm d : ActionCategory H E)) ≫ backward :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ backward) (forwardLeg d))
    have hLast :
        (sphere.{u, v}.map (κ d).inv ≫ colimit.ι J
          (norm d : ActionCategory H E)) ≫ backward =
        sphere.{u, v}.map (κ d).inv ≫
          colimit.ι D (CostructuredArrow.mk (norm d).hom) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => sphere.{u, v}.map (κ d).inv ≫ q)
          (backwardLeg (norm d : ActionCategory H E)))
    exact hFirst.trans (hLast.trans (hNormalize.trans (Category.comp_id _).symm))
  · apply colimit.hom_ext
    intro x
    have hw := colimit.w J (scalarArrow (x := x))
    change sphere.{u, v}.map (κ (dx x)).inv ≫ colimit.ι J
      (norm (dx x) : ActionCategory H E) = colimit.ι J x at hw
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ forward) (backwardLeg x)).trans
        ((forwardLeg (dx x)).trans (hw.trans (Category.comp_id _).symm)))


/-- The actual finite orbit index retains the original free first-block action. -/
def cosetIndex (n m : ℕ) : Type :=
  letI := blockMulAction (card (m - n)) (card n) (card m)
  MulAction.orbitRel.Quotient (Aut (card (m - n)))
    (card (m - n) ⊗ card n ≅ card m)

/-- The literal finite copower of the actual original residual sphere power. -/
def sphereCopower (n m : ℕ) : PointedCGWH.{u, v} :=
  ∐ (fun _ : cosetIndex n m => sphere.{u, v}.obj (card (m - n)))

/-- The full actual action coefficient colimit has its original twisted orbit-copower Iso. -/
def actionToCopowerIso (n m : ℕ) :
    colimit (normalizedDiagram n m) ≅ sphereCopower n m := by
  let R := card (m - n)
  let N := card n
  let M := card m
  letI := blockMulAction R N M
  exact ActionCategory.freeActionColimitCopowerIso
    (Aut R) (R ⊗ N ≅ M) (sphere.{u, v}.obj R) (sphereBlockAction R)
    (blockMulAction_free R N M)

/-- The genuine full native operator coend is a finite copower of its original sphere power. -/
def nativeSphereCopowerIso {n m : ℕ} (h : n ≤ m) :
    nativeHom (card n) (card m) ≅ sphereCopower n m :=
  nativeToBlockIso (card n) (card m) ≪≫
    normalizedColimitIso h ≪≫ actionToCopowerIso n m

/-- The complete original coefficient normalization determines every forward generator. -/
theorem normalizedColimitIso_generator {n m : ℕ} (h : n ≤ m)
    (d : BlockDecomposition (card n) (card m)) :
    letI := blockMulAction (card (m - n)) (card n) (card m)
    colimit.ι (blockDiagram (card n) (card m)) d ≫
      (normalizedColimitIso h).hom =
    sphere.{u, v}.map (cardComplementIso h d).inv ≫ colimit.ι (normalizedDiagram n m)
      (cardNormalizedBlock h d : ActionCategory (Aut (card (m - n)))
        (card (m - n) ⊗ card n ≅ card m)) := by
  exact colimit.ι_desc (normalizedForwardCocone h) d

/-- Every complete native forward sphere generator retains its original automorphism twist. -/
theorem nativeSphereCopowerIso_generator {n m : ℕ} (h : n ≤ m)
    (a : I) (f : (a ⊗ card n) ⟶ card m) :
    let _ := blockMulAction (card (m - n)) (card n) (card m)
    let d : BlockDecomposition (card n) (card m) :=
      CostructuredArrow.mk f
    let e := cardNormalizedBlock h d
    operatorGenerator a (card n) (card m) f ≫
      (nativeSphereCopowerIso h).hom =
    sphere.{u, v}.map (cardComplementIso h d).inv ≫
      End.asHom (sphereBlockAction (card (m - n))
        (ActionCategory.freeActionTwist (Aut (card (m - n)))
          (card (m - n) ⊗ card n ≅ card m)
          (blockMulAction_free (card (m - n)) (card n)
            (card m)) e)) ≫
      Sigma.ι (fun _ : cosetIndex n m => sphere.{u, v}.obj (card (m - n)))
        (Quotient.mk'' e) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let _ := blockMulAction R N M
  let d : BlockDecomposition N M := CostructuredArrow.mk f
  let e := cardNormalizedBlock h d
  let D := blockDiagram N M
  let J := normalizedDiagram n m
  let q₁ : nativeHom N M ⟶ colimit D := (nativeToBlockIso N M).hom
  let q₂ : colimit D ⟶ colimit J := (normalizedColimitIso h).hom
  let q₃ : colimit J ⟶ sphereCopower n m := (actionToCopowerIso n m).hom
  have h₁ : operatorGenerator a N M f ≫ q₁ = colimit.ι D d :=
    nativeToBlock_generator N M a f
  have h₂ : colimit.ι D d ≫ q₂ =
      sphere.{u, v}.map (cardComplementIso h d).inv ≫
        colimit.ι J (e : ActionCategory (Aut R) (R ⊗ N ≅ M)) :=
    normalizedColimitIso_generator h d
  have h₃ :
      colimit.ι J (e : ActionCategory (Aut R) (R ⊗ N ≅ M)) ≫ q₃ =
      End.asHom (sphereBlockAction R
        (ActionCategory.freeActionTwist (Aut R) (R ⊗ N ≅ M)
          (blockMulAction_free R N M) e)) ≫
      Sigma.ι (fun _ : cosetIndex n m => sphere.{u, v}.obj R) (Quotient.mk'' e) :=
    ActionCategory.freeActionColimitCopowerIso_generator
      (Aut R) (R ⊗ N ≅ M) (sphere.{u, v}.obj R) (sphereBlockAction R)
      (blockMulAction_free R N M) e
  change operatorGenerator a N M f ≫ (q₁ ≫ q₂ ≫ q₃) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (q₂ ≫ q₃)) h₁).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ q₃) h₂).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun q => sphere.{u, v}.map (cardComplementIso h d).inv ≫ q) h₃).trans
              (Category.assoc _ _ _).symm)))))


/-- The full finite sphere index has an actual finite type witness. -/
theorem cosetIndex_finite {n m : ℕ} (h : n ≤ m) : Finite (cosetIndex n m) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let b : R ⊗ N ≅ M := eqToIso (congrArg card (Nat.sub_add_cancel h))
  let e : (R ⊗ N ≅ M) ≃ Equiv.Perm (Fin m) :=
    (blockIsoEquivAut R N M b).trans (finAutEquiv M).toEquiv
  let _ : Fintype (R ⊗ N ≅ M) := Fintype.ofEquiv (Equiv.Perm (Fin m)) e.symm
  let _ := blockMulAction R N M
  change Finite (MulAction.orbitRel.Quotient (Aut R) (R ⊗ N ≅ M))
  infer_instance

/-- Below the original source cardinality the actual block category has no objects. -/
theorem blockDecomposition_isEmpty_of_gt {n m : ℕ} (h : m < n) :
    IsEmpty (BlockDecomposition (card n) (card m)) := by
  refine ⟨fun d => ?_⟩
  have hObj : (d.left ⊗ card n).of = (card m).of :=
    FintypeCat.Skeleton.is_skeletal ⟨d.hom.iso⟩
  have hAdd := congrArg FintypeCat.Skeleton.len hObj
  change d.left.of.len + n = m at hAdd
  have hn : n ≤ d.left.of.len + n := Nat.le_add_left _ _
  have hn' : n ≤ m := hAdd ▸ hn
  exact (Nat.not_lt_of_ge hn') h

/-- The literal native Free component is the original finite sphere copower after tensoring. -/
def nativeFreeComponentCopowerIso {n m : ℕ} (h : n ≤ m) (X : PointedCGWH.{u, v}) :
    (Free.object (symmetricOperatorObj.{u, v} (card n)) X).toEnrichedFunctor.obj
      (symmetricOperatorObj.{u, v} (card m)) ≅
        ∐ (fun _ : cosetIndex n m => X ⊗ sphere.{u, v}.obj (card (m - n))) :=
  whiskerLeftIso X (nativeSphereCopowerIso h) ≪≫
    PreservesCoproduct.iso (tensorLeft X)
      (fun _ : cosetIndex n m => sphere.{u, v}.obj (card (m - n)))

/-- Every original tensor copower inverse retains its actual original coend inverse. -/
theorem nativeFreeComponentCopowerIso_inverse_generator {n m : ℕ} (h : n ≤ m)
    (X : PointedCGWH.{u, v}) (q : cosetIndex n m) :
    Sigma.ι (fun _ : cosetIndex n m => X ⊗ sphere.{u, v}.obj (card (m - n))) q ≫
      (nativeFreeComponentCopowerIso h X).inv =
    X ◁ (Sigma.ι (fun _ : cosetIndex n m => sphere.{u, v}.obj (card (m - n))) q ≫
      (nativeSphereCopowerIso h).inv) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let F := tensorLeft X
  let A : cosetIndex n m → PointedCGWH.{u, v} := fun _ => sphere.{u, v}.obj R
  let e : F.obj (∐ A) ≅ ∐ (fun q => F.obj (A q)) := PreservesCoproduct.iso F A
  let φ : nativeHom N M ≅ ∐ A := nativeSphereCopowerIso h
  let t : F.obj (∐ A) ⟶ X ⊗ nativeHom N M := (whiskerLeftIso X φ).inv
  let j : F.obj (A q) ⟶ ∐ (fun q => F.obj (A q)) :=
    Sigma.ι (fun q => F.obj (A q)) q
  have hPres : e.inv = sigmaComparison F A := PreservesCoproduct.inv_hom F A
  have hι : j ≫ e.inv = F.map (Sigma.ι A q) :=
    (congrArg (fun z => j ≫ z) hPres).trans (ι_comp_sigmaComparison F A q)
  have hTensor : F.map (Sigma.ι A q) ≫ t = X ◁ (Sigma.ι A q ≫ φ.inv) :=
    (whiskerLeft_comp X (Sigma.ι A q) φ.inv).symm
  change j ≫ (e.inv ≫ t) = X ◁ (Sigma.ι A q ≫ φ.inv)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ t) hι).trans hTensor)


/-- Complete native Free coefficient maps commute with the full actual inverse copower function. -/
theorem nativeFreeComponentCopowerIso_coefficient {n m : ℕ} (h : n ≤ m)
    {X Y : PointedCGWH.{u, v}} (p : X ⟶ Y) :
    (nativeFreeComponentCopowerIso h X).inv ≫
      (p ▷ nativeHom (card n) (card m)) =
    CategoryTheory.Limits.Sigma.map
      (fun _ : cosetIndex n m => p ▷ sphere.{u, v}.obj (card (m - n))) ≫
      (nativeFreeComponentCopowerIso h Y).inv := by
  apply Sigma.hom_ext
  intro q
  rw [← Category.assoc, nativeFreeComponentCopowerIso_inverse_generator,
    ← Category.assoc, Sigma.ι_map, Category.assoc,
    nativeFreeComponentCopowerIso_inverse_generator]
  exact whisker_exchange p
    (Sigma.ι (fun _ : cosetIndex n m => sphere.{u, v}.obj (card (m - n))) q ≫
      (nativeSphereCopowerIso h).inv)

end PointedCGWH.SymmetricOperatorHom
