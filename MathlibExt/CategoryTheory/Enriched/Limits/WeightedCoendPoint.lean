/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uA

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.Enriched

open Limits BraidedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
  [HasCoproduct (weightedCoend.relations W F)]
  [HasCoproduct (weightedCoend.objects W F)]
  [HasCoequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)]

/-- The tensor-unit-point specialization of the entire original coend relation.
The point is arbitrary; neither relation face nor an ordinary category on A is supplied. -/
theorem weightedCoend.condition_unitPoint
    (a b : A) (e : (𝟙_ V) ⟶ (a ⟶[V] b)) :
    (((ρ_ (W.obj (op b))).inv ≫
        W.obj (op b) ◁ e ≫
        MonoidalClosed.uncurry (W.map (op b) (op a))) ⊗ₘ 𝟙 (F.obj a)) ≫
        weightedCoend.ι W F a =
      (𝟙 (W.obj (op b)) ⊗ₘ
        ((ρ_ (F.obj a)).inv ≫ F.obj a ◁ e ≫
          MonoidalClosed.uncurry (F.map a b))) ≫
        weightedCoend.ι W F b := by
  let U : V := W.obj (op b)
  let U' : V := W.obj (op a)
  let H : V := a ⟶[V] b
  let X : V := F.obj a
  let Y : V := F.obj b
  let p : U ⊗ H ⟶ U' := MonoidalClosed.uncurry (W.map (op b) (op a))
  let q : X ⊗ H ⟶ Y := MonoidalClosed.uncurry (F.map a b)
  let pre : U ⊗ X ⟶ U ⊗ (H ⊗ X) :=
    U ◁ ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X))
  let wf : U ⊗ (H ⊗ X) ⟶ U' ⊗ X :=
    (α_ U H X).inv ≫ (p ⊗ₘ 𝟙 X)
  let df : U ⊗ (H ⊗ X) ⟶ U ⊗ Y :=
    U ◁ ((β_ H X).hom ≫ q)
  let wa : U ⟶ U' := (ρ_ U).inv ≫ U ◁ e ≫ p
  let fa : X ⟶ Y := (ρ_ X).inv ≫ X ◁ e ≫ q
  have hNatural :
      U ◁ (e ⊗ₘ 𝟙 X) ≫ (α_ U H X).inv =
        (α_ U (𝟙_ V) X).inv ≫ ((U ◁ e) ▷ X) := by
    simpa only [id_tensorHom, tensorHom_id] using
      associator_inv_naturality (𝟙 U) e (𝟙 X)
  have hTriangle :
      U ◁ (λ_ X).inv ≫ (α_ U (𝟙_ V) X).inv = (ρ_ U).inv ▷ X := by
    monoidal
  have hLeft : pre ≫ wf = wa ⊗ₘ 𝟙 X := by
    calc
      pre ≫ wf = U ◁ (λ_ X).inv ≫
          (U ◁ (e ⊗ₘ 𝟙 X) ≫ (α_ U H X).inv) ≫ (p ⊗ₘ 𝟙 X) := by
        simp only [pre, wf, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = U ◁ (λ_ X).inv ≫ (α_ U (𝟙_ V) X).inv ≫
          ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X) := by
        simpa only [Category.assoc] using congrArg
          (fun f : U ⊗ ((𝟙_ V) ⊗ X) ⟶ (U ⊗ H) ⊗ X =>
            U ◁ (λ_ X).inv ≫ f ≫ (p ⊗ₘ 𝟙 X)) hNatural
      _ = ((ρ_ U).inv ▷ X) ≫ ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X) := by
        simpa only [Category.assoc] using congrArg
          (fun f : U ⊗ X ⟶ (U ⊗ (𝟙_ V)) ⊗ X =>
            f ≫ ((U ◁ e) ▷ X) ≫ (p ⊗ₘ 𝟙 X)) hTriangle
      _ = wa ⊗ₘ 𝟙 X := by
        simpa only [wa, comp_whiskerRight, Category.assoc] using
          whiskerRight_comp_tensorHom ((ρ_ U).inv ≫ U ◁ e) p (𝟙 X)
  have hUnitCross :
      ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) ≫ (β_ H X).hom =
        (ρ_ X).inv ≫ X ◁ e := by
    simpa only [id_tensorHom, Category.assoc,
      CategoryTheory.braiding_tensorUnit_left, Iso.inv_hom_id_assoc] using
      congrArg (fun f : (𝟙_ V) ⊗ X ⟶ X ⊗ H => (λ_ X).inv ≫ f)
        (braiding_naturality e (𝟙 X))
  have hRight : pre ≫ df = U ◁ fa := by
    calc
      pre ≫ df = U ◁ (((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) ≫
          (β_ H X).hom ≫ q) := by
        simp only [pre, df, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = U ◁ (((ρ_ X).inv ≫ X ◁ e) ≫ q) :=
        (congrArg (fun f : X ⟶ Y => U ◁ f)
          (Category.assoc ((λ_ X).inv ≫ (e ⊗ₘ 𝟙 X)) (β_ H X).hom q).symm).trans
          (congrArg (fun f : X ⟶ X ⊗ H => U ◁ (f ≫ q)) hUnitCross)
      _ = U ◁ fa := by simp only [fa, Category.assoc]
  have hFull : wf ≫ weightedCoend.ι W F a = df ≫ weightedCoend.ι W F b :=
    weightedCoend.condition W F a b
  have hPoint := congrArg
    (fun f : U ⊗ (H ⊗ X) ⟶ weightedCoend W F => pre ≫ f) hFull
  have hWeight : pre ≫ (wf ≫ weightedCoend.ι W F a) =
      (wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W F a :=
    (Category.assoc pre wf (weightedCoend.ι W F a)).symm.trans
      (congrArg (fun f : U ⊗ X ⟶ U' ⊗ X => f ≫ weightedCoend.ι W F a) hLeft)
  have hDiagram : pre ≫ (df ≫ weightedCoend.ι W F b) =
      (𝟙 U ⊗ₘ fa) ≫ weightedCoend.ι W F b :=
    (Category.assoc pre df (weightedCoend.ι W F b)).symm.trans
      ((congrArg (fun f : U ⊗ X ⟶ U ⊗ Y => f ≫ weightedCoend.ι W F b) hRight).trans
        (congrArg (fun f : U ⊗ X ⟶ U ⊗ Y => f ≫ weightedCoend.ι W F b)
          (MonoidalCategory.id_tensorHom U fa).symm))
  exact hWeight.symm.trans (hPoint.trans hDiagram)

end CategoryTheory.Enriched
