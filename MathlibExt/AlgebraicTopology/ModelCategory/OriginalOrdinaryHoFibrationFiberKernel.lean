/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryHoFibrationSource
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberKernel
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryHoZero

/-!
# Covariant fiber images of every original ordinary-Ho arrow

The source is the original fixed-cardinal J fibration of the original Q/R
representative. Its caller's limiting pullback retains both projections.
The model's actual covering-homotopy image law is transported through the
whole source/target comparison and the localization preimage of every Ho
coefficient. No fibration representative, kernel or weak comparison is
supplied as a desired outcome. This first covariant image position is not
the complete signed long exact sequence or a distinguished-triangle axiom.
-/

set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalOrdinaryHoFibrationFiberKernel

section Transport
variable {D : Type*} [Category* D]

private theorem transportedImage {K K' A A' F : D} (e : K ≅ K') (a : A ≅ A')
    (i : F ⟶ A) (h : K' ⟶ A') :
    (∃ l : K' ⟶ F, l ≫ (i ≫ a.hom) = h) ↔
      ∃ l : K ⟶ F, l ≫ i = (e.hom ≫ h) ≫ a.inv := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨e.hom ≫ l, ?_⟩
    calc
      (e.hom ≫ l) ≫ i = (e.hom ≫ (l ≫ (i ≫ a.hom))) ≫ a.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (e.hom ≫ h) ≫ a.inv := by rw [hl]
  · rintro ⟨l, hl⟩
    refine ⟨e.inv ≫ l, ?_⟩
    calc
      (e.inv ≫ l) ≫ (i ≫ a.hom) = e.inv ≫ ((l ≫ i) ≫ a.hom) := by
        simp only [Category.assoc]
      _ = e.inv ≫ (((e.hom ≫ h) ≫ a.inv) ≫ a.hom) := by rw [hl]
      _ = h := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem transportedNull {K K' A A' B B' : D}
    (e : K ≅ K') (a : A ≅ A') (b : B ≅ B')
    (p : A ⟶ B) (f : A' ⟶ B') (hp : p ≫ b.hom = a.hom ≫ f)
    (n : K ⟶ B) (n' : K' ⟶ B') (hn : n ≫ b.hom = e.hom ≫ n') (h : K' ⟶ A') :
    ((e.hom ≫ h) ≫ a.inv) ≫ p = n ↔ h ≫ f = n' := by
  have fac : (((e.hom ≫ h) ≫ a.inv) ≫ p) ≫ b.hom = e.hom ≫ (h ≫ f) := by
    simp only [Category.assoc, hp, Iso.inv_hom_id_assoc]
  constructor
  · intro ht
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ (h ≫ f) = (((e.hom ≫ h) ≫ a.inv) ≫ p) ≫ b.hom := fac.symm
      _ = n ≫ b.hom := by rw [ht]
      _ = e.hom ≫ n' := hn
  · intro ht
    apply (cancel_mono b.hom).mp
    rw [fac, ht, hn]

end Transport

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "H" => toHomotopyCategory C

/-- The whole original caller zero is the original source-built zero in Ho. -/
def null (T Y : HomotopyCategory C) : T ⟶ Y :=
  (GeneratedOrdinaryHoZero.isZero g Z hZ).isTerminal.from T ≫
    (GeneratedOrdinaryHoZero.isZero g Z hZ).isInitial.to Y

/-- Every Ho coefficient morphism retains the same entire original null map. -/
theorem null_precomp {T T' Y : HomotopyCategory C} (a : T' ⟶ T) :
    a ≫ null g Z hZ T Y = null g Z hZ T' Y := by
  unfold null
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ (GeneratedOrdinaryHoZero.isZero g Z hZ).isInitial.to Y)
    ((GeneratedOrdinaryHoZero.isZero g Z hZ).isTerminal.hom_ext _ _)

/-- Every target Ho morphism preserves the actual original null map. -/
theorem null_postcomp {T Y Y' : HomotopyCategory C} (a : Y ⟶ Y') :
    null g Z hZ T Y ≫ a = null g Z hZ T Y' := by
  unfold null
  rw [Category.assoc]
  exact congrArg (fun k => (GeneratedOrdinaryHoZero.isZero g Z hZ).isTerminal.from T ≫ k)
    ((GeneratedOrdinaryHoZero.isZero g Z hZ).isInitial.hom_ext _ _)

/-- Projection of the entire point-set zero word is exactly the source-built Ho zero. -/
theorem null_image (K B : C) :
    (H).map (OrdinaryHoChosenFiberKernel.nullMap Z hZ K B) =
      null g Z hZ ((H).obj K) ((H).obj B) := by
  unfold OrdinaryHoChosenFiberKernel.nullMap null
  rw [Functor.map_comp]
  congr 1
  · exact (GeneratedOrdinaryHoZero.isZero g Z hZ).isTerminal.hom_ext _ _
  · exact (GeneratedOrdinaryHoZero.isZero g Z hZ).isInitial.hom_ext _ _

variable {X Y : HomotopyCategory C} (f : X ⟶ Y)
  (s : PullbackCone (OriginalOrdinaryHoFibrationSource.projection g f)
    (hZ.isInitial.to (OriginalOrdinaryHoArrowSource.targetObject g Y)))
  (hs : IsLimit s)

/-- The actual fiber object is the caller's original pullback of the generated J projection. -/
def fiber : HomotopyCategory C := (H).obj s.pt

/-- The whole first leg is the actual fiber projection followed by the original source Iso. -/
def inclusion : fiber g Z hZ f s ⟶ X :=
  (H).map s.fst ≫ (OriginalOrdinaryHoFibrationSource.sourceIso g f).hom

include hs

/-- Every complete Ho coefficient has the covariant original fiber image/null-kernel law. -/
theorem fiber_image_iff (T : HomotopyCategory C) (h : T ⟶ X) :
    (∃ l : T ⟶ fiber g Z hZ f s, l ≫ inclusion g Z hZ f s = h) ↔
      h ≫ f = null g Z hZ T Y := by
  let K := OriginalOrdinaryHoArrowSource.preimage T
  let e := OriginalOrdinaryHoArrowSource.preimageIso T
  let p := OriginalOrdinaryHoFibrationSource.projection g f
  let : Fibration p := OriginalOrdinaryHoFibrationSource.projection_fibration g f
  let : IsFibrant (OriginalOrdinaryHoArrowSource.targetObject g Y) :=
    OriginalOrdinaryHoArrowSource.target_isFibrant g Y
  have old := OrdinaryHoChosenFiberKernel.chosenFiberHoImage_anyCoefficient_iff
    Z hZ K p s hs ((e.hom ≫ h) ≫ (OriginalOrdinaryHoFibrationSource.sourceIso g f).inv)
  have zero : (H).map (OrdinaryHoChosenFiberKernel.nullMap Z hZ K
      (OriginalOrdinaryHoArrowSource.targetObject g Y)) ≫
        (OriginalOrdinaryHoArrowSource.targetIso g Y).hom = e.hom ≫ null g Z hZ T Y := by
    rw [null_image g Z hZ, null_postcomp g Z hZ]
    exact (null_precomp g Z hZ e.hom).symm
  exact (transportedImage e (OriginalOrdinaryHoFibrationSource.sourceIso g f)
    ((H).map s.fst) h).trans (old.trans
      (transportedNull e (OriginalOrdinaryHoFibrationSource.sourceIso g f)
        (OriginalOrdinaryHoArrowSource.targetIso g Y) ((H).map p) f
        (OriginalOrdinaryHoFibrationSource.projection_square g f) _ _ zero h))

/-- A full original Ho null map has an actual lift through the same caller fiber. -/
def lift (T : HomotopyCategory C) (h : T ⟶ X) (hh : h ≫ f = null g Z hZ T Y) :
    T ⟶ fiber g Z hZ f s :=
  Classical.choose ((fiber_image_iff g Z hZ f s hs T h).mpr hh)

/-- Its entire first-leg composite reconstructs the actual caller's Ho map. -/
theorem lift_fac (T : HomotopyCategory C) (h : T ⟶ X)
    (hh : h ≫ f = null g Z hZ T Y) :
    lift g Z hZ f s hs T h hh ≫ inclusion g Z hZ f s = h :=
  Classical.choose_spec ((fiber_image_iff g Z hZ f s hs T h).mpr hh)

end HomotopicalAlgebra.OriginalOrdinaryHoFibrationFiberKernel
