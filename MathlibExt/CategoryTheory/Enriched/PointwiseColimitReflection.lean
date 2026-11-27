/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Joint reflection of original enriched colimit cocones

The original cocone point, legs and full Hom action remain fixed. Evaluated
universal properties supply the actual enriched descender and its uniqueness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uA uV vV uJ vJ
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  {K : J ⥤ EnrichedFunctorCat V A}

/-- Descend the supplied actual cocone with full original Hom naturality. -/
def descOfEvaluations (c : Cocone K)
    (hc : ∀ a : A, IsColimit ((evaluation a).mapCocone c)) (q : Cocone K) :
    c.pt ⟶ q.pt := by
  let components : ∀ a : A, c.pt.toEnrichedFunctor.obj a ⟶ q.pt.toEnrichedFunctor.obj a :=
    fun a => (hc a).desc ((evaluation a).mapCocone q)
  exact GradedNatTrans.unitOfComponents
    components
    (by
      intro a b
      apply (isColimitOfPreserves (tensorRight (a ⟶[V] b)) (hc a)).hom_ext
      intro j
      let H := a ⟶[V] b
      let iA : (K.obj j).toEnrichedFunctor.obj a ⟶ c.pt.toEnrichedFunctor.obj a :=
        component (c.ι.app j) a
      let iB : (K.obj j).toEnrichedFunctor.obj b ⟶ c.pt.toEnrichedFunctor.obj b :=
        component (c.ι.app j) b
      let qA : (K.obj j).toEnrichedFunctor.obj a ⟶ q.pt.toEnrichedFunctor.obj a :=
        component (q.ι.app j) a
      let qB : (K.obj j).toEnrichedFunctor.obj b ⟶ q.pt.toEnrichedFunctor.obj b :=
        component (q.ι.app j) b
      let dA : c.pt.toEnrichedFunctor.obj a ⟶ q.pt.toEnrichedFunctor.obj a :=
        (hc a).desc ((evaluation a).mapCocone q)
      let dB : c.pt.toEnrichedFunctor.obj b ⟶ q.pt.toEnrichedFunctor.obj b :=
        (hc b).desc ((evaluation b).mapCocone q)
      let actJ := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      let actC := MonoidalClosed.uncurry (c.pt.toEnrichedFunctor.map a b)
      let actQ := MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b)
      have hC : actJ ≫ iB = (iA ▷ H) ≫ actC := by
        simpa only [actJ, actC, iA, iB, H, component, Functor.const_obj_obj,
          tensorHom_id] using
          (c.ι.app j).uncurriedNaturality a b
      have hQ : actJ ≫ qB = (qA ▷ H) ≫ actQ := by
        simpa only [actJ, actQ, qA, qB, H, component, Functor.const_obj_obj,
          tensorHom_id] using
          (q.ι.app j).uncurriedNaturality a b
      have hA : iA ≫ dA = qA := (hc a).fac ((evaluation a).mapCocone q) j
      have hB : iB ≫ dB = qB := (hc b).fac ((evaluation b).mapCocone q) j
      change (iA ▷ H) ≫ actC ≫ dB = (iA ▷ H) ≫ (dA ⊗ₘ 𝟙 H) ≫ actQ
      rw [tensorHom_id]
      calc
        _ = actJ ≫ iB ≫ dB := by rw [← Category.assoc, ← hC, Category.assoc]
        _ = actJ ≫ qB := by rw [hB]
        _ = (qA ▷ H) ≫ actQ := hQ
        _ = _ := by rw [← hA, comp_whiskerRight, Category.assoc])

/-- The complete genuine descender has exactly the original evaluated component. -/
theorem descOfEvaluations_component (c : Cocone K)
    (hc : ∀ a : A, IsColimit ((evaluation a).mapCocone c)) (q : Cocone K) (a : A) :
    component (descOfEvaluations c hc q) a = (hc a).desc ((evaluation a).mapCocone q) := by
  exact GradedNatTrans.unitOfComponents_component _ _ a

/-- Genuine evaluations jointly reflect the actual supplied cocone's UP. -/
def evaluationJointlyReflectsColimits (c : Cocone K)
    (hc : ∀ a : A, IsColimit ((evaluation a).mapCocone c)) : IsColimit c where
  desc := descOfEvaluations c hc
  fac q j := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [component_comp]
    rw [descOfEvaluations_component]
    exact (hc a).fac ((evaluation a).mapCocone q) j
  uniq q m hm := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [descOfEvaluations_component]
    apply (hc a).hom_ext
    intro j
    have h := congrArg (fun z => component z a) (hm j)
    rw [component_comp] at h
    exact h.trans ((hc a).fac ((evaluation a).mapCocone q) j).symm

/-- The entire actual descender component function is the original evaluated descent. -/
theorem evaluationJointlyReflectsColimits_desc_function (c : Cocone K)
    (hc : ∀ a : A, IsColimit ((evaluation a).mapCocone c)) :
    (fun (q : Cocone K) (a : A) =>
      component ((evaluationJointlyReflectsColimits (V := V) (A := A) c hc).desc q) a) =
    fun q a => (hc a).desc ((evaluation a).mapCocone q) := by
  funext q a
  exact descOfEvaluations_component c hc q a

/-- An original square is a pushout exactly when all its genuine evaluations are. -/
theorem isPushout_iff_evaluation [HasPushouts V]
    {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (hcomm : i ≫ f' = f ≫ j) :
    IsPushout i f f' j ↔
      ∀ a : A, IsPushout ((evaluation a).map i) ((evaluation a).map f)
        ((evaluation a).map f') ((evaluation a).map j) := by
  constructor
  · intro h a
    exact h.map (evaluation a)
  · intro h
    let c : PushoutCocone i f := PushoutCocone.mk f' j hcomm
    apply IsPushout.of_isColimit (c := c)
    apply evaluationJointlyReflectsColimits (V := V) (A := A) c
    intro a
    let t := (evaluation a).mapCocone c
    let e := diagramIsoSpan (span i f ⋙ evaluation a)
    refine (IsColimit.precomposeInvEquiv e t).1 ?_
    exact IsColimit.ofIsoColimit (h a).isColimit (PushoutCocone.isoMk t).symm

end CategoryTheory.EnrichedFunctorCat
