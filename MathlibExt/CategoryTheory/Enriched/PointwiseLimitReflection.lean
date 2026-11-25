/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Joint reflection of enriched limit cones

For a diagram of genuine enriched functors, evaluated universal properties
construct the limit lift of the supplied cone, including its full enriched
naturality. The cone point and legs are unchanged. Only the enriched category
and the supplied evaluated limits are required.
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
  {J : Type uJ} [Category.{vJ} J] {K : J ⥤ EnrichedFunctorCat V A}

/-- Lift through the caller's original evaluated cones with full enriched naturality. -/
def liftOfEvaluations (c : Cone K)
    (hc : ∀ a : A, IsLimit ((evaluation a).mapCone c)) (q : Cone K) : q.pt ⟶ c.pt :=
  GradedNatTrans.unitOfComponents
    (fun a => (hc a).lift ((evaluation a).mapCone q))
    (by
      intro a b
      apply (hc b).hom_ext
      intro j
      let H := a ⟶[V] b
      let la : q.pt.toEnrichedFunctor.obj a ⟶ c.pt.toEnrichedFunctor.obj a :=
        (hc a).lift ((evaluation a).mapCone q)
      let lb : q.pt.toEnrichedFunctor.obj b ⟶ c.pt.toEnrichedFunctor.obj b :=
        (hc b).lift ((evaluation b).mapCone q)
      let pa : c.pt.toEnrichedFunctor.obj a ⟶ (K.obj j).toEnrichedFunctor.obj a :=
        component (c.π.app j) a
      let pb : c.pt.toEnrichedFunctor.obj b ⟶ (K.obj j).toEnrichedFunctor.obj b :=
        component (c.π.app j) b
      let qa : q.pt.toEnrichedFunctor.obj a ⟶ (K.obj j).toEnrichedFunctor.obj a :=
        component (q.π.app j) a
      let qb : q.pt.toEnrichedFunctor.obj b ⟶ (K.obj j).toEnrichedFunctor.obj b :=
        component (q.π.app j) b
      let ac := MonoidalClosed.uncurry (c.pt.toEnrichedFunctor.map a b)
      let aq := MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b)
      let aj := MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)
      have hC : ac ≫ pb = (pa ▷ H) ≫ aj := by
        simpa only [ac, pb, pa, H, aj, component, Functor.const_obj_obj,
          tensorHom_id] using (c.π.app j).uncurriedNaturality a b
      have hQ : aq ≫ qb = (qa ▷ H) ≫ aj := by
        simpa only [aq, qb, qa, H, aj, component, Functor.const_obj_obj,
          tensorHom_id] using (q.π.app j).uncurriedNaturality a b
      have hA : la ≫ pa = qa := (hc a).fac ((evaluation a).mapCone q) j
      have hB : lb ≫ pb = qb := (hc b).fac ((evaluation b).mapCone q) j
      change (aq ≫ lb) ≫ pb = ((la ⊗ₘ 𝟙 H) ≫ ac) ≫ pb
      rw [tensorHom_id]
      have ht : ((la ▷ H) ≫ ac) ≫ pb = (qa ▷ H) ≫ aj := by
        rw [Category.assoc, hC, ← Category.assoc, ← comp_whiskerRight, hA]
      exact (Category.assoc aq lb pb).trans
        ((congrArg (fun z => aq ≫ z) hB).trans (hQ.trans ht.symm)))

/-- The actual limit lift has the caller's original evaluated lift as each component. -/
theorem liftOfEvaluations_component (c : Cone K)
    (hc : ∀ a : A, IsLimit ((evaluation a).mapCone c)) (q : Cone K) (a : A) :
    component (liftOfEvaluations c hc q) a = (hc a).lift ((evaluation a).mapCone q) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- Genuine evaluations jointly reflect the universal property of the unchanged original cone. -/
def evaluationJointlyReflectsLimits (c : Cone K)
    (hc : ∀ a : A, IsLimit ((evaluation a).mapCone c)) : IsLimit c where
  lift := liftOfEvaluations c hc
  fac q j := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [component_comp, liftOfEvaluations_component]
    exact (hc a).fac ((evaluation a).mapCone q) j
  uniq q m hm := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [liftOfEvaluations_component]
    apply (hc a).hom_ext
    intro j
    have h := congrArg (fun z => component z a) (hm j)
    rw [component_comp] at h
    exact h.trans ((hc a).fac ((evaluation a).mapCone q) j).symm

end CategoryTheory.EnrichedFunctorCat
