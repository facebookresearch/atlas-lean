/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uV uJ
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subfunctor

variable {C : Type uC} [Category.{vC} C] {D : C ⥤ Type uV}
    {J : Type uJ} [LinearOrder J]

/-- The original monotone subobjects in the SAME fixed target, with inclusion maps. -/
def chainDiagram (U : J → Subfunctor D) (hU : Monotone U) : J ⥤ C ⥤ Type uV where
  obj j := (U j).toFunctor
  map f := homOfLe (hU (leOfHom f))
  map_id j := by
    ext X x
    rfl
  map_comp f g := by
    ext X x
    rfl

/-- Actual original inclusions to the native pointwise union. -/
def chainUnionCocone (U : J → Subfunctor D) (hU : Monotone U) :
    Cocone (chainDiagram U hU) where
  pt := (⨆ j, U j).toFunctor
  ι :=
    { app j := homOfLe (le_iSup U j)
      naturality := by
        intro j k f
        ext X x
        rfl }

/-- The union cocone is colimiting; no Small-index or supplied colimit certificate. -/
def isColimitChainUnionCocone (U : J → Subfunctor D) (hU : Monotone U) :
    IsColimit (chainUnionCocone U hU) := by
  let _ : IsFilteredOrEmpty J := inferInstance
  apply evaluationJointlyReflectsColimits
  intro X
  apply Types.FilteredColimit.isColimitOf'
    (chainDiagram U hU ⋙ (evaluation C (Type uV)).obj X)
    (((evaluation C (Type uV)).obj X).mapCocone (chainUnionCocone U hU))
  · intro x
    have hx : ∃ j : J, x.val ∈ (U j).obj X := by
      simpa only [Subfunctor.iSup_obj, Set.mem_iUnion] using x.property
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, ⟨x.val, hj⟩, rfl⟩
  · intro j x y h
    have hxy : x = y := Subtype.ext
      (congrArg (fun z : (⨆ k, U k).toFunctor.obj X => z.val) h)
    refine ⟨j, 𝟙 j, ?_⟩
    simpa only [Functor.map_id, types_id_apply] using hxy

private theorem eqToIso_hom_ι {U V : Subfunctor D} (h : U = V) :
    (eqToIso (congrArg (fun T : Subfunctor D => T.toFunctor) h)).hom ≫ V.ι = U.ι := by
  cases h
  simp

section Continuous
variable [OrderBot J] [SuccOrder J] [WellFoundedLT J]

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
/-- Literal pointwise-union continuity is converted to the SAME original prefix cocones. -/
theorem chain_isWellOrderContinuous (U : J → Subfunctor D) (hU : Monotone U)
    (hlim : ∀ j : J, Order.IsSuccLimit j →
      U j = ⨆ k : Set.Iio j, U k.1) :
    (chainDiagram U hU).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    let V : Set.Iio j → Subfunctor D := fun k => U k.1
    have hV : Monotone V := fun _ _ h => hU h
    let e : (⨆ k : Set.Iio j, V k).toFunctor ≅ (U j).toFunctor :=
      eqToIso (congrArg (fun T : Subfunctor D => T.toFunctor) (hlim j hj).symm)
    have he : e.hom ≫ (U j).ι = (⨆ k : Set.Iio j, V k).ι :=
      eqToIso_hom_ι (hlim j hj).symm
    refine IsColimit.ofIsoColimit (isColimitChainUnionCocone V hV) ?_
    refine Cocone.ext e ?_
    intro k
    apply (cancel_mono (U j).ι).1
    change (homOfLe (le_iSup V k) ≫ e.hom) ≫ (U j).ι =
      homOfLe (hU k.2.le) ≫ (U j).ι
    rw [Category.assoc, he, homOfLe_ι, homOfLe_ι]⟩

/-- The ORIGINAL well-order diagram/union is a transfinite witness, from actual step memberships. -/
def chainTransfiniteUnion (U : J → Subfunctor D) (hU : Monotone U)
    (hlim : ∀ j : J, Order.IsSuccLimit j → U j = ⨆ k : Set.Iio j, U k.1)
    (P : MorphismProperty (C ⥤ Type uV))
    (hstep : ∀ j : J, ¬ IsMax j → P (homOfLe (hU (Order.le_succ j)))) :
    P.TransfiniteCompositionOfShape J (homOfLe (le_iSup U (⊥ : J))) where
  F := chainDiagram U hU
  isoBot := Iso.refl _
  isWellOrderContinuous := chain_isWellOrderContinuous U hU hlim
  incl := (chainUnionCocone U hU).ι
  isColimit := isColimitChainUnionCocone U hU
  fac := by
    ext X x
    rfl
  map_mem j hj := hstep j hj

/-- Canonical accumulated subobjects: starting A and only seeds STRICTLY earlier than j. -/
def strictPrefixUnion (A : Subfunctor D) (B : J → Subfunctor D) (j : J) : Subfunctor D :=
  A ⊔ ⨆ k : Set.Iio j, B k.1

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
theorem strictPrefixUnion_mono (A : Subfunctor D) (B : J → Subfunctor D) :
    Monotone (strictPrefixUnion A B) := by
  intro i j hij
  apply sup_le_sup le_rfl
  apply iSup_le
  intro k
  exact le_iSup_of_le ⟨k.1, lt_of_lt_of_le k.2 hij⟩ le_rfl

omit [SuccOrder J] [WellFoundedLT J] in
theorem strictPrefixUnion_bot (A : Subfunctor D) (B : J → Subfunctor D) :
    strictPrefixUnion A B ⊥ = A := by
  apply le_antisymm
  · apply sup_le le_rfl
    apply iSup_le
    rintro ⟨k, hk⟩
    exact (not_lt_of_ge bot_le hk).elim
  · exact le_sup_left

omit [WellFoundedLT J] in
/-- Every genuine limit is the actual union of ALL original earlier stages, by construction. -/
theorem strictPrefixUnion_limit (A : Subfunctor D) (B : J → Subfunctor D)
    (j : J) (hj : Order.IsSuccLimit j) :
    strictPrefixUnion A B j = ⨆ k : Set.Iio j, strictPrefixUnion A B k.1 := by
  apply le_antisymm
  · apply sup_le
    · exact le_trans le_sup_left
        (le_iSup (fun k : Set.Iio j => strictPrefixUnion A B k.1) ⟨⊥, hj.bot_lt⟩)
    · apply iSup_le
      intro k
      have hnotmax : ¬ IsMax k.1 := by
        intro hmax
        exact (not_le_of_gt k.2) (hmax k.2.le)
      have hk : k.1 < Order.succ k.1 := Order.lt_succ_of_not_isMax hnotmax
      have hseed : B k.1 ≤ strictPrefixUnion A B (Order.succ k.1) :=
        (le_iSup (fun s : Set.Iio (Order.succ k.1) => B s.1) ⟨k.1, hk⟩).trans le_sup_right
      exact hseed.trans
        (le_iSup (fun s : Set.Iio j => strictPrefixUnion A B s.1)
          ⟨Order.succ k.1, hj.succ_lt k.2⟩)
  · exact iSup_le (fun k => strictPrefixUnion_mono A B k.2.le)

/-- Starting at the ORIGINAL A, the same canonical union prefixes give actual native witnesses. -/
def strictPrefixTransfinite (A : Subfunctor D) (B : J → Subfunctor D)
    (P : MorphismProperty (C ⥤ Type uV))
    (hstep : ∀ j : J, ¬ IsMax j →
      P (homOfLe (strictPrefixUnion_mono A B (Order.le_succ j))))
    (t : J) :
    P.TransfiniteCompositionOfShape (Set.Iic t)
      (homOfLe (show A ≤ strictPrefixUnion A B t from le_sup_left)) := by
  let U := strictPrefixUnion A B
  let h := (chainTransfiniteUnion U (strictPrefixUnion_mono A B)
    (strictPrefixUnion_limit A B) P hstep).iic t
  let e : (U ⊥).toFunctor ≅ A.toFunctor :=
    eqToIso (congrArg (fun T : Subfunctor D => T.toFunctor) (strictPrefixUnion_bot A B))
  apply h.ofArrowIso (Arrow.isoMk e (Iso.refl _) ?_)
  apply (cancel_mono (U t).ι).1
  calc
    (e.hom ≫ homOfLe (show A ≤ U t from le_sup_left)) ≫ (U t).ι = e.hom ≫ A.ι := by
      rw [Category.assoc, homOfLe_ι]
    _ = (U ⊥).ι := by
      have hι {S T : Subfunctor D} (h : S = T) :
          (eqToIso (congrArg (fun T : Subfunctor D => T.toFunctor) h)).hom ≫ T.ι = S.ι := by
        cases h
        simp
      exact hι (strictPrefixUnion_bot A B)
    _ = (homOfLe (strictPrefixUnion_mono A B (show (⊥ : J) ≤ t from bot_le)) ≫ 𝟙 _) ≫
        (U t).ι := by
      rw [Category.comp_id]
      exact (homOfLe_ι (strictPrefixUnion_mono A B bot_le)).symm

end Continuous
end CategoryTheory.Subfunctor
