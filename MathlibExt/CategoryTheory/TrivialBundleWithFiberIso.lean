/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.TrivialBundleWithFiber

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace TrivialBundleWithFiber

variable {C : Type u} [Category.{v} C]
variable {F E E' B : C}

/-- Transport a fixed-fiber presentation across an over-base isomorphism.

Given `e : E ≅ E'` with `e.hom ≫ p' = p` and a presentation `h'` of `p'`
with fixed fiber `F`, this builds a presentation of `p` with the same fiber
and second projection `e.hom ≫ h'.r`. The proof uses the existing
product-cone limit structure with explicit isomorphism composition; inverse
equations are handled by `Category.assoc`. Only the fixed fiber is preserved;
no chart beyond the two presentations is claimed. -/
noncomputable def ofIso {p : E ⟶ B} {p' : E' ⟶ B} (e : E ≅ E')
    (heq : e.hom ≫ p' = p) (h' : TrivialBundleWithFiber F p') :
    TrivialBundleWithFiber F p where
  r := e.hom ≫ h'.r
  isLimit := by
    refine BinaryFan.isLimitMk
      (fun s => BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd ≫ e.inv) ?_ ?_ ?_
    · intro s
      have hInv : e.inv ≫ p = p' := by
        rw [← heq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg
            (fun x =>
              BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd ≫ x) hInv)
          (BinaryFan.IsLimit.lift_fst _ _ _))
    · intro s
      have hInvR : e.inv ≫ (e.hom ≫ h'.r) = h'.r := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg
            (fun x =>
              BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd ≫ x) hInvR)
          (BinaryFan.IsLimit.lift_snd _ _ _))
    · intro s m hm₁ hm₂
      have hE : m ≫ e.hom =
          BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd := by
        apply BinaryFan.IsLimit.hom_ext h'.isLimit
        · have hL : BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd ≫ p' =
              s.fst := BinaryFan.IsLimit.lift_fst _ _ _
          have hM : (m ≫ e.hom) ≫ p' = s.fst := by
            rw [Category.assoc, heq, hm₁]
          exact hM.trans hL.symm
        · have hL : BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd ≫ h'.r =
              s.snd := BinaryFan.IsLimit.lift_snd _ _ _
          have hM : (m ≫ e.hom) ≫ h'.r = s.snd :=
            Eq.trans (Category.assoc _ _ _) hm₂
          exact hM.trans hL.symm
      calc m = (m ≫ e.hom) ≫ e.inv := by
              rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        _ = BinaryFan.IsLimit.lift h'.isLimit s.fst s.snd ≫ e.inv := by
            rw [hE]

/-- Reverse transport across the same over-base equation.

This is exactly `ofIso` applied to `e.symm`; no separate limit argument is
made. It moves a presentation of `p` to one of `p'`. -/
noncomputable def ofIso_rev {p : E ⟶ B} {p' : E' ⟶ B} (e : E ≅ E')
    (heq : e.hom ≫ p' = p) (h : TrivialBundleWithFiber F p) :
    TrivialBundleWithFiber F p' :=
  ofIso e.symm (by
    have : e.inv ≫ p = p' := by
      rw [← heq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact this) h

/-- Fiber-side transport along a fiber isomorphism.

Given `e : F ≅ G` and a presentation `h` of `p` with fixed fiber `G`, this
builds a presentation of the same `p` with the same total object and base,
but fixed fiber `F` and second projection `h.r ≫ e.inv`. Only the fixed
fiber is changed along the supplied iso; no bundle gluing, descent, chart,
or model claim is made. -/
noncomputable def mapFiber {G : C} {p : E ⟶ B} (e : F ≅ G)
    (h : TrivialBundleWithFiber G p) :
    TrivialBundleWithFiber F p where
  r := h.r ≫ e.inv
  isLimit := by
    refine BinaryFan.isLimitMk
      (fun s => BinaryFan.IsLimit.lift h.isLimit s.fst (s.snd ≫ e.hom)) ?_ ?_ ?_
    · intro s
      exact BinaryFan.IsLimit.lift_fst _ _ _
    · intro s
      have hSnd : BinaryFan.IsLimit.lift h.isLimit s.fst (s.snd ≫ e.hom) ≫ h.r =
        s.snd ≫ e.hom := BinaryFan.IsLimit.lift_snd _ _ _
      have hAssoc : BinaryFan.IsLimit.lift h.isLimit s.fst (s.snd ≫ e.hom) ≫
        (h.r ≫ e.inv) =
        (BinaryFan.IsLimit.lift h.isLimit s.fst (s.snd ≫ e.hom) ≫ h.r) ≫ e.inv :=
        (Category.assoc _ _ _).symm
      have hInv : (s.snd ≫ e.hom) ≫ e.inv = s.snd := by
        rw [Category.assoc, e.hom_inv_id]
        exact Category.comp_id _
      exact Eq.trans hAssoc (Eq.trans (congrArg (· ≫ e.inv) hSnd) hInv)
    · intro s m hm₁ hm₂
      have hM : m ≫ h.r = s.snd ≫ e.hom := by
        have hE : (m ≫ (h.r ≫ e.inv)) ≫ e.hom = m ≫ h.r := by
          calc (m ≫ (h.r ≫ e.inv)) ≫ e.hom
              = m ≫ ((h.r ≫ e.inv) ≫ e.hom) := by rw [Category.assoc]
            _ = m ≫ (h.r ≫ (e.inv ≫ e.hom)) := by rw [Category.assoc]
            _ = m ≫ (h.r ≫ 𝟙 _) := by rw [Iso.inv_hom_id]
            _ = m ≫ h.r := by rw [Category.comp_id]
        exact Eq.trans hE.symm (congrArg (· ≫ e.hom) hm₂)
      apply BinaryFan.IsLimit.hom_ext h.isLimit
      · have hL : BinaryFan.IsLimit.lift h.isLimit s.fst (s.snd ≫ e.hom) ≫ p =
          s.fst := BinaryFan.IsLimit.lift_fst _ _ _
        exact hm₁.trans hL.symm
      · have hL : BinaryFan.IsLimit.lift h.isLimit s.fst (s.snd ≫ e.hom) ≫ h.r =
          s.snd ≫ e.hom := BinaryFan.IsLimit.lift_snd _ _ _
        exact hM.trans hL.symm

end TrivialBundleWithFiber

end CategoryTheory
