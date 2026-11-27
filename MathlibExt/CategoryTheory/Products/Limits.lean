/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Product-category zero objects and pushout/pullback squares

For categories `C` and `D` with independent universes, the product `C × D`
carries a componentwise zero object and componentwise pushout/pullback
squares, with no preadditive, exact, or Waldhausen hypotheses. The zero
instance is the pair of chosen zero objects; an object is zero iff both
projections are zero; a square is a pushout (resp. pullback) iff both
projections are. Pushout/pullback statements cover arbitrary product
morphisms via `Prod.hom_ext` and `Prod.mkHom`, not only syntactic
`Prod.mkHom` expressions.

Nonclaims: no preadditive or exact structure, no biproducts, no Waldhausen
structure, no compatibility wrappers, no additivity, no K/G-theory, no
realization, no spectra, no Q/S comparison.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/-- The pair of chosen zero objects is zero for the product. -/
instance prodHasZeroObject [HasZeroObject C] [HasZeroObject D] :
    HasZeroObject (C × D) where
  zero := by
    obtain ⟨Zc, hZc⟩ : ∃ X : C, IsZero X := HasZeroObject.zero
    obtain ⟨Zd, hZd⟩ : ∃ X : D, IsZero X := HasZeroObject.zero
    refine ⟨(Zc, Zd), ⟨?_, ?_⟩⟩
    · intro Y
      exact ⟨⟨⟨(hZc.to_ Y.1, hZd.to_ Y.2)⟩,
        fun f => Prod.hom_ext (hZc.eq_to _) (hZd.eq_to _)⟩⟩
    · intro Y
      exact ⟨⟨⟨(hZc.from_ Y.1, hZd.from_ Y.2)⟩,
        fun f => Prod.hom_ext (hZc.eq_from _) (hZd.eq_from _)⟩⟩

/-- An object in a product is zero iff both projections are zero. -/
@[simp]
theorem isZero_prod_iff {X : C × D} :
    IsZero X ↔ IsZero X.1 ∧ IsZero X.2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact
        { unique_to := fun Y =>
            ⟨⟨⟨(h.to_ (Y, X.2)).1⟩,
              fun f => congrArg (fun m => m.1)
                (h.eq_to (Prod.mkHom f (𝟙 X.2)))⟩⟩,
          unique_from := fun Y =>
            ⟨⟨⟨(h.from_ (Y, X.2)).1⟩,
              fun f => congrArg (fun m => m.1)
                (h.eq_from (Prod.mkHom f (𝟙 X.2)))⟩⟩ }
    · exact
        { unique_to := fun Y =>
            ⟨⟨⟨(h.to_ (X.1, Y)).2⟩,
              fun f => congrArg (fun m => m.2)
                (h.eq_to (Prod.mkHom (𝟙 X.1) f))⟩⟩,
          unique_from := fun Y =>
            ⟨⟨⟨(h.from_ (X.1, Y)).2⟩,
              fun f => congrArg (fun m => m.2)
                (h.eq_from (Prod.mkHom (𝟙 X.1) f))⟩⟩ }
  · rintro ⟨h1, h2⟩
    refine ⟨fun Y => ⟨⟨⟨(h1.to_ Y.1, h2.to_ Y.2)⟩, ?_⟩⟩,
      fun Y => ⟨⟨⟨(h1.from_ Y.1, h2.from_ Y.2)⟩, ?_⟩⟩⟩
    · intro f
      exact Prod.hom_ext (h1.eq_to _) (h2.eq_to _)
    · intro f
      exact Prod.hom_ext (h1.eq_from _) (h2.eq_from _)

/-- A square in a product is a pushout iff both projections are pushouts. -/
theorem isPushout_prod_iff {Z X Y P : C × D} {f : Z ⟶ X}
    {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPushout f g inl inr ↔
      IsPushout f.1 g.1 inl.1 inr.1 ∧
        IsPushout f.2 g.2 inl.2 inr.2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact
        { w := by simpa using congrArg (fun m => m.1) h.w
          isColimit' :=
            ⟨PushoutCocone.IsColimit.mk _ (fun s =>
                let h1 := Prod.mkHom s.inl inl.2
                let k1 := Prod.mkHom s.inr inr.2
                let w1 : f ≫ h1 = g ≫ k1 := Prod.hom_ext s.condition
                  (by simpa using congrArg (fun m => m.2) h.w)
                (h.desc h1 k1 w1).1)
              (fun s =>
                let h1 := Prod.mkHom s.inl inl.2
                let k1 := Prod.mkHom s.inr inr.2
                let w1 : f ≫ h1 = g ≫ k1 := Prod.hom_ext s.condition
                  (by simpa using congrArg (fun m => m.2) h.w)
                congrArg (fun m => m.1) (h.inl_desc h1 k1 w1))
              (fun s =>
                let h1 := Prod.mkHom s.inl inl.2
                let k1 := Prod.mkHom s.inr inr.2
                let w1 : f ≫ h1 = g ≫ k1 := Prod.hom_ext s.condition
                  (by simpa using congrArg (fun m => m.2) h.w)
                congrArg (fun m => m.1) (h.inr_desc h1 k1 w1))
              (fun s m hm₁ hm₂ => by
                have hEq :
                    (inl ≫ Prod.mkHom m (𝟙 P.2)) =
                      Prod.mkHom s.inl inl.2 :=
                  Prod.hom_ext (by simpa using hm₁) (by simp)
                have hEq2 :
                    (inr ≫ Prod.mkHom m (𝟙 P.2)) =
                      Prod.mkHom s.inr inr.2 :=
                  Prod.hom_ext (by simpa using hm₂) (by simp)
                have w1 :
                    f ≫ Prod.mkHom s.inl inl.2 =
                      g ≫ Prod.mkHom s.inr inr.2 :=
                  Prod.hom_ext s.condition
                    (by simpa using congrArg (fun m => m.2) h.w)
                have hDescEq :
                    inl ≫ h.desc (Prod.mkHom s.inl inl.2)
                      (Prod.mkHom s.inr inr.2) w1 =
                      Prod.mkHom s.inl inl.2 :=
                  h.inl_desc _ _ _
                have hDescEq2 :
                    inr ≫ h.desc (Prod.mkHom s.inl inl.2)
                      (Prod.mkHom s.inr inr.2) w1 =
                      Prod.mkHom s.inr inr.2 :=
                  h.inr_desc _ _ _
                have hUniq :
                    Prod.mkHom m (𝟙 P.2) =
                      h.desc (Prod.mkHom s.inl inl.2)
                        (Prod.mkHom s.inr inr.2) w1 :=
                  h.hom_ext (hEq.trans hDescEq.symm)
                    (hEq2.trans hDescEq2.symm)
                exact congrArg (fun m => m.1) hUniq)⟩ }
    · exact
        { w := by simpa using congrArg (fun m => m.2) h.w
          isColimit' :=
            ⟨PushoutCocone.IsColimit.mk _ (fun s =>
                let h1 := Prod.mkHom inl.1 s.inl
                let k1 := Prod.mkHom inr.1 s.inr
                let w1 : f ≫ h1 = g ≫ k1 := Prod.hom_ext
                  (by simpa using congrArg (fun m => m.1) h.w)
                  s.condition
                (h.desc h1 k1 w1).2)
              (fun s =>
                let h1 := Prod.mkHom inl.1 s.inl
                let k1 := Prod.mkHom inr.1 s.inr
                let w1 : f ≫ h1 = g ≫ k1 := Prod.hom_ext
                  (by simpa using congrArg (fun m => m.1) h.w)
                  s.condition
                congrArg (fun m => m.2) (h.inl_desc h1 k1 w1))
              (fun s =>
                let h1 := Prod.mkHom inl.1 s.inl
                let k1 := Prod.mkHom inr.1 s.inr
                let w1 : f ≫ h1 = g ≫ k1 := Prod.hom_ext
                  (by simpa using congrArg (fun m => m.1) h.w)
                  s.condition
                congrArg (fun m => m.2) (h.inr_desc h1 k1 w1))
              (fun s m hm₁ hm₂ => by
                have hEq :
                    (inl ≫ Prod.mkHom (𝟙 P.1) m) =
                      Prod.mkHom inl.1 s.inl :=
                  Prod.hom_ext (by simp) (by simpa using hm₁)
                have hEq2 :
                    (inr ≫ Prod.mkHom (𝟙 P.1) m) =
                      Prod.mkHom inr.1 s.inr :=
                  Prod.hom_ext (by simp) (by simpa using hm₂)
                have w1 :
                    f ≫ Prod.mkHom inl.1 s.inl =
                      g ≫ Prod.mkHom inr.1 s.inr :=
                  Prod.hom_ext
                    (by simpa using congrArg (fun m => m.1) h.w)
                    s.condition
                have hDescEq :
                    inl ≫ h.desc (Prod.mkHom inl.1 s.inl)
                      (Prod.mkHom inr.1 s.inr) w1 =
                      Prod.mkHom inl.1 s.inl :=
                  h.inl_desc _ _ _
                have hDescEq2 :
                    inr ≫ h.desc (Prod.mkHom inl.1 s.inl)
                      (Prod.mkHom inr.1 s.inr) w1 =
                      Prod.mkHom inr.1 s.inr :=
                  h.inr_desc _ _ _
                have hUniq :
                    Prod.mkHom (𝟙 P.1) m =
                      h.desc (Prod.mkHom inl.1 s.inl)
                        (Prod.mkHom inr.1 s.inr) w1 :=
                  h.hom_ext (hEq.trans hDescEq.symm)
                    (hEq2.trans hDescEq2.symm)
                exact congrArg (fun m => m.2) hUniq)⟩ }
  · rintro ⟨h1, h2⟩
    exact
      { w := Prod.hom_ext h1.w h2.w
        isColimit' :=
          ⟨PushoutCocone.IsColimit.mk _ (fun s =>
              let w1 : f.1 ≫ s.inl.1 = g.1 ≫ s.inr.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              let w2 : f.2 ≫ s.inl.2 = g.2 ≫ s.inr.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              Prod.mkHom (h1.desc s.inl.1 s.inr.1 w1)
                (h2.desc s.inl.2 s.inr.2 w2))
            (fun s =>
              let w1 : f.1 ≫ s.inl.1 = g.1 ≫ s.inr.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              let w2 : f.2 ≫ s.inl.2 = g.2 ≫ s.inr.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              Prod.hom_ext (h1.inl_desc s.inl.1 s.inr.1 w1)
                (h2.inl_desc s.inl.2 s.inr.2 w2))
            (fun s =>
              let w1 : f.1 ≫ s.inl.1 = g.1 ≫ s.inr.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              let w2 : f.2 ≫ s.inl.2 = g.2 ≫ s.inr.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              Prod.hom_ext (h1.inr_desc s.inl.1 s.inr.1 w1)
                (h2.inr_desc s.inl.2 s.inr.2 w2))
            (fun s m hm₁ hm₂ => by
              have e1 : inl.1 ≫ m.1 = s.inl.1 :=
                congrArg (fun m => m.1) hm₁
              have e2 : inl.2 ≫ m.2 = s.inl.2 :=
                congrArg (fun m => m.2) hm₁
              have e3 : inr.1 ≫ m.1 = s.inr.1 :=
                congrArg (fun m => m.1) hm₂
              have e4 : inr.2 ≫ m.2 = s.inr.2 :=
                congrArg (fun m => m.2) hm₂
              have w1 : f.1 ≫ s.inl.1 = g.1 ≫ s.inr.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              have w2 : f.2 ≫ s.inl.2 = g.2 ≫ s.inr.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              have u1 : m.1 = h1.desc s.inl.1 s.inr.1 w1 :=
                h1.hom_ext
                  (e1.trans (h1.inl_desc s.inl.1 s.inr.1 w1).symm)
                  (e3.trans (h1.inr_desc s.inl.1 s.inr.1 w1).symm)
              have u2 : m.2 = h2.desc s.inl.2 s.inr.2 w2 :=
                h2.hom_ext
                  (e2.trans (h2.inl_desc s.inl.2 s.inr.2 w2).symm)
                  (e4.trans (h2.inr_desc s.inl.2 s.inr.2 w2).symm)
              exact Prod.hom_ext u1 u2)⟩ }

/-- A square in a product is a pullback iff both projections are pullbacks. -/
theorem isPullback_prod_iff {P X Y Z : C × D} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g ↔
      IsPullback fst.1 snd.1 f.1 g.1 ∧
        IsPullback fst.2 snd.2 f.2 g.2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact
        { w := by simpa using congrArg (fun m => m.1) h.w
          isLimit' :=
            ⟨PullbackCone.IsLimit.mk _ (fun s =>
                let h1 := Prod.mkHom s.fst fst.2
                let k1 := Prod.mkHom s.snd snd.2
                let w1 : h1 ≫ f = k1 ≫ g := Prod.hom_ext s.condition
                  (by simpa using congrArg (fun m => m.2) h.w)
                (h.lift h1 k1 w1).1)
              (fun s =>
                let h1 := Prod.mkHom s.fst fst.2
                let k1 := Prod.mkHom s.snd snd.2
                let w1 : h1 ≫ f = k1 ≫ g := Prod.hom_ext s.condition
                  (by simpa using congrArg (fun m => m.2) h.w)
                congrArg (fun m => m.1) (h.lift_fst h1 k1 w1))
              (fun s =>
                let h1 := Prod.mkHom s.fst fst.2
                let k1 := Prod.mkHom s.snd snd.2
                let w1 : h1 ≫ f = k1 ≫ g := Prod.hom_ext s.condition
                  (by simpa using congrArg (fun m => m.2) h.w)
                congrArg (fun m => m.1) (h.lift_snd h1 k1 w1))
              (fun s m hm₁ hm₂ => by
                have hEq :
                    (Prod.mkHom m (𝟙 P.2) ≫ fst) =
                      Prod.mkHom s.fst fst.2 :=
                  Prod.hom_ext (by simpa using hm₁) (by simp)
                have hEq2 :
                    (Prod.mkHom m (𝟙 P.2) ≫ snd) =
                      Prod.mkHom s.snd snd.2 :=
                  Prod.hom_ext (by simpa using hm₂) (by simp)
                have w1 :
                    Prod.mkHom s.fst fst.2 ≫ f =
                      Prod.mkHom s.snd snd.2 ≫ g :=
                  Prod.hom_ext s.condition
                    (by simpa using congrArg (fun m => m.2) h.w)
                have hLiftEq :
                    h.lift (Prod.mkHom s.fst fst.2)
                      (Prod.mkHom s.snd snd.2) w1 ≫ fst =
                      Prod.mkHom s.fst fst.2 :=
                  h.lift_fst _ _ _
                have hLiftEq2 :
                    h.lift (Prod.mkHom s.fst fst.2)
                      (Prod.mkHom s.snd snd.2) w1 ≫ snd =
                      Prod.mkHom s.snd snd.2 :=
                  h.lift_snd _ _ _
                have hUniq :
                    Prod.mkHom m (𝟙 P.2) =
                      h.lift (Prod.mkHom s.fst fst.2)
                        (Prod.mkHom s.snd snd.2) w1 :=
                  h.hom_ext (hEq.trans hLiftEq.symm)
                    (hEq2.trans hLiftEq2.symm)
                exact congrArg (fun m => m.1) hUniq)⟩ }
    · exact
        { w := by simpa using congrArg (fun m => m.2) h.w
          isLimit' :=
            ⟨PullbackCone.IsLimit.mk _ (fun s =>
                let h1 := Prod.mkHom fst.1 s.fst
                let k1 := Prod.mkHom snd.1 s.snd
                let w1 : h1 ≫ f = k1 ≫ g := Prod.hom_ext
                  (by simpa using congrArg (fun m => m.1) h.w)
                  s.condition
                (h.lift h1 k1 w1).2)
              (fun s =>
                let h1 := Prod.mkHom fst.1 s.fst
                let k1 := Prod.mkHom snd.1 s.snd
                let w1 : h1 ≫ f = k1 ≫ g := Prod.hom_ext
                  (by simpa using congrArg (fun m => m.1) h.w)
                  s.condition
                congrArg (fun m => m.2) (h.lift_fst h1 k1 w1))
              (fun s =>
                let h1 := Prod.mkHom fst.1 s.fst
                let k1 := Prod.mkHom snd.1 s.snd
                let w1 : h1 ≫ f = k1 ≫ g := Prod.hom_ext
                  (by simpa using congrArg (fun m => m.1) h.w)
                  s.condition
                congrArg (fun m => m.2) (h.lift_snd h1 k1 w1))
              (fun s m hm₁ hm₂ => by
                have hEq :
                    (Prod.mkHom (𝟙 P.1) m ≫ fst) =
                      Prod.mkHom fst.1 s.fst :=
                  Prod.hom_ext (by simp) (by simpa using hm₁)
                have hEq2 :
                    (Prod.mkHom (𝟙 P.1) m ≫ snd) =
                      Prod.mkHom snd.1 s.snd :=
                  Prod.hom_ext (by simp) (by simpa using hm₂)
                have w1 :
                    Prod.mkHom fst.1 s.fst ≫ f =
                      Prod.mkHom snd.1 s.snd ≫ g :=
                  Prod.hom_ext
                    (by simpa using congrArg (fun m => m.1) h.w)
                    s.condition
                have hLiftEq :
                    h.lift (Prod.mkHom fst.1 s.fst)
                      (Prod.mkHom snd.1 s.snd) w1 ≫ fst =
                      Prod.mkHom fst.1 s.fst :=
                  h.lift_fst _ _ _
                have hLiftEq2 :
                    h.lift (Prod.mkHom fst.1 s.fst)
                      (Prod.mkHom snd.1 s.snd) w1 ≫ snd =
                      Prod.mkHom snd.1 s.snd :=
                  h.lift_snd _ _ _
                have hUniq :
                    Prod.mkHom (𝟙 P.1) m =
                      h.lift (Prod.mkHom fst.1 s.fst)
                        (Prod.mkHom snd.1 s.snd) w1 :=
                  h.hom_ext (hEq.trans hLiftEq.symm)
                    (hEq2.trans hLiftEq2.symm)
                exact congrArg (fun m => m.2) hUniq)⟩ }
  · rintro ⟨h1, h2⟩
    exact
      { w := Prod.hom_ext h1.w h2.w
        isLimit' :=
          ⟨PullbackCone.IsLimit.mk _ (fun s =>
              let w1 : s.fst.1 ≫ f.1 = s.snd.1 ≫ g.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              let w2 : s.fst.2 ≫ f.2 = s.snd.2 ≫ g.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              Prod.mkHom (h1.lift s.fst.1 s.snd.1 w1)
                (h2.lift s.fst.2 s.snd.2 w2))
            (fun s =>
              let w1 : s.fst.1 ≫ f.1 = s.snd.1 ≫ g.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              let w2 : s.fst.2 ≫ f.2 = s.snd.2 ≫ g.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              Prod.hom_ext (h1.lift_fst s.fst.1 s.snd.1 w1)
                (h2.lift_fst s.fst.2 s.snd.2 w2))
            (fun s =>
              let w1 : s.fst.1 ≫ f.1 = s.snd.1 ≫ g.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              let w2 : s.fst.2 ≫ f.2 = s.snd.2 ≫ g.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              Prod.hom_ext (h1.lift_snd s.fst.1 s.snd.1 w1)
                (h2.lift_snd s.fst.2 s.snd.2 w2))
            (fun s m hm₁ hm₂ => by
              have e1 : m.1 ≫ fst.1 = s.fst.1 :=
                congrArg (fun m => m.1) hm₁
              have e2 : m.2 ≫ fst.2 = s.fst.2 :=
                congrArg (fun m => m.2) hm₁
              have e3 : m.1 ≫ snd.1 = s.snd.1 :=
                congrArg (fun m => m.1) hm₂
              have e4 : m.2 ≫ snd.2 = s.snd.2 :=
                congrArg (fun m => m.2) hm₂
              have w1 : s.fst.1 ≫ f.1 = s.snd.1 ≫ g.1 := by
                simpa using congrArg (fun m => m.1) s.condition
              have w2 : s.fst.2 ≫ f.2 = s.snd.2 ≫ g.2 := by
                simpa using congrArg (fun m => m.2) s.condition
              have u1 : m.1 = h1.lift s.fst.1 s.snd.1 w1 :=
                h1.hom_ext
                  (e1.trans (h1.lift_fst s.fst.1 s.snd.1 w1).symm)
                  (e3.trans (h1.lift_snd s.fst.1 s.snd.1 w1).symm)
              have u2 : m.2 = h2.lift s.fst.2 s.snd.2 w2 :=
                h2.hom_ext
                  (e2.trans (h2.lift_fst s.fst.2 s.snd.2 w2).symm)
                  (e4.trans (h2.lift_snd s.fst.2 s.snd.2 w2).symm)
              exact Prod.hom_ext u1 u2)⟩ }

end CategoryTheory
