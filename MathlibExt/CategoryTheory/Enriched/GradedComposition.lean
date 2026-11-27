/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Tensor composition and change of central grade

The data is computed from the complete original enriched Hom maps and the
actual half-braidings in Center V. A and B remain plain enriched types.
No braiding or closedness of V, ordinary source category, size, or model
assumption is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uB uV vV

namespace CategoryTheory.GradedNatTrans

open MonoidalCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

private theorem componentTensor_assoc
    {b₀ b₁ b₂ b₃ : B} {X Y Z : V}
    (f : X ⟶ (b₀ ⟶[V] b₁)) (g : Y ⟶ (b₁ ⟶[V] b₂))
    (h : Z ⟶ (b₂ ⟶[V] b₃)) :
    (((f ⊗ₘ g) ≫ eComp V b₀ b₁ b₂) ⊗ₘ h) ≫ eComp V b₀ b₂ b₃ =
      (α_ X Y Z).hom ≫
        (f ⊗ₘ ((g ⊗ₘ h) ≫ eComp V b₁ b₂ b₃)) ≫ eComp V b₀ b₁ b₃ := by
  have hIn :
      ((f ⊗ₘ g) ≫ eComp V b₀ b₁ b₂) ⊗ₘ h =
        ((f ⊗ₘ g) ⊗ₘ h) ≫ (eComp V b₀ b₁ b₂ ▷ (b₂ ⟶[V] b₃)) := by
    simpa only [tensorHom_id, Category.comp_id] using
      (tensorHom_comp_tensorHom (f ⊗ₘ g) h
        (eComp V b₀ b₁ b₂) (𝟙 (b₂ ⟶[V] b₃))).symm
  have hOut :
      (f ⊗ₘ (g ⊗ₘ h)) ≫ (b₀ ⟶[V] b₁) ◁ eComp V b₁ b₂ b₃ =
        f ⊗ₘ ((g ⊗ₘ h) ≫ eComp V b₁ b₂ b₃) := by
    simpa only [id_tensorHom, Category.comp_id] using
      (tensorHom_comp_tensorHom f (g ⊗ₘ h)
        (𝟙 (b₀ ⟶[V] b₁)) (eComp V b₁ b₂ b₃))
  calc
    _ = ((f ⊗ₘ g) ⊗ₘ h) ≫
        (eComp V b₀ b₁ b₂ ▷ (b₂ ⟶[V] b₃)) ≫ eComp V b₀ b₂ b₃ := by
      simpa only [Category.assoc] using congrArg
        (fun q : (X ⊗ Y) ⊗ Z ⟶ (b₀ ⟶[V] b₂) ⊗ (b₂ ⟶[V] b₃) =>
          q ≫ eComp V b₀ b₂ b₃) hIn
    _ = ((f ⊗ₘ g) ⊗ₘ h) ≫
        (α_ (b₀ ⟶[V] b₁) (b₁ ⟶[V] b₂) (b₂ ⟶[V] b₃)).hom ≫
        (b₀ ⟶[V] b₁) ◁ eComp V b₁ b₂ b₃ ≫ eComp V b₀ b₁ b₃ := by
      simpa only [Category.assoc] using congrArg
        (fun q : ((b₀ ⟶[V] b₁) ⊗ (b₁ ⟶[V] b₂)) ⊗
            (b₂ ⟶[V] b₃) ⟶ (b₀ ⟶[V] b₃) =>
          ((f ⊗ₘ g) ⊗ₘ h) ≫ q) (e_assoc' V b₀ b₁ b₂ b₃).symm
    _ = (α_ X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) ≫
        (b₀ ⟶[V] b₁) ◁ eComp V b₁ b₂ b₃ ≫ eComp V b₀ b₁ b₃ := by
      simpa only [Category.assoc] using congrArg
        (fun q : (X ⊗ Y) ⊗ Z ⟶ (b₀ ⟶[V] b₁) ⊗
            ((b₁ ⟶[V] b₂) ⊗ (b₂ ⟶[V] b₃)) =>
          q ≫ (b₀ ⟶[V] b₁) ◁ eComp V b₁ b₂ b₃ ≫ eComp V b₀ b₁ b₃)
        (associator_naturality f g h)
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun q : X ⊗ (Y ⊗ Z) ⟶ (b₀ ⟶[V] b₁) ⊗ (b₁ ⟶[V] b₃) =>
          (α_ X Y Z).hom ≫ q ≫ eComp V b₀ b₁ b₃) hOut

variable {F G H : EnrichedFunctor V A B} {Z W : Center V}

/-- The actual tensor-composed components satisfy full central naturality. -/
theorem tensorComp_naturality
    (f : GradedNatTrans Z F G) (g : GradedNatTrans W G H) (a b : A) :
    ((Z ⊗ W).2.β (a ⟶[V] b)).hom ≫
        (F.map a b ⊗ₘ ((f.app b ⊗ₘ g.app b) ≫
          eComp V (F.obj b) (G.obj b) (H.obj b))) ≫
        eComp V (F.obj a) (F.obj b) (H.obj b) =
      (((f.app a ⊗ₘ g.app a) ≫ eComp V (F.obj a) (G.obj a) (H.obj a)) ⊗ₘ
        H.map a b) ≫ eComp V (F.obj a) (H.obj a) (H.obj b) := by
  let P : V := a ⟶[V] b
  let n : (Z.1 ⊗ W.1) ⊗ P ⟶ (Z.1 ⊗ P) ⊗ W.1 :=
    (α_ Z.1 W.1 P).hom ≫ Z.1 ◁ (W.2.β P).hom ≫ (α_ Z.1 P W.1).inv
  let s : (Z.1 ⊗ W.1) ⊗ P ⟶ (P ⊗ Z.1) ⊗ W.1 :=
    n ≫ ((Z.2.β P).hom ▷ W.1)
  have hCenter :
      ((Z ⊗ W).2.β P).hom = s ≫ (α_ P Z.1 W.1).hom := by
    simpa only [s, n, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom, Category.assoc] using
      congrArg Iso.hom (Center.tensor_β Z W P)
  have hFirst := componentTensor_assoc (V := V)
    (F.map a b) (f.app b) (g.app b)
  have hFCombine :
      ((Z.2.β P).hom ▷ W.1) ≫
          (((F.map a b ⊗ₘ f.app b) ≫
            eComp V (F.obj a) (F.obj b) (G.obj b)) ⊗ₘ g.app b) =
        (((Z.2.β P).hom ≫ (F.map a b ⊗ₘ f.app b) ≫
          eComp V (F.obj a) (F.obj b) (G.obj b)) ⊗ₘ g.app b) := by
    simpa only [tensorHom_id, Category.id_comp, Category.assoc] using
      (tensorHom_comp_tensorHom (Z.2.β P).hom (𝟙 W.1)
        ((F.map a b ⊗ₘ f.app b) ≫ eComp V (F.obj a) (F.obj b) (G.obj b))
        (g.app b))
  have hFNat :
      (((Z.2.β P).hom ≫ (F.map a b ⊗ₘ f.app b) ≫
          eComp V (F.obj a) (F.obj b) (G.obj b)) ⊗ₘ g.app b) =
        (((f.app a ⊗ₘ G.map a b) ≫
          eComp V (F.obj a) (G.obj a) (G.obj b)) ⊗ₘ g.app b) :=
    congrArg (fun q : Z.1 ⊗ P ⟶ (F.obj a ⟶[V] G.obj b) =>
      q ⊗ₘ g.app b) (f.naturality a b)
  have hMiddle := componentTensor_assoc (V := V)
    (f.app a) (G.map a b) (g.app b)
  have hGCombine :
      (Z.1 ◁ (W.2.β P).hom) ≫
          (f.app a ⊗ₘ ((G.map a b ⊗ₘ g.app b) ≫
            eComp V (G.obj a) (G.obj b) (H.obj b))) =
        f.app a ⊗ₘ ((W.2.β P).hom ≫
          (G.map a b ⊗ₘ g.app b) ≫ eComp V (G.obj a) (G.obj b) (H.obj b)) := by
    simpa only [id_tensorHom, Category.id_comp, Category.assoc] using
      (tensorHom_comp_tensorHom (𝟙 Z.1) (W.2.β P).hom (f.app a)
        ((G.map a b ⊗ₘ g.app b) ≫ eComp V (G.obj a) (G.obj b) (H.obj b)))
  have hGNat :
      f.app a ⊗ₘ ((W.2.β P).hom ≫
          (G.map a b ⊗ₘ g.app b) ≫ eComp V (G.obj a) (G.obj b) (H.obj b)) =
        f.app a ⊗ₘ ((g.app a ⊗ₘ H.map a b) ≫
          eComp V (G.obj a) (H.obj a) (H.obj b)) :=
    congrArg (fun q : W.1 ⊗ P ⟶ (G.obj a ⟶[V] H.obj b) =>
      f.app a ⊗ₘ q) (g.naturality a b)
  have hLast := componentTensor_assoc (V := V)
    (f.app a) (g.app a) (H.map a b)
  calc
    _ = s ≫ (α_ P Z.1 W.1).hom ≫
        (F.map a b ⊗ₘ ((f.app b ⊗ₘ g.app b) ≫
          eComp V (F.obj b) (G.obj b) (H.obj b))) ≫
        eComp V (F.obj a) (F.obj b) (H.obj b) := by
      exact (congrArg
        (fun q : (Z.1 ⊗ W.1) ⊗ P ⟶ P ⊗ (Z.1 ⊗ W.1) =>
          q ≫ (F.map a b ⊗ₘ ((f.app b ⊗ₘ g.app b) ≫
            eComp V (F.obj b) (G.obj b) (H.obj b))) ≫
            eComp V (F.obj a) (F.obj b) (H.obj b)) hCenter).trans
        (Category.assoc s (α_ P Z.1 W.1).hom
          ((F.map a b ⊗ₘ ((f.app b ⊗ₘ g.app b) ≫
            eComp V (F.obj b) (G.obj b) (H.obj b))) ≫
            eComp V (F.obj a) (F.obj b) (H.obj b)))
    _ = s ≫
        (((F.map a b ⊗ₘ f.app b) ≫
          eComp V (F.obj a) (F.obj b) (G.obj b)) ⊗ₘ g.app b) ≫
        eComp V (F.obj a) (G.obj b) (H.obj b) := by
      simpa only [P, Category.assoc] using congrArg
        (fun q : (P ⊗ Z.1) ⊗ W.1 ⟶ (F.obj a ⟶[V] H.obj b) =>
          s ≫ q) hFirst.symm
    _ = n ≫
        (((f.app a ⊗ₘ G.map a b) ≫
          eComp V (F.obj a) (G.obj a) (G.obj b)) ⊗ₘ g.app b) ≫
        eComp V (F.obj a) (G.obj b) (H.obj b) := by
      simpa only [s, Category.assoc] using congrArg
        (fun q : (Z.1 ⊗ P) ⊗ W.1 ⟶
            (F.obj a ⟶[V] G.obj b) ⊗ (G.obj b ⟶[V] H.obj b) =>
          n ≫ q ≫ eComp V (F.obj a) (G.obj b) (H.obj b))
        (hFCombine.trans hFNat)
    _ = (α_ Z.1 W.1 P).hom ≫ Z.1 ◁ (W.2.β P).hom ≫
        (f.app a ⊗ₘ ((G.map a b ⊗ₘ g.app b) ≫
          eComp V (G.obj a) (G.obj b) (H.obj b))) ≫
        eComp V (F.obj a) (G.obj a) (H.obj b) := by
      simpa only [n, P, Category.assoc, Iso.inv_hom_id_assoc] using congrArg
        (fun q : (Z.1 ⊗ P) ⊗ W.1 ⟶ (F.obj a ⟶[V] H.obj b) =>
          n ≫ q) hMiddle
    _ = (α_ Z.1 W.1 P).hom ≫
        (f.app a ⊗ₘ ((g.app a ⊗ₘ H.map a b) ≫
          eComp V (G.obj a) (H.obj a) (H.obj b))) ≫
        eComp V (F.obj a) (G.obj a) (H.obj b) := by
      simpa only [Category.assoc] using congrArg
        (fun q : Z.1 ⊗ (W.1 ⊗ P) ⟶
            (F.obj a ⟶[V] G.obj a) ⊗ (G.obj a ⟶[V] H.obj b) =>
          (α_ Z.1 W.1 P).hom ≫ q ≫ eComp V (F.obj a) (G.obj a) (H.obj b))
        (hGCombine.trans hGNat)
    _ = _ := by
      simpa only [P] using hLast.symm

/-- Compose the actual transformations in source-first central tensor grade. -/
def tensorComp (f : GradedNatTrans Z F G) (g : GradedNatTrans W G H) :
    GradedNatTrans (Z ⊗ W) F H where
  app a := (f.app a ⊗ₘ g.app a) ≫ eComp V (F.obj a) (G.obj a) (H.obj a)
  naturality a b := tensorComp_naturality f g a b

/-- All component data are the original tensor of Hom maps followed by eComp. -/
theorem tensorComp_app (f : GradedNatTrans Z F G) (g : GradedNatTrans W G H) (a : A) :
    (tensorComp f g).app a =
      (f.app a ⊗ₘ g.app a) ≫ eComp V (F.obj a) (G.obj a) (H.obj a) := rfl

/-- Restrict an actual transformation along a genuine morphism in the center. -/
def regrade {Z' : Center V} (u : Z ⟶ Z') (t : GradedNatTrans Z' F G) :
    GradedNatTrans Z F G where
  app a := u.f ≫ t.app a
  naturality a b := by
    let P : V := a ⟶[V] b
    have hTensorPre :
        (P ◁ u.f) ≫ (F.map a b ⊗ₘ t.app b) =
          F.map a b ⊗ₘ (u.f ≫ t.app b) := by
      simpa only [id_tensorHom, Category.id_comp] using
        (tensorHom_comp_tensorHom (𝟙 P) u.f (F.map a b) (t.app b))
    have hTensorPost :
        (u.f ▷ P) ≫ (t.app a ⊗ₘ G.map a b) =
          (u.f ≫ t.app a) ⊗ₘ G.map a b := by
      simpa only [tensorHom_id, Category.id_comp] using
        (tensorHom_comp_tensorHom u.f (𝟙 P) (t.app a) (G.map a b))
    calc
      _ = (Z.2.β P).hom ≫ (P ◁ u.f) ≫
          (F.map a b ⊗ₘ t.app b) ≫ eComp V (F.obj a) (F.obj b) (G.obj b) := by
        simpa only [P, Category.assoc] using congrArg
          (fun q : P ⊗ Z.1 ⟶
              (F.obj a ⟶[V] F.obj b) ⊗ (F.obj b ⟶[V] G.obj b) =>
            (Z.2.β P).hom ≫ q ≫ eComp V (F.obj a) (F.obj b) (G.obj b))
          hTensorPre.symm
      _ = (u.f ▷ P) ≫ (Z'.2.β P).hom ≫
          (F.map a b ⊗ₘ t.app b) ≫ eComp V (F.obj a) (F.obj b) (G.obj b) := by
        simpa only [Category.assoc] using congrArg
          (fun q : Z.1 ⊗ P ⟶ P ⊗ Z'.1 =>
            q ≫ (F.map a b ⊗ₘ t.app b) ≫ eComp V (F.obj a) (F.obj b) (G.obj b))
          (u.comm P).symm
      _ = (u.f ▷ P) ≫ (t.app a ⊗ₘ G.map a b) ≫
          eComp V (F.obj a) (G.obj a) (G.obj b) := by
        simpa only [Category.assoc] using congrArg
          (fun q : Z'.1 ⊗ P ⟶ (F.obj a ⟶[V] G.obj b) =>
            (u.f ▷ P) ≫ q) (t.naturality a b)
      _ = _ := by
        simpa only [P, Category.assoc] using congrArg
          (fun q : Z.1 ⊗ P ⟶
              (F.obj a ⟶[V] G.obj a) ⊗ (G.obj a ⟶[V] G.obj b) =>
            q ≫ eComp V (F.obj a) (G.obj a) (G.obj b)) hTensorPost

/-- A change of central grade preserves the exact original component maps. -/
theorem regrade_app {Z' : Center V} (u : Z ⟶ Z') (t : GradedNatTrans Z' F G) (a : A) :
    (regrade u t).app a = u.f ≫ t.app a := rfl

end CategoryTheory.GradedNatTrans
