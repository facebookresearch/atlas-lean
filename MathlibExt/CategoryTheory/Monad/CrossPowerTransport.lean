/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Monad.Coresolution

/-! # Intertwining monad powers and their original insertion maps -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Monad

/-- A genuine intertwining functor isomorphism iterates to the same original
monad powers in the two categories. -/
def crossMonadPowerIso {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (T : Monad C) (S : Monad D) (J : C ⥤ D)
    (e : T.toFunctor ⋙ J ≅ J ⋙ S.toFunctor) :
    (n : ℕ) → (F : C) →
      J.obj ((Monad.monadPow T n).obj F) ≅ (Monad.monadPow S n).obj (J.obj F)
  | 0, F => Iso.refl (J.obj F)
  | n + 1, F => crossMonadPowerIso T S J e n (T.obj F) ≪≫
      (Monad.monadPow S n).mapIso (e.app F)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original coefficient map commutes with the iterated comparison. -/
theorem crossMonadPowerIso_naturality {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (T : Monad C) (S : Monad D) (J : C ⥤ D)
    (e : T.toFunctor ⋙ J ≅ J ⋙ S.toFunctor) (n : ℕ) {F G : C} (f : F ⟶ G) :
    J.map ((Monad.monadPow T n).map f) ≫ (crossMonadPowerIso T S J e n G).hom =
      (crossMonadPowerIso T S J e n F).hom ≫ (Monad.monadPow S n).map (J.map f) := by
  induction n generalizing F G with
  | zero =>
      change J.map f ≫ 𝟙 _ = 𝟙 _ ≫ J.map f
      simp only [Category.comp_id, Category.id_comp]
  | succ n ih =>
      change J.map ((Monad.monadPow T n).map (T.map f)) ≫
          ((crossMonadPowerIso T S J e n (T.obj G)).hom ≫
            (Monad.monadPow S n).map (e.hom.app G)) =
        ((crossMonadPowerIso T S J e n (T.obj F)).hom ≫
            (Monad.monadPow S n).map (e.hom.app F)) ≫
          (Monad.monadPow S n).map (S.map (J.map f))
      have hn : J.map (T.map f) ≫ e.hom.app G = e.hom.app F ≫ S.map (J.map f) :=
        e.hom.naturality f
      rw [← Category.assoc, ih (T.map f), Category.assoc,
        ← Functor.map_comp, hn, Functor.map_comp, ← Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine unit square gives every original unit-insertion square. -/
theorem crossMonadPowerIso_etaAtPos {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (T : Monad C) (S : Monad D) (J : C ⥤ D)
    (e : T.toFunctor ⋙ J ≅ J ⋙ S.toFunctor)
    (hu : ∀ F : C, J.map (T.η.app F) ≫ e.hom.app F = S.η.app (J.obj F))
    (n : ℕ) (i : Fin (n + 1)) (F : C) :
    J.map (Monad.etaAtPos T n i F) ≫ (crossMonadPowerIso T S J e (n + 1) F).hom =
      (crossMonadPowerIso T S J e n F).hom ≫ Monad.etaAtPos S n i (J.obj F) := by
  induction n generalizing F with
  | zero =>
      change J.map (T.η.app F) ≫ (𝟙 _ ≫ e.hom.app F) = 𝟙 _ ≫ S.η.app (J.obj F)
      simpa only [Category.id_comp] using hu F
  | succ n ih =>
      rcases i with ⟨k, hk⟩
      cases k with
      | zero =>
          change J.map ((Monad.monadPow T (n + 1)).map (T.η.app F)) ≫
              ((crossMonadPowerIso T S J e (n + 1) (T.obj F)).hom ≫
                (Monad.monadPow S (n + 1)).map (e.hom.app F)) =
            (crossMonadPowerIso T S J e (n + 1) F).hom ≫
              (Monad.monadPow S (n + 1)).map (S.η.app (J.obj F))
          rw [← Category.assoc,
            crossMonadPowerIso_naturality T S J e (n + 1) (T.η.app F),
            Category.assoc, ← Functor.map_comp, hu F]
          rfl
      | succ k =>
          let j : Fin (n + 1) := ⟨k, by omega⟩
          change J.map (Monad.etaAtPos T n j (T.obj F)) ≫
              ((crossMonadPowerIso T S J e (n + 1) (T.obj F)).hom ≫
                (Monad.monadPow S (n + 1)).map (e.hom.app F)) =
            ((crossMonadPowerIso T S J e n (T.obj F)).hom ≫
                (Monad.monadPow S n).map (e.hom.app F)) ≫
              Monad.etaAtPos S n j (S.obj (J.obj F))
          have hn : (Monad.monadPow S n).map (e.hom.app F) ≫
              Monad.etaAtPos S n j (S.obj (J.obj F)) =
            Monad.etaAtPos S n j (J.obj (T.obj F)) ≫
              (Monad.monadPow S (n + 1)).map (e.hom.app F) :=
            Monad.etaAtPos_naturality S n j (e.hom.app F)
          rw [← Category.assoc, ih j (T.obj F), Category.assoc, ← hn, ← Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Three genuine coordinate squares compose through the same comparison isos. -/
theorem threeCoordinateSquares {C : Type uC} [Category.{vC} C]
    {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : C}
    (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁) (h : C₀ ⟶ C₁) (k : D₀ ⟶ D₁)
    (a₀ : A₀ ≅ B₀) (a₁ : A₁ ≅ B₁) (b₀ : B₀ ≅ C₀) (b₁ : B₁ ≅ C₁)
    (c₀ : D₀ ≅ C₀) (c₁ : D₁ ≅ C₁)
    (ha : f ≫ a₁.hom = a₀.hom ≫ g)
    (hb : g ≫ b₁.hom = b₀.hom ≫ h)
    (hc : k ≫ c₁.hom = c₀.hom ≫ h) :
    f ≫ (a₁ ≪≫ b₁ ≪≫ c₁.symm).hom = (a₀ ≪≫ b₀ ≪≫ c₀.symm).hom ≫ k := by
  have hab : f ≫ a₁.hom ≫ b₁.hom = a₀.hom ≫ b₀.hom ≫ h := by
    rw [← Category.assoc, ha, Category.assoc, hb]
  rw [← cancel_mono c₁.hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hc]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using hab

end CategoryTheory.Monad
