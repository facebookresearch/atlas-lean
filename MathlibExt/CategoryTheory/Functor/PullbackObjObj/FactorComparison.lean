/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The full mapping-corner comparison along a given factor

For the supplied factor law `j ≫ r = σ`, restriction along `r` gives
a morphism from the caller's corner for `σ` to its corner for `j`.
The target morphism is a base change of the same restriction at the
target of the tested arrow. The construction retains both chosen
corner pullbacks and proves the complete Arrow equation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.PullbackObjObj.FactorComparison

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)
  {A M B : C₁} {X Y : C₃}
  (j : A ⟶ M) (r : M ⟶ B) (σ : A ⟶ B) (fac : j ≫ r = σ)
  (p : X ⟶ Y)
  (cornerσ : G.PullbackObjObj σ p) (cornerj : G.PullbackObjObj j p)

include fac

/-- The original full contravariant factor law, at every target. -/
theorem restriction_factor (T : C₃) :
    (G.map σ.op).app T = (G.map r.op).app T ≫ (G.map j.op).app T := by
  rw [← fac, op_comp, G.map_comp, NatTrans.comp_app]

/-- The two proposed target coordinates satisfy the original corner
condition using the supplied factor equation. -/
theorem targetCompatibility :
    cornerσ.fst ≫ (G.obj (op A)).map p =
      (cornerσ.snd ≫ (G.map r.op).app Y) ≫ (G.map j.op).app Y := by
  rw [Category.assoc, ← restriction_factor G j r σ fac Y]
  exact cornerσ.isPullback.w

/-- The actual target map is the lift into the supplied `j` corner,
with its first coordinate unchanged and its second restricted by `r`. -/
def targetMap : cornerσ.pt ⟶ cornerj.pt :=
  cornerj.isPullback.lift cornerσ.fst (cornerσ.snd ≫ (G.map r.op).app Y)
    (targetCompatibility G j r σ fac p cornerσ)

/-- The complete first projection is the caller's original one. -/
theorem targetMap_fst :
    targetMap G j r σ fac p cornerσ cornerj ≫ cornerj.fst = cornerσ.fst :=
  cornerj.isPullback.lift_fst _ _ _

/-- The complete second projection is the original target restriction. -/
theorem targetMap_snd :
    targetMap G j r σ fac p cornerσ cornerj ≫ cornerj.snd =
      cornerσ.snd ≫ (G.map r.op).app Y :=
  cornerj.isPullback.lift_snd _ _ _

/-- Both full corner maps satisfy the original factor equation. -/
theorem corner_factor :
    cornerσ.π ≫ targetMap G j r σ fac p cornerσ cornerj =
      (G.map r.op).app X ≫ cornerj.π := by
  apply cornerj.isPullback.hom_ext
  · rw [Category.assoc, targetMap_fst, cornerσ.π_fst,
      Category.assoc, cornerj.π_fst]
    exact restriction_factor G j r σ fac X
  · rw [Category.assoc, targetMap_snd, ← Category.assoc, cornerσ.π_snd,
      Category.assoc, cornerj.π_snd]
    exact (G.map r.op).naturality p

/-- The actual original Arrow map between the two source arrows. -/
def sourceArrow : Arrow.mk j ⟶ Arrow.mk σ where
  left := 𝟙 A
  right := r
  w := (Category.id_comp σ).trans fac.symm

theorem sourceArrow_left : (sourceArrow j r σ fac).left = 𝟙 A := rfl

theorem sourceArrow_right : (sourceArrow j r σ fac).right = r := rfl

/-- The entire induced corner Arrow map has the original restriction
at `X` and the constructed full pullback lift at `Y`. -/
def cornerArrow : Arrow.mk cornerσ.π ⟶ Arrow.mk cornerj.π where
  left := (G.map r.op).app X
  right := targetMap G j r σ fac p cornerσ cornerj
  w := (corner_factor G j r σ fac p cornerσ cornerj).symm

theorem cornerArrow_left :
    (cornerArrow G j r σ fac p cornerσ cornerj).left = (G.map r.op).app X := rfl

theorem cornerArrow_right :
    (cornerArrow G j r σ fac p cornerσ cornerj).right =
      targetMap G j r σ fac p cornerσ cornerj := rfl

/-- The whole Arrow map is the existing functorial map of the actual
Arrow `(𝟙 A, r)`, with the caller's factor equation. -/
theorem cornerArrow_eq_mapArrowLeft :
    cornerArrow G j r σ fac p cornerσ cornerj =
      Functor.PullbackObjObj.mapArrowLeft
        (f₁ := Arrow.mk σ) (f₁' := Arrow.mk j) (f₃ := Arrow.mk p) cornerσ cornerj
        (sourceArrow j r σ fac) := by
  apply Arrow.hom_ext
  · rfl
  · rw [cornerArrow_right]
    apply Eq.trans _ (Functor.PullbackObjObj.mapArrowLeft_right
      (f₁ := Arrow.mk σ) (f₁' := Arrow.mk j) (f₃ := Arrow.mk p)
      cornerσ cornerj (sourceArrow j r σ fac)).symm
    apply cornerj.isPullback.hom_ext
    · rw [targetMap_fst, IsPullback.lift_fst, sourceArrow_left]
      change cornerσ.fst = cornerσ.fst ≫ (G.map (𝟙 A).op).app X
      have hId : (G.map (𝟙 A).op).app X = 𝟙 ((G.obj (op A)).obj X) := by
        change (G.map (𝟙 (op A))).app X = _
        exact congrArg (fun τ : G.obj (op A) ⟶ G.obj (op A) => τ.app X) (G.map_id (op A))
      rw [hId, Category.comp_id]
    · rw [targetMap_snd, IsPullback.lift_snd]
      rw [sourceArrow_right]
      rfl

/-- The actual target comparison is a base change of the original
restriction along the second projection of the supplied `j` corner.
The proof uses both given universal properties, without selecting
another pullback. -/
theorem targetMap_isPullback :
    IsPullback cornerσ.snd (targetMap G j r σ fac p cornerσ cornerj)
      ((G.map r.op).app Y) cornerj.snd := by
  refine IsPullback.mk' (targetMap_snd G j r σ fac p cornerσ cornerj).symm ?_ ?_
  · intro T φ φ' h₁ h₂
    apply cornerσ.isPullback.hom_ext
    · have h := congrArg (fun h => h ≫ cornerj.fst) h₂
      simpa only [Category.assoc, targetMap_fst] using h
    · exact h₁
  · intro T a b w
    have hb : (b ≫ cornerj.fst) ≫ (G.obj (op A)).map p =
        a ≫ (G.map σ.op).app Y := by
      calc
        _ = b ≫ (cornerj.fst ≫ (G.obj (op A)).map p) := Category.assoc _ _ _
        _ = b ≫ (cornerj.snd ≫ (G.map j.op).app Y) := by rw [cornerj.isPullback.w]
        _ = (b ≫ cornerj.snd) ≫ (G.map j.op).app Y := (Category.assoc _ _ _).symm
        _ = (a ≫ (G.map r.op).app Y) ≫ (G.map j.op).app Y := by rw [← w]
        _ = _ := by rw [Category.assoc, ← restriction_factor G j r σ fac Y]
    let l := cornerσ.isPullback.lift (b ≫ cornerj.fst) a hb
    refine ⟨l, cornerσ.isPullback.lift_snd _ _ _, ?_⟩
    apply cornerj.isPullback.hom_ext
    · rw [Category.assoc, targetMap_fst]
      exact cornerσ.isPullback.lift_fst _ _ _
    · rw [Category.assoc, targetMap_snd, ← Category.assoc]
      rw [cornerσ.isPullback.lift_snd]
      exact w

/-- The complete coefficient function of the target comparison. -/
def coefficientMap (T : C₂) : (T ⟶ cornerσ.pt) → (T ⟶ cornerj.pt) :=
  fun h => h ≫ targetMap G j r σ fac p cornerσ cornerj

theorem coefficientMap_function (T : C₂) :
    coefficientMap G j r σ fac p cornerσ cornerj T =
      fun h => h ≫ targetMap G j r σ fac p cornerσ cornerj := rfl

/-- Every coefficient input map respects the same whole target
comparison, including every original point of each Hom set. -/
theorem coefficientMap_naturality {T T' : C₂} (a : T' ⟶ T) (h : T ⟶ cornerσ.pt) :
    coefficientMap G j r σ fac p cornerσ cornerj T' (a ≫ h) =
      a ≫ coefficientMap G j r σ fac p cornerσ cornerj T h :=
  Category.assoc _ _ _

end CategoryTheory.Functor.PullbackObjObj.FactorComparison
