/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.TailPullbackColimit
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open SSet.RezkTailPullbackColimit
namespace TailPullbackColimitTest

private def arbitrary_original_no_mono_hypotheses
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    IsColimit (tailPullbackCocone p n cX cY q hq) :=
  tailPullbackCoconeIsColimit p n cX cY q hq hX hY

/-- The actual directed diagram collapses infinitely many values on every strict transition. -/
private def foldTypes : ℕ ⥤ Type 3 where
  obj _ := ULift.{3} Nat
  map {i j} _ := ↾fun x => if i = j then x else ULift.up 0
  map_id i := by ext x; simp
  map_comp {i j k} f g := by
    ext x
    by_cases hij : i = j
    · subst j; simp
    by_cases hjk : j = k
    · subst k; simp
    have hik : i ≠ k := by
      intro h
      apply hij
      exact Nat.le_antisymm (leOfHom f) (by simpa only [← h] using leOfHom g)
    simp [hij, hjk, hik]
private def nonMonoY : ℕ ⥤ SSet.{3} :=
  foldTypes ⋙ CategoryTheory.Functor.const SimplexCategoryᵒᵖ
private theorem actual_strict_transition_not_mono :
    ¬ Mono (nonMonoY.map (homOfLE (show 0 ≤ 1 by decide))) := by
  intro hm
  let _ : Mono (nonMonoY.map (homOfLE (show 0 ≤ 1 by decide))) := hm
  have hi := (CategoryTheory.mono_iff_injective
    ((nonMonoY.map (homOfLE (show 0 ≤ 1 by decide))).app (op ⦋0⦌))).mp inferInstance
  have h : (ULift.up (0 : Nat) : ULift.{3} Nat) = ULift.up 1 := hi rfl
  exact Nat.zero_ne_one (congrArg ULift.down h)


private def actual_nonMono_Y_tail_colimit :
    IsColimit (tailPullbackCocone (𝟙 nonMonoY) 1
      (colimit.cocone nonMonoY) (colimit.cocone nonMonoY) (𝟙 (colimit nonMonoY))
      (by intro m; simp)) :=
  tailPullbackCoconeIsColimit (𝟙 nonMonoY) 1
    (colimit.cocone nonMonoY) (colimit.cocone nonMonoY) (𝟙 (colimit nonMonoY))
    (by intro m; simp) (colimit.isColimit nonMonoY) (colimit.isColimit nonMonoY)

private theorem both_actual_inverse_aggregate_legs
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    (tailPullbackColimitIso p n cX cY q hq hX hY).inv ≫
        colimit.desc (tailPullbackDiagram p n) (tailFirstProjectionCocone p n cX cY q hq) =
      pullback.fst q (cY.ι.app n) ∧
    (tailPullbackColimitIso p n cX cY q hq hX hY).inv ≫
        colimit.desc (tailPullbackDiagram p n) (tailSecondProjectionCocone p n cX cY q hq) =
      pullback.snd q (cY.ι.app n) :=
  tailPullbackColimitIso_inv_legs p n cX cY q hq hX hY


private def actual_nonMono_Y_tail_zero :
    IsColimit (tailPullbackCocone (𝟙 nonMonoY) 0
      (colimit.cocone nonMonoY) (colimit.cocone nonMonoY) (𝟙 (colimit nonMonoY))
      (by intro m; simp)) :=
  tailPullbackCoconeIsColimit (𝟙 nonMonoY) 0
    (colimit.cocone nonMonoY) (colimit.cocone nonMonoY) (𝟙 (colimit nonMonoY))
    (by intro m; simp) (colimit.isColimit nonMonoY) (colimit.isColimit nonMonoY)

private theorem original_infinite_fixed_base_values :
    Function.Injective (fun k : Nat => (ULift.up k : (nonMonoY.obj 0).obj (op ⦋0⦌))) := by
  intro i j h
  exact congrArg ULift.down h

private def empty : SSet.{0} := ⊥_ _
private def emptyDiagram : ℕ ⥤ SSet.{0} := (CategoryTheory.Functor.const ℕ).obj empty
private def actual_empty_tail_zero :
    IsColimit (tailPullbackCocone (𝟙 emptyDiagram) 0
      (constCocone ℕ empty) (constCocone ℕ empty) (𝟙 empty)
      (by intro m; change (𝟙 empty) ≫ (𝟙 empty) = (𝟙 empty) ≫ (𝟙 empty); rfl)) :=
  by
    let _ : IsConnected ℕ := CategoryTheory.IsFiltered.isConnected ℕ
    exact tailPullbackCoconeIsColimit (𝟙 emptyDiagram) 0
      (constCocone ℕ empty) (constCocone ℕ empty) (𝟙 empty)
      (by intro m; change (𝟙 empty) ≫ (𝟙 empty) = (𝟙 empty) ≫ (𝟙 empty); rfl)
      (isColimitConstCocone ℕ empty) (isColimitConstCocone ℕ empty)


/-- The generic original forward legs are both checked on the SAME colimit-to-pullback Iso. -/
private theorem both_actual_forward_projection_legs
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) (k : ℕ) :
    colimit.ι (tailPullbackDiagram p n) k ≫ (tailPullbackColimitIso p n cX cY q hq hX hY).hom ≫
        pullback.fst q (cY.ι.app n) =
      pullback.fst (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ≫ cX.ι.app (n + k) ∧
    colimit.ι (tailPullbackDiagram p n) k ≫ (tailPullbackColimitIso p n cX cY q hq hX hY).hom ≫
        pullback.snd q (cY.ι.app n) =
      pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) :=
  tailPullbackColimitIso_hom_legs p n cX cY q hq hX hY k

end TailPullbackColimitTest
