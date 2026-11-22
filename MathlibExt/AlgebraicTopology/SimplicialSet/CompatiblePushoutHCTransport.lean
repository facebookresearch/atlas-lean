/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Transport of homotopy cartesian squares

This file expresses homotopy cartesianness using the ordinary pullback lift followed by the homotopy pullback comparison. For a sharp right map it is equivalent to weakness of the ordinary lift, and it is preserved and reflected by commuting maps of squares whose four components are weak equivalences.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SSet.SharpComparisonDraft
namespace SSet.RezkCompatiblePushout

/-- On a sharp right map, the original HC assertion is exactly weakness of
its ordinary lift. No fibrancy assumption is imposed on its base. -/
theorem hc_iff_ordinaryLift_weak {A X Y Z : SSet.{u}}
    {f : A ⟶ X} {s : A ⟶ Y} {p : X ⟶ Z} {g : Y ⟶ Z}
    (sq : CommSq f s p g) (hp : Sharp p) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) ↔
      WeakEquivalence (pullback.lift f s sq.w) := by
  let _ : WeakEquivalence (comparison p g) := hp Y g
  exact weakEquivalence_postcomp_iff (pullback.lift f s sq.w) (comparison p g)

/-- An actual strict square with sharp right map is HC by its own universal
property and the actual comparison, with the original two projections. -/
theorem strictSquare_hc {A X Y Z : SSet.{u}}
    {f : A ⟶ X} {s : A ⟶ Y} {p : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback f s p g) (hp : Sharp p) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) := by
  have h : sq.isoPullback.hom = pullback.lift f s sq.w := by
    apply pullback.hom_ext <;> simp
  let _ : IsIso (pullback.lift f s sq.w) := by rw [← h]; infer_instance
  let _ : WeakEquivalence (comparison p g) := hp Y g
  infer_instance

/-- Weak maps of whole original squares preserve and reflect the literal
HC assertion. All four components and every original square law are retained. -/
theorem hc_weakSquare_iff {A X Y Z A' X' Y' Z' : SSet.{u}}
    {f : A ⟶ X} {s : A ⟶ Y} {p : X ⟶ Z} {g : Y ⟶ Z}
    {f' : A' ⟶ X'} {s' : A' ⟶ Y'} {p' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (sq : CommSq f s p g) (sq' : CommSq f' s' p' g')
    (alphaA : A ⟶ A') (alphaX : X ⟶ X') (alphaY : Y ⟶ Y') (alphaZ : Z ⟶ Z')
    (hf : f ≫ alphaX = alphaA ≫ f') (hs : s ≫ alphaY = alphaA ≫ s')
    (hp : p ≫ alphaZ = alphaX ≫ p') (hg : g ≫ alphaZ = alphaY ≫ g')
    (hA : WeakEquivalence alphaA) (hX : WeakEquivalence alphaX)
    (hY : WeakEquivalence alphaY) (hZ : WeakEquivalence alphaZ) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) ↔
      WeakEquivalence (pullback.lift f' s' sq'.w ≫ comparison p' g') := by
  let eta : cospan p g ⟶ cospan p' g' := cospanHomMk alphaZ alphaX alphaY hp hg
  let L := pullback.lift f s sq.w
  let L' := pullback.lift f' s' sq'.w
  have hL : L ≫ lim.map eta = alphaA ≫ L' := by
    apply pullback.hom_ext
    · simpa [L, L', eta, Category.assoc] using hf
    · simpa [L, L', eta, Category.assoc] using hs
  have hEta (j : WalkingCospan) : WeakEquivalence (eta.app j) := by
    cases j with
    | none => change WeakEquivalence alphaZ; exact hZ
    | some a =>
      cases a with
      | left => change WeakEquivalence alphaX; exact hX
      | right => change WeakEquivalence alphaY; exact hY
  let _ : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map eta) :=
    homotopyPullback_map_weakEquivalence eta hEta
  let _ : WeakEquivalence alphaA := hA
  have hnat : lim.map eta ≫ comparison p' g' = comparison p g ≫
      (homotopyPullback (C := SSet.{u})).map eta :=
    (homotopyPullbackComparison (C := SSet.{u})).naturality eta
  have hfac : (L ≫ comparison p g) ≫ (homotopyPullback (C := SSet.{u})).map eta =
      alphaA ≫ (L' ≫ comparison p' g') := by
    calc
      (L ≫ comparison p g) ≫ (homotopyPullback (C := SSet.{u})).map eta =
          L ≫ (comparison p g ≫ (homotopyPullback (C := SSet.{u})).map eta) :=
        Category.assoc _ _ _
      _ = L ≫ (lim.map eta ≫ comparison p' g') := by rw [← hnat]
      _ = (L ≫ lim.map eta) ≫ comparison p' g' := (Category.assoc _ _ _).symm
      _ = (alphaA ≫ L') ≫ comparison p' g' := by rw [hL]
      _ = alphaA ≫ (L' ≫ comparison p' g') := Category.assoc _ _ _
  constructor
  · intro h
    let _ : WeakEquivalence (L ≫ comparison p g) := h
    have hcomp : WeakEquivalence
        ((L ≫ comparison p g) ≫ (homotopyPullback (C := SSet.{u})).map eta) :=
      inferInstance
    rw [hfac] at hcomp
    let _ := hcomp
    exact weakEquivalence_of_precomp alphaA (L' ≫ comparison p' g')
  · intro h
    let _ : WeakEquivalence (L' ≫ comparison p' g') := h
    have hcomp : WeakEquivalence (alphaA ≫ (L' ≫ comparison p' g')) := inferInstance
    rw [← hfac] at hcomp
    let _ := hcomp
    exact weakEquivalence_of_postcomp (L ≫ comparison p g)
      ((homotopyPullback (C := SSet.{u})).map eta)

end SSet.RezkCompatiblePushout
