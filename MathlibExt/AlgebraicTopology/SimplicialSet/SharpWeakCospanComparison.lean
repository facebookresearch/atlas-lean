/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SharpFibrations

/-!
# Weak changes of all three legs of sharp simplicial cospans

The actual ordinary pullback map is weak when both original left legs
are sharp and the total, parameter, and base maps are weak. This keeps
the whole changing-base square and does not require a Kan base.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.SharpComparisonDraft

/-- The whole ordinary pullback comparison preserves weak cospan changes between sharp maps. -/
theorem pullbackMap_weak {X B T X' B' T' : SSet.{u}}
    (p : X ⟶ B) (t : T ⟶ B) (q : X' ⟶ B') (t' : T' ⟶ B')
    (s : X ⟶ X') (r : T ⟶ T') (h : B ⟶ B')
    (hsq : p ≫ h = s ≫ q) (hrq : t ≫ h = r ≫ t')
    (hs : WeakEquivalence s) (hr : WeakEquivalence r) (hh : WeakEquivalence h)
    (hp : Sharp p) (hq : Sharp q) :
    WeakEquivalence (pullback.map p t q t' s r h hsq hrq) := by
  let eta : cospan p t ⟶ cospan q t' := cospanHomMk h s r hsq hrq
  have heta (j : WalkingCospan) : WeakEquivalence (eta.app j) := by
    cases j with
    | none => exact hh
    | some a => cases a with
      | left => exact hs
      | right => exact hr
  let _ : WeakEquivalence (comparison p t) := hp T t
  let _ : WeakEquivalence (comparison q t') := hq T' t'
  let _ : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map eta) :=
    homotopyPullback_map_weakEquivalence eta heta
  have hfac : lim.map eta ≫ comparison q t' = comparison p t ≫
      (homotopyPullback (C := SSet.{u})).map eta :=
    (homotopyPullbackComparison (C := SSet.{u})).naturality eta
  have hc : WeakEquivalence (lim.map eta ≫ comparison q t') := by
    rw [hfac]
    infer_instance
  let _ := hc
  have hm : WeakEquivalence (lim.map eta) :=
    weakEquivalence_of_postcomp (lim.map eta) (comparison q t')
  have he : lim.map eta = pullback.map p t q t' s r h hsq hrq := by
    apply pullback.hom_ext <;> simp [eta, pullback.map]
  rw [he] at hm
  exact hm

end SSet.SharpComparisonDraft
