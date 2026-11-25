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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutZeroCoherence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Cokernel half of the assembled levelwise pushout

Given `D : LevelwisePushoutData C` with zero composites `wS`/`wT` on the two
source diagrams, source cokernel colimits `hS`/`hT` on the second arrows, and
an epi hypothesis on the common diagram second arrow `D.R.map' 1 2`, the
packaged `levelwisePushoutShortComplex C D wS wT` has a cokernel colimit at
its `g`.

The proof reuses component pushout `desc`/`fac`/`hom_ext`, source cokernel
universal properties (`desc`, `π_desc`, `hom_ext`), associativity, and epi
cancellation. The epi lets descended `S₂`/`T₂` maps agree on `R₂` for
`isPushout2.desc` via `RS`/`RT` naturality and `isPushout1.w`.

Orientation follows the assembly file: `S`/`T` legs point into the pushout
apices (`inlS`/`inrT`); induced maps point forward (`P₀ ⟶ P₁ ⟶ P₂`);
the descending map points out of the assembled arrow.

Nonclaims: no `IsAdmissibleExact` claim, no cofiber-sequence or category
instance, no general gluing, no additivity, no `K₀`/G/spectra/Q-S comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- The assembled short complex has a cokernel colimit at its `g` from
source cokernel colimits and an epi on the common second arrow. -/
noncomputable def levelwisePushoutShortComplex_isColimit_cokernel
    (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.S.map' 1 2 (Nat.le_succ 1) le_rfl = 0)
    (wT : D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.T.map' 1 2 (Nat.le_succ 1) le_rfl = 0)
    (hS : IsColimit (CokernelCofork.ofπ (D.S.map' 1 2 (Nat.le_succ 1) le_rfl) wS))
    (hT : IsColimit (CokernelCofork.ofπ (D.T.map' 1 2 (Nat.le_succ 1) le_rfl) wT))
    [Epi (D.R.map' 1 2 (Nat.le_succ 1) le_rfl)] :
    IsColimit (CokernelCofork.ofπ
      (levelwisePushoutShortComplex C D wS wT).g
      (levelwisePushoutShortComplex C D wS wT).zero) := by
  have hg_eq : (levelwisePushoutShortComplex C D wS wT).g = D.inducedMap12 :=
    levelwisePushoutShortComplex_g C D wS wT
  have h12S : D.inlS1 ≫ D.inducedMap12 = D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inlS2 :=
    D.isPushout1.inl_desc _ _ _
  have h12T : D.inrT1 ≫ D.inducedMap12 = D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inrT2 :=
    D.isPushout1.inr_desc _ _ _
  have mkDesc : ∀ {W : C} (g' : D.P1 ⟶ W),
      (levelwisePushoutShortComplex C D wS wT).f ≫ g' = 0 →
      Σ' (aS : D.S.obj' 2 le_rfl ⟶ W) (aT : D.T.obj' 2 le_rfl ⟶ W),
        (D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aS = D.inlS1 ≫ g') ∧
        (D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aT = D.inrT1 ≫ g') ∧
        (ComposableArrows.app' D.RS 2 le_rfl ≫ aS =
          ComposableArrows.app' D.RT 2 le_rfl ≫ aT) := by
    intro W g' eq'
    have hf_eq : (levelwisePushoutShortComplex C D wS wT).f = D.inducedMap01 :=
      levelwisePushoutShortComplex_f C D wS wT
    have h01S : D.inlS0 ≫ D.inducedMap01 =
        D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inlS1 :=
      D.isPushout0.inl_desc _ _ _
    have h01T : D.inrT0 ≫ D.inducedMap01 =
        D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inrT1 :=
      D.isPushout0.inr_desc _ _ _
    have hNatS : D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ ComposableArrows.app' D.RS 2 le_rfl =
        ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫ D.S.map' 1 2 (Nat.le_succ 1) le_rfl :=
      ComposableArrows.naturality' D.RS 1 2
    have hNatT : D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ ComposableArrows.app' D.RT 2 le_rfl =
        ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫ D.T.map' 1 2 (Nat.le_succ 1) le_rfl :=
      ComposableArrows.naturality' D.RT 1 2
    have w1 : ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫ D.inlS1 =
        ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫ D.inrT1 :=
      D.isPushout1.w
    have eq01 : D.inducedMap01 ≫ g' = 0 := by
      have : (levelwisePushoutShortComplex C D wS wT).f ≫ g' = 0 := eq'
      rwa [hf_eq] at this
    have hkS : D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ (D.inlS1 ≫ g') = 0 := by
      calc D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ (D.inlS1 ≫ g')
          = (D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inlS1) ≫ g' :=
            (Category.assoc _ _ _).symm
        _ = (D.inlS0 ≫ D.inducedMap01) ≫ g' := by rw [← h01S]
        _ = D.inlS0 ≫ (D.inducedMap01 ≫ g') := Category.assoc _ _ _
        _ = D.inlS0 ≫ 0 := by rw [eq01]
        _ = 0 := comp_zero
    have hkT : D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ (D.inrT1 ≫ g') = 0 := by
      calc D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ (D.inrT1 ≫ g')
          = (D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inrT1) ≫ g' :=
            (Category.assoc _ _ _).symm
        _ = (D.inrT0 ≫ D.inducedMap01) ≫ g' := by rw [← h01T]
        _ = D.inrT0 ≫ (D.inducedMap01 ≫ g') := Category.assoc _ _ _
        _ = D.inrT0 ≫ 0 := by rw [eq01]
        _ = 0 := comp_zero
    let aS : D.S.obj' 2 le_rfl ⟶ W :=
      hS.desc (CokernelCofork.ofπ (D.inlS1 ≫ g') hkS)
    let aT : D.T.obj' 2 le_rfl ⟶ W :=
      hT.desc (CokernelCofork.ofπ (D.inrT1 ≫ g') hkT)
    have facS : D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aS = D.inlS1 ≫ g' :=
      Cofork.IsColimit.π_desc hS
    have facT : D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aT = D.inrT1 ≫ g' :=
      Cofork.IsColimit.π_desc hT
    have agree : ComposableArrows.app' D.RS 2 le_rfl ≫ aS =
        ComposableArrows.app' D.RT 2 le_rfl ≫ aT := by
      apply (cancel_epi (D.R.map' 1 2 (Nat.le_succ 1) le_rfl)).mp
      calc D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (ComposableArrows.app' D.RS 2 le_rfl ≫ aS)
          = (D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ ComposableArrows.app' D.RS 2 le_rfl) ≫ aS := by
            rw [← Category.assoc]
        _ = (ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫ D.S.map' 1 2 (Nat.le_succ 1) le_rfl) ≫
            aS := by
            rw [hNatS]
        _ = ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫
            (D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aS) := by
            rw [Category.assoc]
        _ = ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫ (D.inlS1 ≫ g') := by
            rw [facS]
        _ = (ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫ D.inlS1) ≫ g' := by
            rw [← Category.assoc]
        _ = (ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫ D.inrT1) ≫ g' := by
            rw [w1]
        _ = ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫ (D.inrT1 ≫ g') := by
            rw [Category.assoc]
        _ = ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫
            (D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aT) := by
            rw [← facT]
        _ = (ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫ D.T.map' 1 2 (Nat.le_succ 1) le_rfl) ≫
            aT := by
            rw [← Category.assoc]
        _ = (D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ ComposableArrows.app' D.RT 2 le_rfl) ≫ aT := by
            rw [← hNatT]
        _ = D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (ComposableArrows.app' D.RT 2 le_rfl ≫ aT) := by
            rw [Category.assoc]
    exact ⟨aS, aT, facS, facT, agree⟩
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} g' eq' => ?_) ?_ ?_
  · change D.P1 ⟶ W at g'
    exact D.isPushout2.desc (mkDesc g' eq').1 (mkDesc g' eq').2.1 (mkDesc g' eq').2.2.2.2
  · intro W g' eq'
    change D.P1 ⟶ W at g'
    dsimp only [id]
    obtain ⟨aS, aT, facS, facT, agree⟩ := mkDesc g' eq'
    have fac_push : D.inducedMap12 ≫ D.isPushout2.desc aS aT agree = g' := by
      apply D.isPushout1.hom_ext
      · calc D.inlS1 ≫ (D.inducedMap12 ≫ D.isPushout2.desc aS aT agree)
            = (D.inlS1 ≫ D.inducedMap12) ≫ D.isPushout2.desc aS aT agree := by
              rw [← Category.assoc]
          _ = (D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inlS2) ≫ D.isPushout2.desc aS aT agree := by
              rw [h12S]
          _ = D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (D.inlS2 ≫ D.isPushout2.desc aS aT agree) := by
              rw [Category.assoc]
          _ = D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aS := by
              rw [D.isPushout2.inl_desc aS aT agree]
          _ = D.inlS1 ≫ g' := facS
      · calc D.inrT1 ≫ (D.inducedMap12 ≫ D.isPushout2.desc aS aT agree)
            = (D.inrT1 ≫ D.inducedMap12) ≫ D.isPushout2.desc aS aT agree := by
              rw [← Category.assoc]
          _ = (D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inrT2) ≫ D.isPushout2.desc aS aT agree := by
              rw [h12T]
          _ = D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (D.inrT2 ≫ D.isPushout2.desc aS aT agree) := by
              rw [Category.assoc]
          _ = D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aT := by
              rw [D.isPushout2.inr_desc aS aT agree]
          _ = D.inrT1 ≫ g' := facT
    have goal_eq : (levelwisePushoutShortComplex C D wS wT).g ≫
        D.isPushout2.desc aS aT agree = g' := by
      rw [hg_eq]
      exact fac_push
    exact goal_eq
  · intro W g' eq' m hm
    change D.P1 ⟶ W at g'
    change D.P2 ⟶ W at m
    dsimp only [id]
    obtain ⟨aS, aT, facS, facT, agree⟩ := mkDesc g' eq'
    have hm01 : D.inducedMap12 ≫ m = g' := by
      have : (levelwisePushoutShortComplex C D wS wT).g ≫ m = g' := hm
      rwa [hg_eq] at this
    have eS : D.inlS2 ≫ m = aS := by
      apply Cofork.IsColimit.hom_ext hS
      calc D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (D.inlS2 ≫ m)
          = (D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inlS2) ≫ m := by rw [← Category.assoc]
        _ = (D.inlS1 ≫ D.inducedMap12) ≫ m := by rw [← h12S]
        _ = D.inlS1 ≫ (D.inducedMap12 ≫ m) := by rw [Category.assoc]
        _ = D.inlS1 ≫ g' := by rw [hm01]
        _ = D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aS := by rw [facS]
    have eT : D.inrT2 ≫ m = aT := by
      apply Cofork.IsColimit.hom_ext hT
      calc D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (D.inrT2 ≫ m)
          = (D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inrT2) ≫ m := by rw [← Category.assoc]
        _ = (D.inrT1 ≫ D.inducedMap12) ≫ m := by rw [← h12T]
        _ = D.inrT1 ≫ (D.inducedMap12 ≫ m) := by rw [Category.assoc]
        _ = D.inrT1 ≫ g' := by rw [hm01]
        _ = D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ aT := by rw [facT]
    have final : m = D.isPushout2.desc aS aT agree := by
      apply D.isPushout2.hom_ext
      · calc D.inlS2 ≫ m = aS := eS
          _ = D.inlS2 ≫ D.isPushout2.desc aS aT agree := by
              rw [D.isPushout2.inl_desc aS aT agree]
      · calc D.inrT2 ≫ m = aT := eT
          _ = D.inrT2 ≫ D.isPushout2.desc aS aT agree := by
              rw [D.isPushout2.inr_desc aS aT agree]
    exact final

end CategoryTheory.Waldhausen.SConstruction
