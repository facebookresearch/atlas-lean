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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwisePushoutAssembly
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Zero coherence for the assembled levelwise pushout

Given `D : LevelwisePushoutData C` with induced maps `P₀ ⟶ P₁ ⟶ P₂`,
zero composites `wS`/`wT` on the two source diagrams imply the induced
composite is zero. The proof applies `IsPushout.hom_ext` at level 0 and
rewrites each leg with the four assembly leg laws (`inl`/`inr` at levels
`0 → 1` and `1 → 2`), associativity, and zero composition. The result is
packaged as a `ShortComplex` with focused `f`/`g` computation lemmas.

Requires only `[Category C] [HasZeroMorphisms C]`. No `Preadditive`,
`HasZeroObject`, `ExactCategory`, or `WaldhausenCategoryWithoutGluing` hypotheses.
`IsPushout` orientation follows the assembly file: `S`/`T` legs point into
the pushout apices and the induced maps point forward.

Nonclaims: no admissible-mono/exact/cofiber-sequence theorem, no
`WaldhausenCategoryWithoutGluing` instance, no cokernel comparison, no additivity,
no `K₀`/G-theory/spectra/Q-S comparison.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Induced maps of a `LevelwisePushoutData` compose to zero from zero
composites on the two source diagrams. -/
theorem levelwisePushout_comp_zero (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) :
    D.inducedMap01 ≫ D.inducedMap12 = 0 := by
  apply D.isPushout0.hom_ext
  · have h01S : D.inlS0 ≫ D.inducedMap01 = D.S.map' 0 1 ≫ D.inlS1 :=
      D.isPushout0.inl_desc _ _ _
    have h12S : D.inlS1 ≫ D.inducedMap12 = D.S.map' 1 2 ≫ D.inlS2 :=
      D.isPushout1.inl_desc _ _ _
    calc D.inlS0 ≫ (D.inducedMap01 ≫ D.inducedMap12)
        = (D.S.map' 0 1 ≫ D.S.map' 1 2) ≫ D.inlS2 := by
          rw [← Category.assoc, h01S, Category.assoc, h12S, ← Category.assoc]
      _ = 0 ≫ D.inlS2 := by rw [wS]
      _ = 0 := by simp
      _ = D.inlS0 ≫ 0 := by simp
  · have h01T : D.inrT0 ≫ D.inducedMap01 = D.T.map' 0 1 ≫ D.inrT1 :=
      D.isPushout0.inr_desc _ _ _
    have h12T : D.inrT1 ≫ D.inducedMap12 = D.T.map' 1 2 ≫ D.inrT2 :=
      D.isPushout1.inr_desc _ _ _
    calc D.inrT0 ≫ (D.inducedMap01 ≫ D.inducedMap12)
        = (D.T.map' 0 1 ≫ D.T.map' 1 2) ≫ D.inrT2 := by
          rw [← Category.assoc, h01T, Category.assoc, h12T, ← Category.assoc]
      _ = 0 ≫ D.inrT2 := by rw [wT]
      _ = 0 := by simp
      _ = D.inrT0 ≫ 0 := by simp

/-- Associated short complex on `P₀ ⟶ P₁ ⟶ P₂` with the induced maps. -/
noncomputable def levelwisePushoutShortComplex (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) : ShortComplex C where
  f := D.inducedMap01
  g := D.inducedMap12
  zero := levelwisePushout_comp_zero C D wS wT

/-- The packaged short complex recovers the first induced map. -/
@[simp]
theorem levelwisePushoutShortComplex_f (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) :
    (levelwisePushoutShortComplex C D wS wT).f = D.inducedMap01 :=
  rfl

/-- The packaged short complex recovers the second induced map. -/
@[simp]
theorem levelwisePushoutShortComplex_g (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) :
    (levelwisePushoutShortComplex C D wS wT).g = D.inducedMap12 :=
  rfl

/-- The packaged short complex has the actual source pushout apex. -/
@[simp]
theorem levelwisePushoutShortComplex_X₁ (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) :
    (levelwisePushoutShortComplex C D wS wT).X₁ = D.P0 :=
  rfl

/-- The packaged short complex has the actual middle pushout apex. -/
@[simp]
theorem levelwisePushoutShortComplex_X₂ (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) :
    (levelwisePushoutShortComplex C D wS wT).X₂ = D.P1 :=
  rfl

/-- The packaged short complex has the actual quotient pushout apex. -/
@[simp]
theorem levelwisePushoutShortComplex_X₃ (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0) :
    (levelwisePushoutShortComplex C D wS wT).X₃ = D.P2 :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
