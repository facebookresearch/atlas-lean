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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationPushout

/-! # Tests for pushouts along finite-stage cofibrations -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationPushoutTests

open _root_.CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance stageCofibrationPushoutTestsWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (D : StagePushoutComponentData C f g) :
    StagePushoutPresentation C f g :=
  D.toPresentation

example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (hf : stageCofibrations C n f) :
    StagePushoutPresentation C f g :=
  StageCofibrationPushout.presentation (g := g) hf

example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (hf : stageCofibrations C n f) :
    IsPushout f g
      (StageCofibrationPushout.inl (g := g) hf)
      (StageCofibrationPushout.inr (g := g) hf) :=
  StageCofibrationPushout.isPushout (g := g) hf

example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (hf : stageCofibrations C n f) :
    stageCofibrations C n (StageCofibrationPushout.inr (g := g) hf) :=
  StageCofibrationPushout.inr_stageCofibrations (g := g) hf

example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (hf : stageCofibrations C n f) :
    ∃ (P : Stage C n) (inN : N ⟶ P) (inM : M ⟶ P),
      IsPushout g f inN inM ∧ stageCofibrations C n inN :=
  StageCofibrationPushout.exists_pushout (g := g) hf

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationPushoutTests
