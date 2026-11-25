/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationStability

/-! # Stability import, degree arguments, and canonical instances

Import only the focused stability module. Exercise its documented migration
from explicit positional degrees to inferred or named degrees, and the
canonical instances exported through that import.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationStabilityTests

open _root_.CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

example (n : ℕ) (A : Stage C n) : stageCofibrations C n (𝟙 A) :=
  stageCofibrations_id C (n := n) A

example (n : ℕ) (A : Stage C n) : stageCofibrations C n (𝟙 A) :=
  stageCofibrations_id C A

example (n : ℕ) {A B D : Stage C n} (f : A ⟶ B) (g : B ⟶ D)
    (hf : stageCofibrations C n f) (hg : stageCofibrations C n g) :
    stageCofibrations C n (f ≫ g) :=
  stageCofibrations_comp C (n := n) f g hf hg

example (n : ℕ) {A B D : Stage C n} (f : A ⟶ B) (g : B ⟶ D)
    (hf : stageCofibrations C n f) (hg : stageCofibrations C n g) :
    stageCofibrations C n (f ≫ g) :=
  stageCofibrations_comp C f g hf hg

example (n : ℕ) {A B : Stage C n} (f : A ⟶ B) [IsIso f] :
    stageCofibrations C n f :=
  stageCofibrations_of_isIso C (n := n) f

example (n : ℕ) {A B : Stage C n} (f : A ⟶ B) [IsIso f] :
    stageCofibrations C n f :=
  stageCofibrations_of_isIso C f

example (n : ℕ) : (stageCofibrations C n).ContainsIdentities := inferInstance

example (n : ℕ) : (stageCofibrations C n).RespectsIso := inferInstance

example (n : ℕ) : (stageCofibrations C n).IsMultiplicative := inferInstance

example (n : ℕ) : (stageCofibrations C n).IsMultiplicative :=
  stageCofibrationsMultiplicative C n

example (n : ℕ) : (stageCofibrations C n).RespectsIso :=
  stageCofibrationsRespectsIso C n

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationStabilityTests
