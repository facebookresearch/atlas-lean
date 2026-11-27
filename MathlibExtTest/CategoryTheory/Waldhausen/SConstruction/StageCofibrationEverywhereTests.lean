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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationEverywhere

/-! # Tests for every-cell stage cofibrations -/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationEverywhereTests

open _root_.CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example :
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).IsStableUnderCobaseChange :=
  inferInstance

example {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C b.len) (x : Ar a.len) :
    ((reindexStage α).obj A).obj.obj x =
      A.obj.obj ((indexFunctor α).obj x) := by
  simp

example {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrationsEverywhere C n f) :
    stageCofibrations C n f :=
  stageCofibrations_of_everywhere C hf

example {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j k : Fin (n + 1)}
    (hij hij' : i ≤ j) (hjk hjk' : j ≤ k) :
    IsStageCofibrationCell C f hij hjk ↔
      IsStageCofibrationCell C f hij' hjk' :=
  IsStageCofibrationCell.proof_irrel C f hij hij' hjk hjk'

example {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B)
    (hf : stageCofibrationsEverywhere C b.len f) :
    stageCofibrationsEverywhere C a.len ((reindexStage α).map f) :=
  stageCofibrationsEverywhere_of_reindexStage C α f hf

example {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j k l : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (h₁ : IsStageCofibrationCell C f hij hjk)
    (h₂ : IsStageCofibrationCell C f (hij.trans hjk) hkl) :
    IsStageCofibrationCell C f hij (hjk.trans hkl) :=
  IsStageCofibrationCell.paste_horiz C f hij hjk hkl h₁ h₂

example {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j : Fin (n + 1)} (hij : i ≤ j) (hjj : j ≤ j) :
    IsStageCofibrationCell C f hij hjj :=
  IsStageCofibrationCell.refl C f hij hjj

example {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f)
    {j k : Fin (n + 1)} (hjk : j ≤ k) :
    IsStageCofibrationCell C f (Fin.zero_le j) hjk :=
  zeroRowCell_of_stageCofibrations C hf hjk

example {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    (hzero : IsStageCofibrationCell C f (Fin.zero_le j) hjk) :
    IsStageCofibrationCell C f hij hjk :=
  IsStageCofibrationCell.of_zeroRow C f hij hjk hzero

example {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f) :
    stageCofibrationsEverywhere C n f :=
  stageCofibrationsEverywhere_of_stageCofibrations C hf

example {n : ℕ} {A B : Stage C n} (f : A ⟶ B) :
    stageCofibrationsEverywhere C n f ↔ stageCofibrations C n f :=
  stageCofibrationsEverywhere_iff_stageCofibrations C f

example {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B)
    (hf : stageCofibrations C b.len f) :
    stageCofibrations C a.len ((reindexStage α).map f) :=
  stageCofibrations_of_reindexStage C α f hf

example {n : ℕ} (A : Stage C n) :
    stageCofibrations C n (𝟙 A) :=
  stageCofibrations_id C A

example {n : ℕ} {A B : Stage C n} (f : A ⟶ B) [IsIso f] :
    stageCofibrations C n f :=
  stageCofibrations_of_isIso C f

example (n : ℕ) : (stageCofibrations C n).ContainsIdentities := inferInstance

example (n : ℕ) : (stageCofibrations C n).RespectsIso := inferInstance

example {n : ℕ} {A B D : Stage C n} (f : A ⟶ B) (g : B ⟶ D)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    (hf : IsStageCofibrationCell C f hij hjk)
    (hg : IsStageCofibrationCell C g hij hjk) :
    IsStageCofibrationCell C (f ≫ g) hij hjk :=
  IsStageCofibrationCell.comp C f g hij hjk hf hg

example {n : ℕ} {A B D : Stage C n} (f : A ⟶ B) (g : B ⟶ D)
    (hf : stageCofibrations C n f) (hg : stageCofibrations C n g) :
    stageCofibrations C n (f ≫ g) :=
  stageCofibrations_comp C f g hf hg

example (n : ℕ) : (stageCofibrations C n).IsMultiplicative := inferInstance

example {n : ℕ} {A B : Stage C n} {f : A ⟶ B}
    (hf : stageCofibrations C n f) (x : Ar n) :
    IsCofibration (f.hom.app x) :=
  stageCofibrations_app C hf x

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationEverywhereTests
