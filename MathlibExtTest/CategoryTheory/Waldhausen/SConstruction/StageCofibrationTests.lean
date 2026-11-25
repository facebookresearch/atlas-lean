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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibration

/-!
# Finite-stage cofibration tests

Focused public-API checks for the zero-row accessors, the exact orientation
of the successive pushout witness, and vacuity in degree zero.  These tests
make no pointwise-equivalence or Waldhausen-instance claim.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- The zero-row object is the literal interval `(0,j)`. -/
example {n : ℕ} (A : Stage C n) (j : Fin (n + 1)) :
    A.zeroRowObj j = A.obj.obj (interval 0 j (Fin.zero_le _)) :=
  rfl

/-- Successive zero-row maps use `(0,i) ⟶ (0,i+1)` in that order. -/
example {n : ℕ} (A : Stage C n) (i : Fin n) :
    A.zeroRowSuccMap i =
      A.obj.map (horiz (Fin.zero_le _) i.castSucc_le_succ) :=
  rfl

/-- A stage-map component is evaluated at the literal zero-row interval. -/
example {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    (j : Fin (n + 1)) :
    Stage.zeroRowApp f j = f.hom.app (interval 0 j (Fin.zero_le _)) :=
  rfl

/-- Membership exposes the genuine old-next/new-previous pushout and its
cofibrant induced map to the new next object. -/
example {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    (hf : stageCofibrations C n f) (i : Fin n) :
    ∃ (P : C)
      (inl : A.zeroRowObj i.succ ⟶ P)
      (inr : B.zeroRowObj i.castSucc ⟶ P)
      (d : P ⟶ B.zeroRowObj i.succ),
      IsPushout (A.zeroRowSuccMap i) (Stage.zeroRowApp f i.castSucc)
          inl inr ∧
        inl ≫ d = Stage.zeroRowApp f i.succ ∧
        inr ≫ d = B.zeroRowSuccMap i ∧
        IsCofibration d :=
  hf i

/-- Every degree-zero stage morphism satisfies the successive-step condition
because there is no `Fin 0` index. -/
example {A B : Stage C 0} (f : A ⟶ B) : stageCofibrations C 0 f := by
  intro i
  exact Fin.elim0 i

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageCofibrationTests
