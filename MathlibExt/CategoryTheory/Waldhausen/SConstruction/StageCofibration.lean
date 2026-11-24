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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage

/-!
# Cofibrations in finite Waldhausen stages

The classical cofibrations in `S_n C` are defined by successive induced
pushout maps along the zero row.  For a stage map `A ⟶ B` and
`i : Fin n`, the required map has source

`A(0,i+1) ⊔_[A(0,i)] B(0,i)`

and target `B(0,i+1)`.  Its membership in the base cofibrations is part of
the existential pushout witness below.

This condition is stronger than pointwise cofibration of the components. The
file defines only the morphism property: it supplies no Waldhausen structure
on `Stage C n`, multiplicativity or pushout closure theorem, extension-stage
membership theorem, homotopy, realization, or additivity result.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

namespace Stage

/-- The object in the zero row of a stage at column `j`. -/
def zeroRowObj {n : ℕ} (A : Stage C n) (j : Fin (n + 1)) : C :=
  A.obj.obj (interval 0 j (Fin.zero_le _))

/-- The successive zero-row map from column `i` to column `i+1`. -/
def zeroRowSuccMap {n : ℕ} (A : Stage C n) (i : Fin n) :
    A.zeroRowObj i.castSucc ⟶ A.zeroRowObj i.succ :=
  A.obj.map (horiz (Fin.zero_le _) i.castSucc_le_succ)

/-- The component of a stage morphism at the zero-row object in column `j`. -/
def zeroRowApp {n : ℕ} {A B : Stage C n} (f : A ⟶ B)
    (j : Fin (n + 1)) : A.zeroRowObj j ⟶ B.zeroRowObj j :=
  f.hom.app (interval 0 j (Fin.zero_le _))

end Stage

variable (C)

/-- Genuine Waldhausen `S_n` cofibrations.

At every successive zero-row step, a pushout of the old stage map along the
previous component must admit the canonical induced map to the new next
object, and that induced map must be a cofibration in `C`.  The definition is
existential and does not select pushout data. -/
def stageCofibrations (n : ℕ) : MorphismProperty (Stage C n) :=
  fun A B f => ∀ i : Fin n,
    ∃ (P : C)
      (inl : A.zeroRowObj i.succ ⟶ P)
      (inr : B.zeroRowObj i.castSucc ⟶ P)
      (d : P ⟶ B.zeroRowObj i.succ),
      IsPushout (A.zeroRowSuccMap i) (Stage.zeroRowApp f i.castSucc)
          inl inr ∧
        inl ≫ d = Stage.zeroRowApp f i.succ ∧
        inr ≫ d = B.zeroRowSuccMap i ∧
        IsCofibration d

end CategoryTheory.Waldhausen.SConstruction
