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
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # The actual homology tail preserves a proved comparison of cochain maps -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A true homology-tail formula and a true cochain-map comparison determine their actual composite in all degrees. -/
def liftedTailComposition {A B D : CochainComplex C ℕ}
    (e : A ⟶ B) (f : B ⟶ D) (t : A ⟶ D) (n : ℕ)
    (tail : B.homology n ⟶ D.homology n)
    (htail : tail = homologyMap f n) (hcomp : e ≫ f = t) :
    PLift (homologyMap e n ≫ tail = homologyMap t n) := by
  refine ⟨?_⟩
  rw [htail, ← homologyMap_comp, hcomp]

end HomologicalComplex
