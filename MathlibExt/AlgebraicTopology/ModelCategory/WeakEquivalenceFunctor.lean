/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Brown's lemma for functors on cofibrant objects

A functor that sends trivial cofibrations to weak equivalences sends weak
equivalences between cofibrant objects to weak equivalences. The proof uses
the original cofibrant Brown factorization and requires no adjunction.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]

/-- Brown's factorization proves weak preservation between the two original
cofibrant endpoints from trivial-cofibration preservation alone. -/
theorem map_weakEquivalence_of_cofibrant (F : C ⥤ D)
    (hF : trivialCofibrations C ≤ (weakEquivalences D).inverseImage F)
    {X Y : C} (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f] :
    WeakEquivalence (F.map f) := by
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  let : WeakEquivalence (F.map h.i) :=
    (weakEquivalence_iff _).mpr (hF h.i (mem_trivialCofibrations h.i))
  let : WeakEquivalence (F.map h.s) :=
    (weakEquivalence_iff _).mpr (hF h.s (mem_trivialCofibrations h.s))
  have hs : F.map h.s ≫ F.map h.p = 𝟙 (F.obj Y) := by
    rw [← F.map_comp, h.s_p, F.map_id]
  let : WeakEquivalence (F.map h.p) := weakEquivalence_of_precomp_of_fac hs
  rw [← h.fac, F.map_comp]
  infer_instance

end CategoryTheory.Functor
