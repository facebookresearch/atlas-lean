/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Quillen functors and Brown's lemma

A left Quillen functor preserves weak equivalences between cofibrant objects,
and a right Quillen functor preserves weak equivalences between fibrant objects.
The second assertion is the first in the opposite model categories.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

/-- A left Quillen functor preserves weak equivalences between cofibrant objects. -/
theorem map_weakEquivalence_of_cofibrant {X Y : C} (f : X ⟶ Y)
    [IsQuillenAdjunction adj] [WeakEquivalence f]
    [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (L.map f) := by
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  have hMap := (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations
  have : WeakEquivalence (L.map h.i) :=
    (weakEquivalence_iff _).mpr (hMap h.i (mem_trivialCofibrations h.i)).2
  have : WeakEquivalence (L.map h.s) :=
    (weakEquivalence_iff _).mpr (hMap h.s (mem_trivialCofibrations h.s)).2
  have hs_p : L.map h.s ≫ L.map h.p = 𝟙 (L.obj Y) := by
    rw [← L.map_comp, h.s_p, L.map_id]
  have : WeakEquivalence (L.map h.p) := weakEquivalence_of_precomp_of_fac hs_p
  rw [← h.fac, L.map_comp]
  infer_instance

/-- A right Quillen functor preserves weak equivalences between fibrant objects. -/
theorem map_weakEquivalence_of_fibrant {X Y : D} (f : X ⟶ Y)
    [IsQuillenAdjunction adj] [WeakEquivalence f]
    [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (R.map f) := by
  have : IsCofibrant (Opposite.op X) :=
    (isCofibrant_iff_of_isInitial (terminal.from X).op
      (initialOpOfTerminal terminalIsTerminal)).mpr inferInstance
  have : IsCofibrant (Opposite.op Y) :=
    (isCofibrant_iff_of_isInitial (terminal.from Y).op
      (initialOpOfTerminal terminalIsTerminal)).mpr inferInstance
  exact (weakEquivalences_op_iff (R.map f)).mp
    (map_weakEquivalence_of_cofibrant (adj := adj.op) f.op)

end CategoryTheory.Adjunction.IsQuillenAdjunction
