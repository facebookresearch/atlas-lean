/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Opposites of composable arrows

This file exposes the canonical reversal through `opEquivalence` together with object/map formulas.
-/

@[expose] public section

namespace CategoryTheory.ComposableArrows

universe v u u₁ v₁ u₂ v₂

variable {C : Type u} [Category.{v} C]

/-- The opposite of an `n`-composable arrow in `C`, as an `n`-composable arrow in `Cᵒᵖ`. -/
noncomputable def op {n : ℕ} (S : ComposableArrows C n) : ComposableArrows Cᵒᵖ n :=
  (opEquivalence C n).functor.obj (Opposite.op S)

/-- The `i`-th object of `S.op` is the opposite of the `S`-object at `i.rev`. -/
@[simp]
lemma op_obj {n : ℕ} (S : ComposableArrows C n) (i : Fin (n + 1)) :
    S.op.obj i = Opposite.op (S.obj i.rev) := by
  simp [op]

/-- The action of `S.op` on `f` is the opposite of the action of `S` on the reversed inequality. -/
@[simp]
lemma op_map {n : ℕ} (S : ComposableArrows C n) {i j : Fin (n + 1)} (f : i ⟶ j) :
    S.op.map f = (S.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).op := by
  simp only [op]
  congr
  simp

/-- The composable arrow in `C` underlying an `n`-composable arrow in `Cᵒᵖ`, via `opEquivalence`. -/
noncomputable def unop {n : ℕ} (S : ComposableArrows Cᵒᵖ n) :
    ComposableArrows C n :=
  Opposite.unop ((opEquivalence C n).inverse.obj S)

/-- The `i`-th object of `S.unop` is the unopposite of the `S`-object at `i.rev`. -/
@[simp]
lemma unop_obj {n : ℕ} (S : ComposableArrows Cᵒᵖ n)
    (i : Fin (n + 1)) :
    S.unop.obj i = Opposite.unop (S.obj i.rev) := by
  simp [unop]

/-- The action of `S.unop` on `f` is the unopposite of the action of `S` on the
    reversed inequality. -/
@[simp]
lemma unop_map {n : ℕ} (S : ComposableArrows Cᵒᵖ n)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    S.unop.map f =
      (S.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).unop := by
  simp only [unop]
  congr
  simp

/-- The unit isomorphism `S.op.unop ≅ S` supplied by `opEquivalence`. -/
noncomputable abbrev opUnop {n : ℕ} (S : ComposableArrows C n) :
    S.op.unop ≅ S :=
  Iso.unop ((opEquivalence C n).unitIso.app (Opposite.op S))

/-- The counit isomorphism `S.unop.op ≅ S` supplied by `opEquivalence`. -/
noncomputable abbrev unopOp {n : ℕ} (S : ComposableArrows Cᵒᵖ n) :
    S.unop.op ≅ S :=
  (opEquivalence C n).counitIso.app S

variable {C' : Type u₁} {B' : Type u₂} [Category.{v₁} C'] [Category.{v₂} B']

/-- Reversal commutes with whiskering a composable arrow. -/
theorem op_mapFunctor (H : C' ⥤ B') (n : ℕ) (X : ComposableArrows C' n) :
    ComposableArrows.op (X ⋙ H) = ComposableArrows.op X ⋙ H.op := by
  have h_obj : ∀ i : Fin (n + 1),
      (ComposableArrows.op (X ⋙ H)).obj i =
        (ComposableArrows.op X ⋙ H.op).obj i := fun i => by
    simp [ComposableArrows.op_obj]
  refine ComposableArrows.ext h_obj (fun i hi => ?_)
  refine (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).mpr ?_
  simp only [ComposableArrows.map', ComposableArrows.op_map, Functor.comp_map]
  refine heq_of_eq (congrArg (fun f => (H.map f).op) ?_)
  exact congrArg X.map (Subsingleton.elim _ _)

end CategoryTheory.ComposableArrows
