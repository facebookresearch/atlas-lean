/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeFullPath

/-!
# Actual original cylinder charts of the right cube

The original path is retained at cylinder zero and its full interval at
cylinder one. Monotonicity gives a genuine ordinary cylinder functor,
whose nerve is the corresponding whole simplicial prism. The original
front-composition quotient is not yet assumed to preserve this chart.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeCylinder
open PathLastMaximum RightCubeFullPath
variable {n : ℕ}

/-- The actual original last path selected by the supplied original cylinder label. -/
def select (i : Fin (n + 1)) (p : LastPath.{u} i) (t : Fin 2) : LastPath.{u} i :=
  if t = 0 then p else fullPath i

/-- The original cylinder zero retains its entire supplied last path. -/
theorem select_zero (i : Fin (n + 1)) (p : LastPath.{u} i) : select i p 0 = p := by
  simp only [select, ite_true]

/-- The original cylinder one is the entire full interval path at the same supplied original source. -/
theorem select_one (i : Fin (n + 1)) (p : LastPath.{u} i) : select i p 1 = fullPath i := by
  simp only [select, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]

/-- Original path inclusions and increasing cylinder labels preserve the actual selected path. -/
theorem select_mono (i : Fin (n + 1)) {p q : LastPath.{u} i} (f : p ⟶ q)
    {t s : Fin 2} (h : t ≤ s) : (select i p t).I ⊆ (select i q s).I := by
  by_cases hs : s = 0
  · have ht : t = 0 := le_antisymm (hs ▸ h) (Fin.zero_le _)
    rw [ht, hs, select_zero, select_zero]
    exact f.hom.down.down
  · by_cases ht : t = 0
    · rw [ht, select_zero]
      simp only [select, ite_eq_right hs]
      exact path_le_full i p
    · simp only [select, ite_eq_right ht, ite_eq_right hs]
      exact le_rfl

/-- The genuine ordinary cylinder functor on the actual original last-path category. -/
def functor (i : Fin (n + 1)) : LastPath.{u} i × ULift.{u} (Fin 2) ⥤ LastPath.{u} i where
  obj x := select i x.1 x.2.down
  map f := ⟨homOfLE (select_mono i f.1 f.2.down.down)⟩

/-- The actual whole original cylinder chart on a path chain and scalar interval simplex. -/
def chain (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} i)).obj q) (t : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{u}).obj q) :
    (nerve (LastPath.{u} i)).obj q :=
  p.prod' ((SSet.stdSimplex.isoNerve.{u} 1).hom.app q t) ⋙ functor i

/-- Every original scalar vertex of the cylinder chart is the corresponding actual original selected path. -/
theorem chain_obj (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} i)).obj q) (t : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{u}).obj q)
    (j : Fin (q.unop.len + 1)) : (chain i p t).obj j = select i (p.obj j) (t.down.toOrderHom j) := rfl

end CategoryTheory.CoherentRealization.RightCubeCylinder
