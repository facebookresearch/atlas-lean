/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCellPreimage

/-!
# Exact full original parent-cell coefficient injection

The actual original parent and high vertex have different native ranks.
Every ordinal coefficient is recovered from the SAME original word
vertex, so the full original parent cell is monic, including all of
its constant and degenerate coefficients.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating quiver for the complete coefficient injection. -/
private local instance coverQuiverForInjection : Quiver.{v} (CoverVertex V z) := coverQuiver V z

private lemma fin_two_cases (i : Fin 2) : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- The SAME actual original parent-generator source and target vertices are distinct. -/
lemma parentEdgeSource_ne_target (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    parentEdgeSource V z a ha ≠ parentEdgeTarget V z a ha := by
  unfold parentEdgeSource parentEdgeTarget
  cases parentEdge V z a ha with
  | inl _ =>
    change coverParent V z a ha ≠ a
    intro h
    have he := congrArg (CoverVertex.rank V z) h
    have hr := coverParent_rank V z a ha
    omega
  | inr _ =>
    change a ≠ coverParent V z a ha
    intro h
    have he := congrArg (CoverVertex.rank V z) h
    have hr := coverParent_rank V z a ha
    omega

/-- EVERY original coefficient of a parent cell is recovered by its SAME full native original word. -/
theorem coverParentCell_app_injective (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ) :
    Function.Injective ((coverParentCell V z k a).app (op ⦋n⦌)) := by
  intro c d h
  apply SSet.stdSimplex.ext
  intro i
  have hv := congrArg (fun w => w.obj i) h
  rcases fin_two_cases (c i) with hc | hc <;> rcases fin_two_cases (d i) with hd | hd
  · exact hc.trans hd.symm
  · have hs := coverParentCell_obj_zero V z k a n c i hc
    have ht := coverParentCell_obj_one V z k a n d i hd
    have he := hs.symm.trans (hv.trans ht)
    exact False.elim (parentEdgeSource_ne_target V z a.val (coverCellLabel_pos V z k a) he)
  · have hs := coverParentCell_obj_one V z k a n c i hc
    have ht := coverParentCell_obj_zero V z k a n d i hd
    have he := ht.symm.trans (hv.symm.trans hs)
    exact False.elim (parentEdgeSource_ne_target V z a.val (coverCellLabel_pos V z k a) he)
  · exact hc.trans hd.symm

end Quiver.FreeGroupoid.OriginalWords
