/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverAllCellPreimageWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCellInjection
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverCellHighVertices

/-!
# Full original all-cell open-complement injection

The SAME original high vertex is detected by its native rank outside
the old-stage preimage. Equality of the original full image words
therefore recovers the actual high-vertex label and every original
ordinal coefficient. No graph or weak conclusion is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for the actual full cell images. -/
private local instance coverQuiverForComplement : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- Full original image equality outside the old preimage recovers BOTH the original label and entire coefficient. -/
theorem coverAllCellMap_complement_injective (k n : ℕ)
    (a b : (coverAllCells V z k) _⦋n⦌)
    (ha : a ∉ ((coverRankStage V z k).preimage (coverAllCellMap V z k)).obj (op ⦋n⦌))
    (h : (coverAllCellMap V z k).app (op ⦋n⦌) a = (coverAllCellMap V z k).app (op ⦋n⦌) b) : a = b := by
  rcases a with ⟨a, c⟩
  rcases b with ⟨b, d⟩
  change (coverParentCell V z k a).app (op ⦋n⦌) c =
    (coverParentCell V z k b).app (op ⦋n⦌) d at h
  have hca : c ∉ ((coverRankStage V z k).preimage (coverParentCell V z k a)).obj (op ⦋n⦌) := ha
  obtain ⟨i, hai, hri⟩ := coverParentCell_high_vertex_exists V z k a n c hca
  have hv := congrArg (fun w => w.obj i) h
  have hbr : ¬ CoverVertex.rank V z (((coverParentCell V z k b).app (op ⦋n⦌) d).obj i) ≤ k :=
    fun hb => hri ((congrArg (CoverVertex.rank V z) hv).symm ▸ hb)
  have hbi := coverParentCell_vertex_eq_high V z k b n d i hbr
  have hab : a.val = b.val := hai.symm.trans (hv.trans hbi)
  have hl : a = b := Subtype.ext hab
  subst b
  have hc : c = d := coverParentCell_app_injective V z k a n h
  subst d
  rfl

end Quiver.FreeGroupoid.OriginalWords
