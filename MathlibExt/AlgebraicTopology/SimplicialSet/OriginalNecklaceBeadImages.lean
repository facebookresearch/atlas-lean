/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadSimplexLifts
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAllMaps

/-!
# Same original bead intervals under joint-preserving maps

A whole original source bead whose two vertices have distinct images
maps into the entire actual target bead between those image joints.
The result follows from the SAME original full simplex containment,
without assuming anything about the target input's weak class.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

variable {T U : Data} (f : T ⟶ U)

/-- Every original positive bead maps to the exact full target bead when its images are distinct. -/
theorem bead_image {a b : Fin (T.dimension + 1)} (h : IsBead T a b)
    (hj : ∀ i ∈ T.joints, f.operator.toOrderHom i ∈ U.joints)
    (hab : f.operator.toOrderHom a < f.operator.toOrderHom b) :
    IsBead U (f.operator.toOrderHom a) (f.operator.toOrderHom b) := by
  refine ⟨hj a h.source, hj b h.target, hab, ?_⟩
  intro j hjU
  let s : (Δ[length a b] : SSet.{0}) _⦋length a b⦌ := SSet.yonedaEquiv (𝟙 _)
  have hs := f.lands (op ⦋length a b⦌) (bead_interval_mem h s)
  have hc := (mem_complex_iff U.joints _).mp hs j hjU
  rcases hc with hc | hc
  · apply Or.inr
    have ht := hc (Fin.last (length a b))
    change f.operator.toOrderHom (embedding a b h.positive.le (Fin.last (length a b))) ≤ j at ht
    rw [embedding_last] at ht
    exact ht
  · apply Or.inl
    have ht := hc 0
    change j ≤ f.operator.toOrderHom (embedding a b h.positive.le 0) at ht
    rw [embedding_zero] at ht
    exact ht

/-- The full image of every source bead lies between its SAME actual image endpoints. -/
theorem bead_image_bounds {a b : Fin (T.dimension + 1)} (h : IsBead T a b)
    (i : Fin (length a b + 1)) :
    f.operator.toOrderHom a ≤ f.operator.toOrderHom (embedding a b h.positive.le i) ∧
      f.operator.toOrderHom (embedding a b h.positive.le i) ≤ f.operator.toOrderHom b := by
  have hl := (embedding a b h.positive.le).monotone (Fin.zero_le i)
  have hr := (embedding a b h.positive.le).monotone (Fin.le_last i)
  rw [embedding_zero] at hl
  rw [embedding_last] at hr
  exact ⟨f.operator.toOrderHom.monotone hl, f.operator.toOrderHom.monotone hr⟩

/-- The SAME full source bead is collapsed constantly when its original image endpoints coincide. -/
theorem bead_collapsed {a b : Fin (T.dimension + 1)} (h : IsBead T a b)
    (hab : f.operator.toOrderHom a = f.operator.toOrderHom b)
    (i : Fin (length a b + 1)) :
    f.operator.toOrderHom (embedding a b h.positive.le i) = f.operator.toOrderHom a := by
  have hc := bead_image_bounds f h i
  exact le_antisymm (hc.2.trans hab.symm.le) hc.1

end SSet.OriginalNecklace
