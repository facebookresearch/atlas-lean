/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadCoverage

/-!
# Full scalar lifting and detection by actual original beads

Every entire simplex of a positive original necklace lifts to one of its
same whole native bead intervals. Consequently maps out of the original
necklace are determined by their restrictions to all original full beads.
The statement retains the original universe and every original
simplicial-set map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- The same original full interval simplex has an actual complete native preimage. -/
theorem exists_bead_simplex_preimage {T : Data} {a b : Fin (T.dimension + 1)}
    (h : IsBead T a b) {d : ℕ} (s : (Δ[T.dimension] : SSet.{u}) _⦋d⦌)
    (hs : ∀ j, a ≤ s j ∧ s j ≤ b) :
    ∃ t : (Δ[length a b] : SSet.{u}) _⦋d⦌,
      (SSet.stdSimplex.map (operator a b h.positive.le)).app (op ⦋d⦌) t = s := by
  let t : (Δ[length a b] : SSet.{u}) _⦋d⦌ :=
    stdSimplex.objMk (n := ⦋length a b⦌) (m := op ⦋d⦌)
      (show Fin (d + 1) →o Fin (length a b + 1) from
        { toFun := fun j => ⟨(s j).val - a.val, by
            have hj := hs j
            change a.val ≤ (s j).val ∧ (s j).val ≤ b.val at hj
            dsimp [length]
            omega⟩
          monotone' := fun i j hij => by
            change (s i).val - a.val ≤ (s j).val - a.val
            exact Nat.sub_le_sub_right (stdSimplex.monotone_apply s hij) _ })
  refine ⟨t, ?_⟩
  apply stdSimplex.ext
  intro j
  apply Fin.ext
  change a.val + ((s j).val - a.val) = (s j).val
  have hj := (hs j).1
  change a.val ≤ (s j).val at hj
  omega

/-- Every full native source simplex is in the actual image of an entire original bead map. -/
theorem exists_native_bead_preimage (T : Data) (hn : 0 < T.dimension)
    {d : ℕ} (s : T.object.{u} _⦋d⦌) :
    ∃ (a b : Fin (T.dimension + 1)) (h : IsBead T a b)
      (t : (Δ[length a b] : SSet.{u}) _⦋d⦌), (beadMap h).app (op ⦋d⦌) t = s := by
  obtain ⟨a, b, h, hs⟩ := simplex_in_bead T hn s.val s.property
  obtain ⟨t, ht⟩ := exists_bead_simplex_preimage h s.val hs
  exact ⟨a, b, h, t, Subtype.ext ht⟩

/-- The entire original input maps are determined by their SAME restrictions to every full bead. -/
theorem hom_ext_of_beads (T : Data) (hn : 0 < T.dimension) {K : SSet.{u}}
    {f g : T.object ⟶ K}
    (h : ∀ (a b : Fin (T.dimension + 1)) (h : IsBead T a b), beadMap h ≫ f = beadMap h ≫ g) :
    f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨a, b, hb, t, ht⟩ := exists_native_bead_preimage T hn s
  have he := ConcreteCategory.congr_hom (congr_app (h a b hb) (op ⦋d⦌)) t
  change f.app (op ⦋d⦌) ((beadMap hb).app (op ⦋d⦌) t) =
    g.app (op ⦋d⦌) ((beadMap hb).app (op ⦋d⦌) t) at he
  simpa only [ht] using he

end SSet.OriginalNecklace
