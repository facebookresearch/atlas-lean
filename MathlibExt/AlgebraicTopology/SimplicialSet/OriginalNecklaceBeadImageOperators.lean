/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadImages

/-!
# Literal original interval operators of whole bead maps

The same original necklace operator restricts to the actual full bead
interval by subtracting its original initial image vertex. Both endpoint
maps, the entire simplex operator square and actual epi recognition are
retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

variable {T U : Data} (f : T ⟶ U) {a b : Fin (T.dimension + 1)} (h : IsBead T a b)

/-- The SAME original ordinal map on every vertex of the full source bead interval. -/
def beadImageOperator : ⦋length a b⦌ ⟶
    ⦋length (f.operator.toOrderHom a) (f.operator.toOrderHom b)⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨(f.operator.toOrderHom (embedding a b h.positive.le i)).val -
          (f.operator.toOrderHom a).val, by
        have hi := bead_image_bounds f h i
        change (f.operator.toOrderHom a).val ≤ _ ∧ _ ≤ (f.operator.toOrderHom b).val at hi
        dsimp [length]
        omega⟩
      monotone' := fun i j hij => by
        change _ - (f.operator.toOrderHom a).val ≤ _ - (f.operator.toOrderHom a).val
        exact Nat.sub_le_sub_right
          (f.operator.toOrderHom.monotone ((embedding a b h.positive.le).monotone hij)) _ }

/-- The same original interval operator begins at its actual original initial image. -/
theorem beadImageOperator_zero : (beadImageOperator f h).toOrderHom 0 = 0 := by
  apply Fin.ext
  change (f.operator.toOrderHom (embedding a b h.positive.le 0)).val -
    (f.operator.toOrderHom a).val = 0
  rw [embedding_zero, Nat.sub_self]

/-- The same original interval operator ends at its actual original terminal image. -/
theorem beadImageOperator_last :
    (beadImageOperator f h).toOrderHom (Fin.last (length a b)) =
      Fin.last (length (f.operator.toOrderHom a) (f.operator.toOrderHom b)) := by
  apply Fin.ext
  change (f.operator.toOrderHom (embedding a b h.positive.le (Fin.last (length a b)))).val -
    (f.operator.toOrderHom a).val = _
  rw [embedding_last]
  rfl

/-- The entire original operator square retains BOTH complete native interval maps. -/
theorem beadImageOperator_square :
    beadImageOperator f h ≫ operator (f.operator.toOrderHom a) (f.operator.toOrderHom b)
      (f.operator.toOrderHom.monotone h.positive.le) = operator a b h.positive.le ≫ f.operator := by
  ext i : 3
  apply Fin.ext
  change (f.operator.toOrderHom a).val +
      ((f.operator.toOrderHom (embedding a b h.positive.le i)).val -
        (f.operator.toOrderHom a).val) = (f.operator.toOrderHom (embedding a b h.positive.le i)).val
  have hi := (bead_image_bounds f h i).1
  change (f.operator.toOrderHom a).val ≤ _ at hi
  omega

/-- A surjective original necklace operator gives an actual full surjection on every source bead image. -/
theorem beadImageOperator_surjective (hf : Function.Surjective f.operator.toOrderHom) :
    Function.Surjective (beadImageOperator f h).toOrderHom := by
  intro j
  let z := embedding (f.operator.toOrderHom a) (f.operator.toOrderHom b)
    (f.operator.toOrderHom.monotone h.positive.le) j
  have hz : f.operator.toOrderHom a ≤ z ∧ z ≤ f.operator.toOrderHom b := by
    have hl := (embedding (f.operator.toOrderHom a) (f.operator.toOrderHom b)
      (f.operator.toOrderHom.monotone h.positive.le)).monotone (Fin.zero_le j)
    have hr := (embedding (f.operator.toOrderHom a) (f.operator.toOrderHom b)
      (f.operator.toOrderHom.monotone h.positive.le)).monotone (Fin.le_last j)
    rw [embedding_zero] at hl
    rw [embedding_last] at hr
    exact ⟨hl, hr⟩
  by_cases hza : z = f.operator.toOrderHom a
  · refine ⟨0, ?_⟩
    rw [beadImageOperator_zero]
    apply Fin.ext
    have he := congrArg Fin.val hza
    change (f.operator.toOrderHom a).val + j.val = (f.operator.toOrderHom a).val at he
    change 0 = j.val
    omega
  by_cases hzb : z = f.operator.toOrderHom b
  · refine ⟨Fin.last (length a b), ?_⟩
    rw [beadImageOperator_last]
    apply Fin.ext
    have he := congrArg Fin.val hzb
    change (f.operator.toOrderHom a).val + j.val = (f.operator.toOrderHom b).val at he
    change (f.operator.toOrderHom b).val - (f.operator.toOrderHom a).val = j.val
    omega
  obtain ⟨i, hi⟩ := hf z
  have hai : a ≤ i := by
    by_contra hai
    have hc := f.operator.toOrderHom.monotone (le_of_lt (not_le.mp hai))
    have he : z = f.operator.toOrderHom a := le_antisymm (hi.symm.le.trans hc) hz.1
    exact hza he
  have hib : i ≤ b := by
    by_contra hib
    have hc := f.operator.toOrderHom.monotone (le_of_lt (not_le.mp hib))
    have he : z = f.operator.toOrderHom b := le_antisymm hz.2 (hc.trans hi.le)
    exact hzb he
  let k : Fin (length a b + 1) := ⟨i.val - a.val, by
    dsimp [length]
    change a.val ≤ i.val at hai
    change i.val ≤ b.val at hib
    omega⟩
  have hk : embedding a b h.positive.le k = i := by
    apply Fin.ext
    change a.val + (i.val - a.val) = i.val
    change a.val ≤ i.val at hai
    omega
  refine ⟨k, ?_⟩
  apply Fin.ext
  change (f.operator.toOrderHom (embedding a b h.positive.le k)).val -
    (f.operator.toOrderHom a).val = j.val
  rw [hk, hi]
  change (f.operator.toOrderHom a).val + j.val - (f.operator.toOrderHom a).val = j.val
  omega

/-- The literal full bead-image operator is epi for the same actual vertex-surjective original map. -/
theorem beadImageOperator_epi (hf : Function.Surjective f.operator.toOrderHom) :
    Epi (beadImageOperator f h) :=
  (SimplexCategory.epi_iff_surjective (f := beadImageOperator f h)).mpr
    (beadImageOperator_surjective f h hf)

/-- The whole native bead square retains the SAME original necklace simplicial map. -/
theorem beadMap_image_square
    (hj : ∀ i ∈ T.joints, f.operator.toOrderHom i ∈ U.joints)
    (hab : f.operator.toOrderHom a < f.operator.toOrderHom b) :
    SSet.stdSimplex.map (beadImageOperator f h) ≫ beadMap.{u} (bead_image f h hj hab) =
      beadMap h ≫ f.map := by
  apply (cancel_mono (complex.{u} U.joints).ι).1
  rw [Category.assoc, beadMap_ι, Category.assoc, Morphism.map_ι, ← Category.assoc,
    beadMap_ι, ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg (fun g => SSet.stdSimplex.map g) (beadImageOperator_square f h)

end SSet.OriginalNecklace
