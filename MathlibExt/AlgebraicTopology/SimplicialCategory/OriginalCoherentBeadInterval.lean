/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentIntervalFaceCover
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentUnit

/-!
# Full original endpoint intervals as coherent beads

The same complete interval is read through its consecutive original
ordinal vertices. The full Hom isomorphism reuses the native coherent
path image and preimage, retaining every coefficient and operator.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

open SimplicialEnrichment

variable {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)

/-- The exact number of original edges in the endpoint interval. -/
def length : ℕ := b.val - a.val

/-- The consecutive original interval embedding. -/
def embedding : Fin (length a b + 1) ↪o Fin (n + 1) where
  toFun i := ⟨a.val + i.val, by
    have hi := i.isLt
    have hb := b.isLt
    have h : a.val ≤ b.val := hab
    dsimp [length] at hi
    omega⟩
  inj' _ _ h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  map_rel_iff' := by
    intro i j
    change a.val + i.val ≤ a.val + j.val ↔ i.val ≤ j.val
    omega

/-- The first original interval vertex is the original source. -/
theorem embedding_zero : embedding a b hab 0 = a :=
  Fin.ext (Nat.add_zero a.val)

/-- The last original interval vertex is the original target. -/
theorem embedding_last : embedding a b hab (Fin.last (length a b)) = b := by
  apply Fin.ext
  change a.val + (b.val - a.val) = b.val
  have h : a.val ≤ b.val := hab
  omega

/-- The original enriched operator uses the same interval embedding. -/
def operator : ⦋length a b⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk (embedding a b hab).toOrderHom

/-- The same original embedding at the coefficient universe. -/
def liftedEmbedding : ULift.{u} (Fin (length a b + 1)) ↪o ULift.{u} (Fin (n + 1)) where
  toFun i := ULift.up (embedding a b hab i.down)
  inj' _ _ h := ULift.ext ((embedding a b hab).injective (congrArg ULift.down h))
  map_rel_iff' := by
    intro i j
    exact (embedding a b hab).map_rel_iff

/-- Every original vertex between the supplied endpoints has its actual interval preimage. -/
theorem coverage (x : ULift.{u} (Fin (n + 1)))
    (ha : liftedEmbedding.{u} a b hab (ULift.up 0) ≤ x)
    (hb : x ≤ liftedEmbedding.{u} a b hab (ULift.up (Fin.last (length a b)))) :
    x ∈ Set.range (liftedEmbedding.{u} a b hab) := by
  have hax : a.val ≤ x.down.val := by
    change (embedding a b hab 0).val ≤ x.down.val at ha
    rw [embedding_zero] at ha
    exact ha
  have hxb : x.down.val ≤ b.val := by
    change x.down.val ≤ (embedding a b hab (Fin.last (length a b))).val at hb
    rw [embedding_last] at hb
    exact hb
  let i : Fin (length a b + 1) := ⟨x.down.val - a.val, by
    dsimp [length]
    omega⟩
  refine ⟨ULift.up i, ?_⟩
  apply ULift.ext
  apply Fin.ext
  change a.val + (x.down.val - a.val) = x.down.val
  omega

/-- The original whole Hom isomorphism before its exact endpoint readback. -/
def wholeHomIso :
    nerve (SimplicialThickening.Path
      (ULift.up.{u} (0 : Fin (length a b + 1)))
      (ULift.up.{u} (Fin.last (length a b)))) ≅
    nerve (SimplicialThickening.Path
      (liftedEmbedding.{u} a b hab (ULift.up 0))
      (liftedEmbedding.{u} a b hab (ULift.up (Fin.last (length a b))))) :=
  IntervalFaceCover.wholeHomIso (liftedEmbedding a b hab) _ _ (coverage a b hab)

/-- Both original endpoint equations in the coefficient universe. -/
theorem lifted_zero : liftedEmbedding.{u} a b hab (ULift.up 0) = ULift.up a :=
  ULift.ext (embedding_zero a b hab)

/-- The terminal original coefficient endpoint equation. -/
theorem lifted_last :
    liftedEmbedding.{u} a b hab (ULift.up (Fin.last (length a b))) = ULift.up b :=
  ULift.ext (embedding_last a b hab)

/-- The entire original interval Hom is read as a full zero-to-last bead Hom. -/
def homIso :
    nerve (SimplicialThickening.Path
      (ULift.up.{u} (0 : Fin (length a b + 1)))
      (ULift.up.{u} (Fin.last (length a b)))) ≅
        nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) :=
  wholeHomIso a b hab ≪≫
    eqToIso (congrArg₂
      (fun x y : ULift.{u} (Fin (n + 1)) => nerve (SimplicialThickening.Path x y))
      (lifted_zero a b hab) (lifted_last a b hab))

/-- The full interval forward map is the same original coherent simplex operator,
followed by the literal original endpoint equalities. -/
theorem homIso_hom :
    (homIso.{u} a b hab).hom =
      (coherentSimplexMap (operator a b hab)).map
        (SimplicialThickening.mk (ULift.up 0))
        (SimplicialThickening.mk (ULift.up (Fin.last (length a b)))) ≫
      eqToHom (congrArg₂
        (fun x y : ULift.{u} (Fin (n + 1)) => nerve (SimplicialThickening.Path x y))
        (lifted_zero a b hab) (lifted_last a b hab)) := by
  rw [homIso, Iso.trans_hom]
  congr 1

private theorem coefficient_surjective {X Y : SSet.{u}} (e : X ≅ Y)
    (q : SimplexCategoryᵒᵖ) (p : Y.obj q) :
    ∃ r, e.hom.app q r = p := by
  refine ⟨e.inv.app q p, ?_⟩
  have h := ConcreteCategory.congr_hom (congr_app e.inv_hom_id q) p
  exact h

/-- Every full original scalar generator is in its same full endpoint-interval image. -/
theorem exists_original_coefficient {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))).obj q) :
    ∃ r, (homIso a b hab).hom.app q r = p := by
  exact coefficient_surjective (homIso a b hab) q p

end CategoryTheory.CoherentRealization.OriginalBeadInterval
