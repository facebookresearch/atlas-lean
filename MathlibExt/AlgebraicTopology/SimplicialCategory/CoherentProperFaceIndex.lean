/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialObject.Matching

/-!
# Actual proper-injection indexing for coherent right-cube latching

These are the original matching-index objects and structured-arrow
morphisms. Every proper original injection factors through a genuine
coface, and degree zero has no index object. Only neutral categorical
and simplex APIs are used; no latching or model outcome is assumed.
-/

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.ProperFaceIndex

/-- The actual original coface as an object of the proper-injection matching index. -/
def face (n : ℕ) (i : Fin (n + 2)) : SimplicialObject.matchingIndex (n + 1) :=
  ⟨StructuredArrow.mk (SimplexCategory.δ i).op,
    ⟨by change Mono (SimplexCategory.δ i); infer_instance,
      by change n < n + 1; exact Nat.lt_succ_self n⟩⟩

/-- The actual structured-arrow map determined by a whole original factorization of two proper injections. -/
def hom {n : ℕ} (a b : SimplicialObject.matchingIndex n)
    (g : b.obj.right.unop ⟶ a.obj.right.unop) (hg : g ≫ a.obj.hom.unop = b.obj.hom.unop) : a ⟶ b :=
  ObjectProperty.homMk (StructuredArrow.homMk g.op (by
    apply Quiver.Hom.unop_inj
    exact hg))

/-- The actual index map retains exactly the same prescribed original ordinal operator. -/
theorem hom_right {n : ℕ} (a b : SimplicialObject.matchingIndex n)
    (g : b.obj.right.unop ⟶ a.obj.right.unop) (hg : g ≫ a.obj.hom.unop = b.obj.hom.unop) :
    (hom a b g hg).hom.right = g.op := rfl

/-- A genuine original proper injection is not surjective on its original ordinal labels. -/
theorem not_surjective {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    ¬Function.Surjective a.obj.hom.unop.toOrderHom := by
  intro h
  let : Epi a.obj.hom.unop := (SimplexCategory.epi_iff_surjective (f := a.obj.hom.unop)).mpr h
  exact (Nat.not_le_of_lt a.property.2) (SimplexCategory.len_le_of_epi a.obj.hom.unop)

/-- Every actual original proper injection in positive degree factors through one genuine supplied coface. -/
theorem factor_face {n : ℕ} (a : SimplicialObject.matchingIndex (n + 1)) :
    ∃ (i : Fin (n + 2)) (θ : a.obj.right.unop ⟶ ⦋n⦌), a.obj.hom.unop = θ ≫ SimplexCategory.δ i :=
  SimplexCategory.eq_comp_δ_of_not_surjective a.obj.hom.unop (not_surjective a)

/-- Resolving degree zero has literally no proper-injection index object. -/
theorem zero_elim (a : SimplicialObject.matchingIndex 0) : False := Nat.not_lt_zero _ a.property.2

end CategoryTheory.CoherentRealization.ProperFaceIndex
