/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentNormalPath
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadCoefficientGluing

/-!
# Complete original coefficient flags on concatenated necklaces

Every scalar flag is the union of the entire original prefix and suffix
images. The original pivot, endpoints and all scalar operators are
retained literally.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.ConcatFlags

open OriginalBead.TerminalFlag
open SSet.OriginalTwoBead.OrdinalCharts

/-- The complete original lifted prefix operator on every coefficient vertex. -/
abbrev prefixLift (p q : ℕ) : ULift.{u} (Fin (p + 1)) →o ULift.{u} (Fin (p + q + 1)) :=
  (prefixOperator p q).toOrderHom.uliftMap

/-- The complete original lifted suffix operator on every coefficient vertex. -/
abbrev suffixLift (p q : ℕ) : ULift.{u} (Fin (q + 1)) →o ULift.{u} (Fin (p + q + 1)) :=
  (suffixOperator p q).toOrderHom.uliftMap

/-- The entire original scalar coefficient is glued at every original flag. -/
abbrev coefficient {p q : ℕ} {d : SimplexCategoryᵒᵖ}
    (l : (coefficientObject.{u} p).obj d) (r : (coefficientObject.{u} q).obj d) :
    (coefficientObject.{u} (p + q)).obj d :=
  (OriginalBead.CoefficientGluing.map p q).app d (l, r)

/-- Every complete original concatenated flag is its same literal image union. -/
theorem flags {p q : ℕ} {d : SimplexCategoryᵒᵖ}
    (l : (coefficientObject.{u} p).obj d) (r : (coefficientObject.{u} q).obj d)
    (t : Fin (d.unop.len + 1)) :
    ((coefficient l r).obj t).I = prefixLift p q '' (l.obj t).I ∪
      suffixLift p q '' (r.obj t).I := rfl

/-- The same actual pivot occurs in every complete original concatenated flag. -/
theorem pivot_mem {p q : ℕ} {d : SimplexCategoryᵒᵖ}
    (l : (coefficientObject.{u} p).obj d) (r : (coefficientObject.{u} q).obj d)
    (t : Fin (d.unop.len + 1)) :
    ULift.up.{u} (pivot p q) ∈ ((coefficient l r).obj t).I :=
  Or.inl ⟨ULift.up.{u} (Fin.last p), (l.obj t).right, ULift.ext (prefix_last p q)⟩

private instance {n : ℕ} (a b : SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- Every original scalar face or degeneracy retains both entire original coefficient maps. -/
theorem coefficient_inner {p q : ℕ} {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (l : (coefficientObject.{u} p).obj d)
    (r : (coefficientObject.{u} q).obj d) :
    (coefficientObject.{u} (p + q)).map f (coefficient l r) =
      coefficient ((coefficientObject.{u} p).map f l) ((coefficientObject.{u} q).map f r) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j g
  exact Subsingleton.elim _ _

/-- The entire concatenated final flag is full whenever both original final flags are full. -/
theorem final_full {p q : ℕ} {d : SimplexCategoryᵒᵖ}
    (l : (coefficientObject.{u} p).obj d) (r : (coefficientObject.{u} q).obj d)
    (hl : (l.obj (Fin.last d.unop.len)).I = Set.univ)
    (hr : (r.obj (Fin.last d.unop.len)).I = Set.univ) :
    ((coefficient l r).obj (Fin.last d.unop.len)).I = Set.univ := by
  ext j
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    by_cases hj : j.down.val ≤ p
    · let i : Fin (p + 1) := ⟨j.down.val, by omega⟩
      exact Or.inl ⟨ULift.up.{u} i, hl.symm ▸ Set.mem_univ _, ULift.ext (Fin.ext rfl)⟩
    · let i : Fin (q + 1) := ⟨j.down.val - p, by have := j.down.isLt; omega⟩
      refine Or.inr ⟨ULift.up.{u} i, hr.symm ▸ Set.mem_univ _, ?_⟩
      apply ULift.ext
      apply Fin.ext
      change p + (j.down.val - p) = j.down.val
      omega

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.ConcatFlags
