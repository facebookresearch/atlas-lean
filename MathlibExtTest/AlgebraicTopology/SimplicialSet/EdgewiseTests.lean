/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import MathlibExt.AlgebraicTopology.SimplicialSet.Edgewise

/-!
# Canonical edgewise subdivision regression tests

Focused consumer checks for the canonical `SimplexCategory.edgewiseQ` and
`SSet.esd` API: packaged-map block orientation (first-block reversal,
second-block shift), `Q ⦋0⦌`/`Q ⦋1⦌` degrees as numerals, face/degeneracy
packaged formulas (`edgewiseQ_map_δ`/`edgewiseQ_map_σ`) with low-degree
`decide` guards, plus `esd` object/map computation, natural-transformation
components, the generic degree formula, and degree-zero/degree-one consequences.

The right-inclusion and comparison tests pin low-degree values, all
face/degeneracy naturality, target rather than source on `Δ[1]` and on a
nonidentity nerve arrow, constant simplicial sets, universes, and the intended
absence of later realization, outer-edgewise, Stage, and equivalence APIs.

Nonclaims: no outer-bisimplicial or Stage comparison, no Q/S comparison, no
realization or weak-equivalence theorem, no additivity, `K₀`, or spectra
claim.
-/

open CategoryTheory Opposite SimplexCategory

open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.EdgewiseTests

/-- Constant 0 on `Fin 2`: distinguishes `rev`-conjugated vs straight. -/
def const0₂ : Fin 2 →o Fin 2 where
  toFun _ := 0
  monotone' := fun _ _ _ => le_rfl

-- 1. First-block reversal at the packaged level: straight copy would give 0.
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.Hom.mk const0₂)).toOrderHom
      ⟨0, by decide⟩).val = 1 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.Hom.mk const0₂)).toOrderHom
      ⟨1, by decide⟩).val = 1 := by decide

-- 2. Second-block shift at the packaged level: unshifted would give 0.
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.Hom.mk const0₂)).toOrderHom
      ⟨2, by decide⟩).val = 2 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.Hom.mk const0₂)).toOrderHom
      ⟨3, by decide⟩).val = 2 := by decide

-- 3. `Q ⦋0⦌`/`Q ⦋1⦌` degrees as numerals.
example : (SimplexCategory.edgewiseQ.obj ⦋0⦌).len = 1 := by decide
example : (SimplexCategory.edgewiseQ.obj ⦋1⦌).len = 3 := by decide

-- 4. `esd` object computation.
example (X : SSet.{0}) (n : SimplexCategoryᵒᵖ) :
    (SSet.esd.obj X).obj n = X.obj (SimplexCategory.edgewiseQ.op.obj n) := rfl

-- 5. `esd` map computation on subdivided objects.
example (X : SSet.{0}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (SSet.esd.obj X).map f = X.map (SimplexCategory.edgewiseQ.op.map f) := rfl

-- 6. `esd` natural-transformation component.
example {X Y : SSet.{0}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (SSet.esd.map f).app n = f.app (SimplexCategory.edgewiseQ.op.obj n) := rfl

-- 7. Generic degree formula: `(esd X)ₙ = X_{2n+1}`.
example (X : SSet.{0}) (n : ℕ) :
    (SSet.esd.obj X).obj (Opposite.op ⦋n⦌) =
      X.obj (Opposite.op ⦋2 * n + 1⦌) :=
  SSet.esd_obj_op_mk X n

-- 8. Degree-zero and degree-one consequences.
example (X : SSet.{0}) :
    (SSet.esd.obj X).obj (Opposite.op ⦋0⦌) = X.obj (Opposite.op ⦋1⦌) :=
  SSet.esd_zero_eq_one X
example (X : SSet.{0}) :
    (SSet.esd.obj X).obj (Opposite.op ⦋1⦌) = X.obj (Opposite.op ⦋3⦌) :=
  SSet.esd_one_eq_three X

-- 9. Face/degeneracy packaged formulas as rewrites.
example :
    SimplexCategory.edgewiseQ.map (SimplexCategory.δ (⟨0, by decide⟩ : Fin 2)) =
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ ((⟨0, by decide⟩ : Fin 2).rev))
        (SimplexCategory.δ (⟨0, by decide⟩ : Fin 2)) :=
  SimplexCategory.edgewiseQ_map_δ _
example :
    SimplexCategory.edgewiseQ.map (SimplexCategory.δ (⟨1, by decide⟩ : Fin 2)) =
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ ((⟨1, by decide⟩ : Fin 2).rev))
        (SimplexCategory.δ (⟨1, by decide⟩ : Fin 2)) :=
  SimplexCategory.edgewiseQ_map_δ _
example :
    SimplexCategory.edgewiseQ.map (SimplexCategory.σ (⟨0, by decide⟩ : Fin 1)) =
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.σ ((⟨0, by decide⟩ : Fin 1).rev))
        (SimplexCategory.σ (⟨0, by decide⟩ : Fin 1)) :=
  SimplexCategory.edgewiseQ_map_σ _

-- 10. Low-degree `decide` guards: first-block reversal, second-block shift.
-- `δ 0`: reversed first block gives 0, shifted second block gives 3.
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.δ (⟨0, by decide⟩ : Fin 2))).toOrderHom
      ⟨0, by decide⟩).val = 0 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.δ (⟨0, by decide⟩ : Fin 2))).toOrderHom
      ⟨1, by decide⟩).val = 3 := by decide
-- `δ 1`: reversed first block gives 1, shifted second block gives 2.
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.δ (⟨1, by decide⟩ : Fin 2))).toOrderHom
      ⟨0, by decide⟩).val = 1 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.δ (⟨1, by decide⟩ : Fin 2))).toOrderHom
      ⟨1, by decide⟩).val = 2 := by decide
-- `σ 0`: first block unshifted, second block shifted by one.
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.σ (⟨0, by decide⟩ : Fin 1))).toOrderHom
      ⟨0, by decide⟩).val = 0 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.σ (⟨0, by decide⟩ : Fin 1))).toOrderHom
      ⟨1, by decide⟩).val = 0 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.σ (⟨0, by decide⟩ : Fin 1))).toOrderHom
      ⟨2, by decide⟩).val = 1 := by decide
example :
    ((SimplexCategory.edgewiseQ.map (SimplexCategory.σ (⟨0, by decide⟩ : Fin 1))).toOrderHom
      ⟨3, by decide⟩).val = 1 := by decide

-- 11. The right-block inclusion has values `n + 1, ..., 2n + 1`.
example :
    ((SimplexCategory.edgewiseRightInclusion.app ⦋0⦌).toOrderHom
      (0 : Fin 1)).val = 1 := by
  rw [SimplexCategory.edgewiseRightInclusion_app_apply_val]
  simp
example :
    ((SimplexCategory.edgewiseRightInclusion.app ⦋1⦌).toOrderHom
      (0 : Fin 2)).val = 2 := by
  rw [SimplexCategory.edgewiseRightInclusion_app_apply_val]
  simp
example :
    ((SimplexCategory.edgewiseRightInclusion.app ⦋1⦌).toOrderHom
      (1 : Fin 2)).val = 3 := by
  rw [SimplexCategory.edgewiseRightInclusion_app_apply_val]
  simp
example :
    ((SimplexCategory.edgewiseRightInclusion.app ⦋2⦌).toOrderHom
      (0 : Fin 3)).val = 3 := by
  rw [SimplexCategory.edgewiseRightInclusion_app_apply_val]
  simp
example :
    ((SimplexCategory.edgewiseRightInclusion.app ⦋2⦌).toOrderHom
      (1 : Fin 3)).val = 4 := by
  rw [SimplexCategory.edgewiseRightInclusion_app_apply_val]
  simp
example :
    ((SimplexCategory.edgewiseRightInclusion.app ⦋2⦌).toOrderHom
      (2 : Fin 3)).val = 5 := by
  rw [SimplexCategory.edgewiseRightInclusion_app_apply_val]
  simp

-- 12. Low-degree coface orientation: `δ 0` and then `δ 0 ≫ δ 0`.
example :
    SimplexCategory.edgewiseRightInclusion.app ⦋0⦌ =
      SimplexCategory.δ (0 : Fin 2) :=
  SimplexCategory.edgewiseRightInclusion_app_zero
example :
    SimplexCategory.edgewiseRightInclusion.app ⦋1⦌ =
      SimplexCategory.δ (0 : Fin 3) ≫
        SimplexCategory.δ (0 : Fin 4) :=
  SimplexCategory.edgewiseRightInclusion_app_one

-- 13. Naturality covers every face and every degeneracy in every degree.
example {n : ℕ} (i : Fin (n + 2)) :
    SimplexCategory.δ i ≫
        SimplexCategory.edgewiseRightInclusion.app ⦋n + 1⦌ =
      SimplexCategory.edgewiseRightInclusion.app ⦋n⦌ ≫
        SimplexCategory.edgewiseQ.map (SimplexCategory.δ i) :=
  SimplexCategory.edgewiseRightInclusion.naturality _

example {n : ℕ} (i : Fin (n + 1)) :
    SimplexCategory.σ i ≫
        SimplexCategory.edgewiseRightInclusion.app ⦋n⦌ =
      SimplexCategory.edgewiseRightInclusion.app ⦋n + 1⦌ ≫
        SimplexCategory.edgewiseQ.map (SimplexCategory.σ i) :=
  SimplexCategory.edgewiseRightInclusion.naturality _

-- 14. The comparison component is exactly contravariant right-block
-- precomposition and is natural in the simplicial set.
example (X : SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (SSet.esdComparison.app X).app a =
      X.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op :=
  SSet.esdComparison_app_app X a

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.esd.map f ≫ SSet.esdComparison.app Y =
      SSet.esdComparison.app X ≫ f := by
  exact SSet.esdComparison.naturality f

-- 15. On `Δ[1]`, the identity edge maps to its target, not its source.
def deltaOneIdentity : Δ[1].obj (op ⦋1⦌) :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk OrderHom.id : ⦋1⦌ ⟶ ⦋1⦌)

example :
    (SSet.esdComparison.app Δ[1]).app (op ⦋0⦌) deltaOneIdentity =
      Δ[1].δ 0 deltaOneIdentity :=
  SSet.esdComparison_app_zero Δ[1] deltaOneIdentity

example :
    (SSet.esdComparison.app Δ[1]).app (op ⦋0⦌) deltaOneIdentity =
      SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ (0 : Fin 2)) := by
  rw [SSet.esdComparison_app_zero]
  rfl

example :
    (SSet.esdComparison.app Δ[1]).app (op ⦋0⦌) deltaOneIdentity ≠
      SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ (1 : Fin 2)) := by
  rw [SSet.esdComparison_app_zero]
  change SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.δ (0 : Fin 2)) ≠
    SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.δ (1 : Fin 2))
  intro h
  exact (by decide : SimplexCategory.δ (0 : Fin 2) ≠
    SimplexCategory.δ (1 : Fin 2))
      (SSet.stdSimplex.objEquiv.symm.injective h)

-- 16. The nerve of a genuine nonidentity arrow also maps to its target.
def finTwoArrow : (0 : Fin 2) ⟶ (1 : Fin 2) :=
  homOfLE (by decide)

def finTwoNerveEdge :
    (CategoryTheory.nerve (Fin 2)).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ finTwoArrow

example :
    (SSet.esdComparison.app (CategoryTheory.nerve (Fin 2))).app
        (op ⦋0⦌) finTwoNerveEdge =
      ComposableArrows.mk₀ (1 : Fin 2) := by
  rw [SSet.esdComparison_app_zero]
  exact ComposableArrows.ext₀ rfl

example :
    (SSet.esdComparison.app (CategoryTheory.nerve (Fin 2))).app
        (op ⦋0⦌) finTwoNerveEdge ≠
      ComposableArrows.mk₀ (0 : Fin 2) := by
  have ht :
      (SSet.esdComparison.app (CategoryTheory.nerve (Fin 2))).app
          (op ⦋0⦌) finTwoNerveEdge =
        ComposableArrows.mk₀ (1 : Fin 2) := by
    rw [SSet.esdComparison_app_zero]
    exact ComposableArrows.ext₀ rfl
  intro h
  have h' : ComposableArrows.mk₀ (1 : Fin 2) =
      ComposableArrows.mk₀ (0 : Fin 2) := ht.symm.trans h
  have hObj := congrArg
    (fun z : ComposableArrows (Fin 2) 0 => z.obj (0 : Fin 1)) h'
  exact (by decide : (1 : Fin 2) ≠ 0) hObj

-- 17. On a constant simplicial set the comparison component is identity.
def constantSSet (A : Type u) : SSet.{u} :=
  (SimplicialObject.const (Type u)).obj A

example (A : Type u) (a : SimplexCategoryᵒᵖ) (x : A) :
    (SSet.esdComparison.app (constantSSet A)).app a x = x :=
  rfl

-- 18. Universe-polymorphic consumers, including mixed category universes.
example : SSet.esd.{0} ⟶ 𝟭 SSet.{0} := SSet.esdComparison
example : SSet.esd.{1} ⟶ 𝟭 SSet.{1} := SSet.esdComparison

section MixedUniverses

variable (C₀₁ : Type) [Category.{1} C₀₁]
variable (C₁₀ : Type 1) [Category.{0} C₁₀]

example : SSet.esd.obj (CategoryTheory.nerve C₀₁) ⟶
    CategoryTheory.nerve C₀₁ :=
  SSet.esdComparison.app _

example : SSet.esd.obj (CategoryTheory.nerve C₁₀) ⟶
    CategoryTheory.nerve C₁₀ :=
  SSet.esdComparison.app _

end MixedUniverses

-- 19. The leaf exposes no later realization, outer-edgewise, Stage, or
-- global-equivalence claim.

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.esdComparison_mem_realizationWeakEquivalences

/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check TopCat.SimplicialRealization.edgewiseComparison

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.outerEdgewise

/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.outerEdgewiseStageDiagonalComparison

/-- failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth SSet.esd.IsEquivalence

-- 20. Standard-axiom audit endpoints.
#print axioms SimplexCategory.edgewiseRightInclusion
#print axioms SimplexCategory.edgewiseRightInclusion_app_zero
#print axioms SimplexCategory.edgewiseRightInclusion_app_one
#print axioms SSet.esdComparison
#print axioms SSet.esdComparison_app_zero

end MathlibExtTest.AlgebraicTopology.SimplicialSet.EdgewiseTests
