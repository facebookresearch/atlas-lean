/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeCylinderSection
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom

/-!
# The actual standard-simplex cylinder deformation

The original collapse and its proved ordinal section form a
pointwise upper retraction of the product ordinal. Its actual natural
transformation gives the whole nerve homotopy from the identity
cylinder map to section after collapse. The original row coordinate
is fixed throughout; in the zero row the entire point is fixed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeCylinder

/-- Section after collapse fixes the zero row and sends the one row to its last vertex. -/
theorem section_collapse_order (n : ℕ) (p : Fin (n + 1) × Fin 2) :
    sectionOrder n (collapseOrder n p) = if p.2 = 0 then p else (Fin.last n, 1) := by
  rcases p with ⟨i, j⟩
  fin_cases j
  · change sectionOrder n (collapseOrder n (i, 0)) = (i, 0)
    have hc : collapseOrder n (i, 0) = i.castSucc := rfl
    have hn : i.castSucc ≠ Fin.last (n + 1) := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = n + 1 at hv
      have hi := i.isLt
      omega
    rw [hc, sectionOrder_apply, dite_eq_right hn]
    change (i.castSucc.castPred hn, 0) = (i, 0)
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  · change sectionOrder n (collapseOrder n (i, 1)) = (Fin.last n, 1)
    have hc : collapseOrder n (i, 1) = Fin.last (n + 1) := rfl
    rw [hc, sectionOrder_apply, dite_eq_left rfl]

/-- Every original product-ordinal point lies below its actual section after collapse. -/
theorem le_section_collapse (n : ℕ) (p : Fin (n + 1) × Fin 2) : p ≤ sectionOrder n (collapseOrder n p) := by
  rw [section_collapse_order]
  by_cases hp : p.2 = 0
  · rw [ite_eq_left hp]
  · rw [ite_eq_right hp]
    exact ⟨Fin.le_last _, Fin.le_last _⟩

/-- The actual natural transformation from the identity to section after collapse. -/
def sectionUnit (n : ℕ) : 𝟭 (ULift.{u} (Fin (n + 1) × Fin 2)) ⟶
    collapseFunctor n ⋙ sectionFunctor n where
  app p := homOfLE (le_section_collapse n p.down)

/-- The entire nerve cylinder of the actual ordinal retraction unit, in native simplex-product coordinates. -/
def deformationMap (n : ℕ) : ((Δ[n] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ Δ[n] ⊗ Δ[1] :=
  ((prodStdSimplex.isoNerve n 1).hom ▷ (Δ[1] : SSet.{u})) ≫
    CategoryTheory.NatTrans.nerveHomotopyMap (sectionUnit n) ≫ (prodStdSimplex.isoNerve n 1).inv

/-- Initial evaluation is the identical original whole cylinder. -/
theorem deformationMap_zero (n : ℕ) : SSet.ι₀ ≫ deformationMap.{u} n = 𝟙 (Δ[n] ⊗ (Δ[1] : SSet.{u})) := by
  let h := ((CategoryTheory.NatTrans.nerveHomotopy (sectionUnit.{u} n)).precomp
    (prodStdSimplex.isoNerve n 1).hom).postcomp (prodStdSimplex.isoNerve n 1).inv
  have hh : h.h = deformationMap n := by
    dsimp only [h]
    rw [Homotopy.postcomp_h, Homotopy.precomp_h]
    exact Category.assoc _ _ _
  have hz := h.h₀
  rw [hh] at hz
  simpa only [CategoryTheory.nerveMap_id, Category.comp_id, Iso.hom_inv_id] using hz

/-- Final evaluation is the original collapse followed by its actual whole section. -/
theorem deformationMap_one (n : ℕ) : SSet.ι₁ ≫ deformationMap.{u} n = simplexCollapse n ≫ simplexSection n := by
  let h := ((CategoryTheory.NatTrans.nerveHomotopy (sectionUnit.{u} n)).precomp
    (prodStdSimplex.isoNerve n 1).hom).postcomp (prodStdSimplex.isoNerve n 1).inv
  have hr : (prodStdSimplex.isoNerve n 1).hom ≫ nerveMap (collapseFunctor n ⋙ sectionFunctor n) ≫
      (prodStdSimplex.isoNerve n 1).inv = simplexCollapse n ≫ simplexSection n := by
    rw [simplexCollapse, simplexSection, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    have hn := congrArg (fun k => (prodStdSimplex.isoNerve n 1).hom ≫ k ≫
      (prodStdSimplex.isoNerve n 1).inv) (CategoryTheory.nerveMap_comp (collapseFunctor n) (sectionFunctor n))
    simpa only [Category.assoc] using hn.symm
  have hh : h.h = deformationMap n := by
    dsimp only [h]
    rw [Homotopy.postcomp_h, Homotopy.precomp_h]
    exact Category.assoc _ _ _
  exact (congrArg (fun k => SSet.ι₁ ≫ k) hh.symm).trans (h.h₁.trans hr)

/-- The actual complete standard-simplex cylinder homotopy. -/
def deformation (n : ℕ) : Homotopy (𝟙 ((Δ[n] : SSet.{u}) ⊗ Δ[1]))
    (simplexCollapse n ≫ simplexSection n) :=
  Homotopy.mkOfH (deformationMap n) (deformationMap_zero n) (deformationMap_one n)

/-- The original row coordinate remains fixed at every scalar vertex throughout the entire deformation. -/
theorem deformationMap_snd (n m : ℕ)
    (s : (((Δ[n] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1]) _⦋m⦌) (i : Fin (m + 1)) :
    ((deformationMap n).app _ s).2 i = s.1.2 i := by
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor (sectionUnit.{u} n)).obj
    (ULift.up (s.1.1 i, s.1.2 i), s.2 i)).down.2 = s.1.2 i
  generalize ht : s.2 i = t
  fin_cases t
  · rfl
  · change (sectionOrder n (collapseOrder n (s.1.1 i, s.1.2 i))).2 = s.1.2 i
    rw [section_collapse_order]
    by_cases hs : s.1.2 i = 0
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs]
      have hj := (s.1.2 i).isLt
      have hn : (s.1.2 i).val ≠ 0 := fun h => hs (Fin.ext h)
      apply Fin.ext
      change 1 = (s.1.2 i).val
      omega

/-- Every original zero-row coordinate is fixed throughout the whole deformation. -/
theorem deformationMap_fst_of_zero (n m : ℕ)
    (s : (((Δ[n] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1]) _⦋m⦌) (i : Fin (m + 1))
    (hs : s.1.2 i = 0) : ((deformationMap n).app _ s).1 i = s.1.1 i := by
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor (sectionUnit.{u} n)).obj
    (ULift.up (s.1.1 i, s.1.2 i), s.2 i)).down.1 = s.1.1 i
  generalize ht : s.2 i = t
  fin_cases t
  · rfl
  · change (sectionOrder n (collapseOrder n (s.1.1 i, s.1.2 i))).1 = s.1.1 i
    rw [section_collapse_order, ite_eq_left hs]

end SSet.WalkingAdjunction.ConeCylinder
