/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeCylinder

/-!
# Actual sections of the standard simplex cylinder maps

For each standard simplex, the original base vertices lie in its
zero cylinder row and the new apex lies at the final vertex of the
one row. The resulting actual ordinal nerve map is a section of the
simplex cylinder-to-cone collapse. This proves epimorphy of the whole
standard simplex cone map. These sections are used at fixed simplex
dimensions; no natural inverse in an arbitrary simplicial set is
asserted.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeCylinder

/-- The original base vertices in the zero row and the new apex at the final one-row vertex. -/
def sectionOrder (n : ℕ) : Fin (n + 2) →o Fin (n + 1) × Fin 2 where
  toFun k := if h : k = Fin.last (n + 1) then (Fin.last n, 1) else (k.castPred h, 0)
  monotone' k l hkl := by
    by_cases hl : l = Fin.last (n + 1)
    · by_cases hk : k = Fin.last (n + 1)
      · simp only [dite_eq_left hk, dite_eq_left hl]
        exact le_rfl
      · simp only [dite_eq_right hk, dite_eq_left hl]
        exact ⟨Fin.le_last _, show (0 : Fin 2) ≤ 1 from by decide⟩
    · have hk : k ≠ Fin.last (n + 1) := by
        intro he
        exact hl (le_antisymm (Fin.le_last _) (he ▸ hkl))
      simp only [dite_eq_right hk, dite_eq_right hl]
      exact ⟨hkl, le_rfl⟩

/-- The section uses the original zero row away from the apex and the last one-row vertex at the apex. -/
theorem sectionOrder_apply (n : ℕ) (k : Fin (n + 2)) :
    sectionOrder n k = if h : k = Fin.last (n + 1) then (Fin.last n, 1) else (k.castPred h, 0) := rfl

/-- The actual ordinal section is a right inverse of the original ordinal collapse. -/
theorem sectionOrder_collapse (n : ℕ) (k : Fin (n + 2)) : collapseOrder n (sectionOrder n k) = k := by
  by_cases hk : k = Fin.last (n + 1)
  · rw [sectionOrder_apply, dite_eq_left hk]
    subst k
    rfl
  · rw [sectionOrder_apply, dite_eq_right hk]
    change (k.castPred hk).castSucc = k
    exact Fin.castSucc_castPred k hk

/-- The actual ordinary functor of the section, with the same lifted ordinal objects. -/
def sectionFunctor (n : ℕ) : ULift.{u} (Fin (n + 2)) ⥤ ULift.{u} (Fin (n + 1) × Fin 2) :=
  (show Monotone (fun k : ULift.{u} (Fin (n + 2)) => ULift.up (sectionOrder n k.down)) from
    fun _k _l hkl => (sectionOrder n).monotone hkl).functor

/-- The whole original simplicial section at the specified standard simplex dimension. -/
def simplexSection (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1] :=
  (SSet.stdSimplex.isoNerve (n + 1)).hom ≫ nerveMap (sectionFunctor n) ≫ (prodStdSimplex.isoNerve n 1).inv

/-- The section retains the original first coordinate in every original scalar simplex. -/
theorem simplexSection_fst (n m : ℕ) (s : (Δ[n + 1] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    ((simplexSection n).app _ s).1 i = (sectionOrder n (s i)).1 := rfl

/-- The section retains the original row coordinate in every original scalar simplex. -/
theorem simplexSection_snd (n m : ℕ) (s : (Δ[n + 1] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    ((simplexSection n).app _ s).2 i = (sectionOrder n (s i)).2 := rfl

/-- The actual whole section followed by collapse is the identical original standard simplex map. -/
theorem simplexSection_collapse (n : ℕ) : simplexSection.{u} n ≫ simplexCollapse n = 𝟙 Δ[n + 1] := by
  ext ⟨⟨m⟩⟩ : 3
  funext s
  apply SSet.stdSimplex.ext
  intro i
  change collapseOrder n (sectionOrder n (s i)) = s i
  exact sectionOrder_collapse n (s i)

/-- The actual standard simplex collapse is epimorphic because its whole section is proved. -/
instance simplexCollapse_epi (n : ℕ) : Epi (simplexCollapse.{u} n) where
  left_cancellation f g h := by
    have he := congrArg (fun k => simplexSection n ≫ k) h
    simpa only [← Category.assoc, simplexSection_collapse, Category.id_comp] using he

/-- The standard simplex cylinder map in native join coordinates is epimorphic. -/
instance simplexCone_epi (n : ℕ) : Epi (simplexCone.{u} n) :=
  inferInstanceAs (Epi (simplexCollapse.{u} n ≫ (joinStdSimplexIso n 0).inv))

/-- The constructed whole cylinder-to-cone map on a standard simplex is its identical original simplex map. -/
theorem coneCylinder_stdSimplex (n : ℕ) : coneCylinder (Δ[n] : SSet.{u}) = simplexCone n := by
  have h := coneCylinder_simplex (𝟙 (Δ[n] : SSet.{u}))
  simpa only [id_whiskerRight, Category.id_comp, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.comp_id] using h

/-- Every whole standard simplex cylinder-to-cone map is epimorphic. -/
instance coneCylinder_stdSimplex_epi (n : ℕ) : Epi (coneCylinder (Δ[n] : SSet.{u})) := by
  rw [coneCylinder_stdSimplex]
  infer_instance

end SSet.WalkingAdjunction.ConeCylinder
