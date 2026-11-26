/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideFaceIdentity
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMiddleMap

/-!
# Actual identity and composition on the nonexceptional coherent Hom maps

Every ordered interval except the two outer endpoints is supplied by an
actual endpoint face. The original middle-face agreement lets its first
and last readings preserve the same entire enriched composition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornOrderedMaps
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

private theorem first_outside (a : Fin (n + 3)) (ha : a ≠ 0) :
    (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding (0 : Fin (n + 3)))
      (ULift.up (a.pred ha)) := by
  change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove (a.pred ha)
  simpa only [Fin.succAbove_zero, Fin.succ_pred] using Fin.pos_iff_ne_zero.mpr ha

private theorem last_outside (a : Fin (n + 3)) (ha : a ≠ Fin.last (n + 2)) :
    (OrdinalFace.embedding (Fin.last (n + 2))) (ULift.up (a.castPred ha)) <
      (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) := by
  change (Fin.last (n + 2)).succAbove (a.castPred ha) < Fin.last (n + 2)
  simpa only [Fin.succAbove_last, Fin.castSucc_castPred] using Fin.lt_last_iff_ne_last.mpr ha

/-- The whole original Hom map carried by the supplied first endpoint face. -/
def firstMap (a b : Fin (n + 3)) (ha : a ≠ 0) (hb : b ≠ 0) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶ (HornFaces.object f a ⟶[SSet.{u}]
      HornFaces.object f b) :=
  HornOutsideIntervals.faceMap f 0 hi₀.symm (ULift.up (a.pred ha)) (ULift.up (b.pred hb))
    (Or.inl (first_outside.{u} a ha)) (Fin.succ_pred a ha) (Fin.succ_pred b hb)

/-- The whole original Hom map carried by the supplied last endpoint face. -/
def lastMap (a b : Fin (n + 3)) (ha : a ≠ Fin.last (n + 2)) (hb : b ≠ Fin.last (n + 2)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶ (HornFaces.object f a ⟶[SSet.{u}]
      HornFaces.object f b) :=
  HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hiₙ.symm (ULift.up (a.castPred ha)) (ULift.up (b.castPred hb))
    (Or.inr (last_outside.{u} b hb))
    (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred a ha)
    (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred b hb)

/-- The actual existing whole nonexceptional ordered Hom extraction, with all supplied original endpoint data. -/
abbrev orderedMap (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :=
  HornOutsideIntervals.homMap f hi₀ hiₙ a b hab h

/-- A positive source interval is exactly its actual supplied first-face reading. -/
theorem map_eq_first (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (ha : a ≠ 0) (hb : b ≠ 0) : orderedMap f hi₀ hiₙ a b hab h = firstMap f hi₀ a b ha hb := by
  simp only [orderedMap, HornOutsideIntervals.homMap, dite_eq_right ha]
  rfl

/-- An interval ending before the last vertex is exactly the actual supplied last-face reading. -/
theorem map_eq_last (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (ha : a ≠ Fin.last (n + 2)) (hb : b ≠ Fin.last (n + 2)) :
    orderedMap f hi₀ hiₙ a b hab h = lastMap f hiₙ a b ha hb := by
  classical
  by_cases ha₀ : a = 0
  · subst a
    simp only [orderedMap, HornOutsideIntervals.homMap]
    rfl
  · have hb₀ : b ≠ 0 := fun h₀ => ha₀ (le_antisymm (h₀ ▸ hab) (Fin.zero_le _))
    let aI : Interior.{u} n := ⟨ULift.up a, Fin.pos_iff_ne_zero.mpr ha₀, Fin.lt_last_iff_ne_last.mpr ha⟩
    let bI : Interior.{u} n := ⟨ULift.up b, Fin.pos_iff_ne_zero.mpr hb₀, Fin.lt_last_iff_ne_last.mpr hb⟩
    exact (map_eq_first f hi₀ hiₙ a b hab h ha₀ hb₀).trans
      (HornMiddleMap.firstMap_eq_lastMap f hi₀ hiₙ aI bI)

/-- The actual nonexceptional Hom extraction preserves the original enriched identity at every individual vertex. -/
theorem map_id (a : Fin (n + 3)) (h : a ≠ 0 ∨ a ≠ Fin.last (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) ≫ orderedMap f hi₀ hiₙ a a le_rfl h =
      eId SSet.{u} (HornFaces.object f a) := by
  classical
  by_cases ha : a = 0
  · have hₙ : a ≠ Fin.last (n + 2) := h.resolve_left (not_not_intro ha)
    rw [map_eq_last f hi₀ hiₙ a a le_rfl h hₙ hₙ]
    exact OutsideFaceIdentity.faceMap_id f (Fin.last (n + 2)) hiₙ.symm (ULift.up (a.castPred hₙ))
      (Or.inr (last_outside.{u} a hₙ)) (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred a hₙ)
  · rw [map_eq_first f hi₀ hiₙ a a le_rfl h ha ha]
    exact OutsideFaceIdentity.faceMap_id f 0 hi₀.symm (ULift.up (a.pred ha))
      (Or.inl (first_outside.{u} a ha)) (Fin.succ_pred a ha)

/-- The actual whole ordered Hom maps preserve enriched composition whenever the output interval is nonexceptional. -/
theorem map_comp (a b c : Fin (n + 3)) (hab : a ≤ b) (hbc : b ≤ c)
    (hac : a ≠ 0 ∨ c ≠ Fin.last (n + 2)) (hab' : a ≠ 0 ∨ b ≠ Fin.last (n + 2))
    (hbc' : b ≠ 0 ∨ c ≠ Fin.last (n + 2)) :
    eComp SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) (SimplicialThickening.mk (ULift.up.{u} b))
        (SimplicialThickening.mk (ULift.up.{u} c)) ≫ orderedMap f hi₀ hiₙ a c (hab.trans hbc) hac =
      (orderedMap f hi₀ hiₙ a b hab hab' ⊗ₘ orderedMap f hi₀ hiₙ b c hbc hbc') ≫
        eComp SSet.{u} (HornFaces.object f a) (HornFaces.object f b) (HornFaces.object f c) := by
  classical
  by_cases ha : a = 0
  · have hc : c ≠ Fin.last (n + 2) := hac.resolve_left (not_not_intro ha)
    have hb : b ≠ Fin.last (n + 2) := ne_of_lt (lt_of_le_of_lt hbc (Fin.lt_last_iff_ne_last.mpr hc))
    have haₙ : a ≠ Fin.last (n + 2) := ne_of_lt (lt_of_le_of_lt (hab.trans hbc) (Fin.lt_last_iff_ne_last.mpr hc))
    rw [map_eq_last f hi₀ hiₙ a c (hab.trans hbc) hac haₙ hc,
      map_eq_last f hi₀ hiₙ a b hab hab' haₙ hb, map_eq_last f hi₀ hiₙ b c hbc hbc' hb hc]
    exact OutsideFaceAlgebra.faceMap_comp f (Fin.last (n + 2)) hiₙ.symm
      (ULift.up (a.castPred haₙ)) (ULift.up (b.castPred hb)) (ULift.up (c.castPred hc))
      (Or.inr (last_outside.{u} b hb)) (Or.inr (last_outside.{u} c hc)) (Or.inr (last_outside.{u} c hc))
      (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred a haₙ)
      (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred b hb)
      (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred c hc)
  · have hb : b ≠ 0 := fun h₀ => ha (le_antisymm (h₀ ▸ hab) (Fin.zero_le _))
    have hc : c ≠ 0 := fun h₀ => ha (le_antisymm (h₀ ▸ (hab.trans hbc)) (Fin.zero_le _))
    rw [map_eq_first f hi₀ hiₙ a c (hab.trans hbc) hac ha hc,
      map_eq_first f hi₀ hiₙ a b hab hab' ha hb, map_eq_first f hi₀ hiₙ b c hbc hbc' hb hc]
    exact OutsideFaceAlgebra.faceMap_comp f 0 hi₀.symm (ULift.up (a.pred ha)) (ULift.up (b.pred hb))
      (ULift.up (c.pred hc))
      (Or.inl (first_outside.{u} a ha)) (Or.inl (first_outside.{u} b hb)) (Or.inl (first_outside.{u} a ha))
      (Fin.succ_pred a ha) (Fin.succ_pred b hb) (Fin.succ_pred c hc)

end CategoryTheory.CoherentRealization.HornOrderedMaps
