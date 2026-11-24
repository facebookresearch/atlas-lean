/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOrderedMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOuterMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedSingletonHomUnits

/-!
# Whole original Hom maps and all composition laws of a coherent horn filler

The constructed Kan outer-Hom extension is combined with the actual
nonexceptional supplied-face maps and genuinely empty reverse intervals.
Its whole identity and composition laws retain all original vertices,
including the two endpoint-unit cases.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornHomMaps
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
  [SSet.KanComplex (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2)))]

/-- The actual whole map on every original coherent Hom, including the outer extension and empty reverse intervals. -/
def homMap (a b : Fin (n + 3)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := by
  classical
  by_cases h : a = 0 ∧ b = Fin.last (n + 2)
  · obtain ⟨rfl, rfl⟩ := h
    exact HornOuterMap.map f hi₀ hiₙ
  · by_cases hab : a ≤ b
    · exact HornOrderedMaps.orderedMap f hi₀ hiₙ a b hab (by
        by_cases ha : a = 0
        · exact Or.inr (fun hb => h ⟨ha, hb⟩)
        · exact Or.inl ha)
    · exact HomUnitsAndEmpty.emptyMap (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n + 3))) ≤ ULift.up b from hab) _

/-- The actual outer pair reads exactly the whole constructed Kan-Hom extension. -/
theorem homMap_outer : homMap f hi₀ hiₙ 0 (Fin.last (n + 2)) = HornOuterMap.map f hi₀ hiₙ := by
  classical
  simp only [homMap, and_self, dite_eq_left True.intro]

/-- Every other ordered pair reads exactly its actual supplied endpoint-face Hom map. -/
theorem homMap_ordered (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    homMap f hi₀ hiₙ a b = HornOrderedMaps.orderedMap f hi₀ hiₙ a b hab h := by
  classical
  have hN : ¬(a = 0 ∧ b = Fin.last (n + 2)) := by
    rintro ⟨ha, hb⟩
    exact h.elim (fun h => h ha) (fun h => h hb)
  simp only [homMap, dite_eq_right hN, dite_eq_left hab]

/-- The actual original Hom maps preserve the enriched identity at every individual original vertex. -/
theorem homMap_id (a : Fin (n + 3)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) ≫ homMap f hi₀ hiₙ a a = eId SSet.{u}
      (HornFaces.object f a) := by
  classical
  have h : a ≠ 0 ∨ a ≠ Fin.last (n + 2) := by
    by_cases ha : a = 0
    · right
      intro hb
      have h' := congrArg Fin.val (ha.symm.trans hb)
      change 0 = n + 2 at h'
      omega
    · exact Or.inl ha
  rw [homMap_ordered f hi₀ hiₙ a a le_rfl h]
  exact HornOrderedMaps.map_id f hi₀ hiₙ a h

/-- All whole original Hom maps preserve enriched composition, including empty factors, the outer interval
  and both actual endpoint-unit cases. -/
theorem homMap_comp (a b c : Fin (n + 3)) :
    eComp SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) (SimplicialThickening.mk (ULift.up.{u} b))
        (SimplicialThickening.mk (ULift.up.{u} c)) ≫ homMap f hi₀ hiₙ a c =
      (homMap f hi₀ hiₙ a b ⊗ₘ homMap f hi₀ hiₙ b c) ≫
        eComp SSet.{u} (HornFaces.object f a) (HornFaces.object f b) (HornFaces.object f c) := by
  classical
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · by_cases hN : a = 0 ∧ c = Fin.last (n + 2)
      · obtain ⟨rfl, rfl⟩ := hN
        by_cases hb₀ : b = 0
        · subst b
          exact @SingletonHomUnits.left_comp (coherentSimplex.{u} ⦋n + 2⦌) C
            (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))
            (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
            (HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (0 : Fin (n + 3))))
            (homMap f hi₀ hiₙ 0 0) (homMap f hi₀ hiₙ 0 (Fin.last (n + 2))) (homMap_id f hi₀ hiₙ 0)
        · by_cases hbₙ : b = Fin.last (n + 2)
          · subst b
            exact @SingletonHomUnits.right_comp (coherentSimplex.{u} ⦋n + 2⦌) C
              (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))
              (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
              (HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (Fin.last (n + 2))))
              (homMap f hi₀ hiₙ (Fin.last (n + 2)) (Fin.last (n + 2)))
              (homMap f hi₀ hiₙ 0 (Fin.last (n + 2))) (homMap_id f hi₀ hiₙ (Fin.last (n + 2)))
          · let bI : Interior.{u} n := ⟨ULift.up b, Fin.pos_iff_ne_zero.mpr hb₀, Fin.lt_last_iff_ne_last.mpr hbₙ⟩
            rw [homMap_outer f hi₀ hiₙ, homMap_ordered f hi₀ hiₙ 0 b (Fin.zero_le _) (Or.inr hbₙ),
              homMap_ordered f hi₀ hiₙ b (Fin.last (n + 2)) (Fin.le_last _) (Or.inl hb₀)]
            exact HornOuterMap.positive_comp f hi₀ hiₙ bI
      · have hac : a ≠ 0 ∨ c ≠ Fin.last (n + 2) := by
          by_cases ha : a = 0
          · exact Or.inr (fun hc => hN ⟨ha, hc⟩)
          · exact Or.inl ha
        have hab' : a ≠ 0 ∨ b ≠ Fin.last (n + 2) := by
          by_cases ha : a = 0
          · right
            intro hb
            exact hN ⟨ha, le_antisymm (Fin.le_last _) (hb ▸ hbc)⟩
          · exact Or.inl ha
        have hbc' : b ≠ 0 ∨ c ≠ Fin.last (n + 2) := by
          by_cases hc : c = Fin.last (n + 2)
          · left
            intro hb
            exact hN ⟨le_antisymm (hb ▸ hab) (Fin.zero_le _), hc⟩
          · exact Or.inr hc
        rw [homMap_ordered f hi₀ hiₙ a c (hab.trans hbc) hac,
          homMap_ordered f hi₀ hiₙ a b hab hab', homMap_ordered f hi₀ hiₙ b c hbc hbc']
        exact HornOrderedMaps.map_comp f hi₀ hiₙ a b c hab hbc hac hab' hbc'
    · apply SSet.hom_ext
      intro q
      apply ConcreteCategory.hom_ext
      rintro ⟨p₀, p₁⟩
      exact False.elim (hbc (show b ≤ c from HomUnitsAndEmpty.source_order (a := ULift.up.{u} b) (b :=
        ULift.up.{u} c) p₁))
  · apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    rintro ⟨p₀, p₁⟩
    exact False.elim (hab (show a ≤ b from HomUnitsAndEmpty.source_order (a := ULift.up.{u} a) (b :=
      ULift.up.{u} b) p₀))

/-- The actual enriched simplex assembled from the proved whole Hom maps, preserving every individual
  original vertex. -/
def simplex : coherentSimplex.{u} ⦋n + 2⦌ ⟶ C where
  obj a := HornFaces.object f a.as.down
  map a b := homMap f hi₀ hiₙ a.as.down b.as.down
  map_id a := homMap_id f hi₀ hiₙ a.as.down
  map_comp a b c := homMap_comp f hi₀ hiₙ a.as.down b.as.down c.as.down

/-- The assembled enriched simplex has exactly the supplied original vertex at every original label. -/
theorem simplex_obj (a : Fin (n + 3)) : (simplex f hi₀ hiₙ).obj (.mk (ULift.up a)) = HornFaces.object f a := rfl

/-- The whole assembled simplex Hom map is literally the original constructed Hom map at the two supplied labels. -/
theorem simplex_map (a b : Fin (n + 3)) :
    (simplex f hi₀ hiₙ).map (.mk (ULift.up a)) (.mk (ULift.up b)) = homMap f hi₀ hiₙ a b := rfl

end CategoryTheory.CoherentRealization.HornHomMaps
