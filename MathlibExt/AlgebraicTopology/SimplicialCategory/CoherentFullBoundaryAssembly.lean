/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryHomGlue
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornAssembly

/-!
# Original full-boundary assembly does not change with its retained horn

Both endpoint faces belong to every original inner horn. Every
nonouter complete original Hom map is therefore the same. The existing
whole horn assembly, with the same outer map, gives one identical
enriched simplex at all retaining original inner indices.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomAssembly
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- Every original inner-horn extraction has the same complete nonouter ordered Hom map. -/
theorem orderedMap_horn (i j : Fin (n+3))
    (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2))
    (hj₀ : j ≠ 0) (hjₙ : j ≠ Fin.last (n+2))
    (a b : Fin (n+3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n+2)) :
    HornOrderedMaps.orderedMap (BoundaryFaces.horn f i) hi₀ hiₙ a b hab h =
      HornOrderedMaps.orderedMap (BoundaryFaces.horn f j) hj₀ hjₙ a b hab h := by
  classical
  by_cases ha : a = 0
  · have hbₙ : b ≠ Fin.last (n+2) := h.resolve_left (not_not_intro ha)
    have haₙ : a ≠ Fin.last (n+2) := by
      subst a
      intro h0
      have hv := congrArg Fin.val h0
      change 0 = n+2 at hv
      omega
    rw [HornOrderedMaps.map_eq_last _ _ _ _ _ _ _ haₙ hbₙ,
      HornOrderedMaps.map_eq_last _ _ _ _ _ _ _ haₙ hbₙ]
    rfl
  · have hb : b ≠ 0 := fun h0 => ha (le_antisymm (h0 ▸ hab) (Fin.zero_le _))
    rw [HornOrderedMaps.map_eq_first _ _ _ _ _ _ _ ha hb,
      HornOrderedMaps.map_eq_first _ _ _ _ _ _ _ ha hb]
    rfl

variable (g : outerHom.{u} n ⟶
  (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (Fin.last (n+2))))

/-- The SAME original complete boundary extension restricts to each original inner-horn box. -/
theorem horn_extension (hg : (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ g = BoundaryHomGlue.map f)
    (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) :
    (HornBoxGlue.box i hi₀ hiₙ).ι ≫ g =
      HornBoxGlue.boxMap hi₀ hiₙ (BoundaryFaces.horn f i) :=
  (congrArg (fun q => q ≫ g) (BoundaryHomGlue.hornBoxInclusion_ι i hi₀ hiₙ).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => BoundaryHomGlue.hornBoxInclusion i hi₀ hiₙ ≫ q) hg).trans
        (BoundaryHomGlue.map_hornBox f i hi₀ hiₙ)))

/-- The same existing original assembly at any retained original inner-horn label. -/
def simplex (hg : (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ g = BoundaryHomGlue.map f)
    (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) : coherentSimplex.{u} ⦋n+2⦌ ⟶ C :=
  HornAssembly.simplex (BoundaryFaces.horn f i) hi₀ hiₙ g (horn_extension f g hg i hi₀ hiₙ)

/-- Every retained original index gives the same whole enriched simplex with all original Hom maps. -/
theorem simplex_eq (hg : (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ g = BoundaryHomGlue.map f)
    (i j : Fin (n+3))
    (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2))
    (hj₀ : j ≠ 0) (hjₙ : j ≠ Fin.last (n+2)) :
    simplex f g hg i hi₀ hiₙ = simplex f g hg j hj₀ hjₙ := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := simplex f g hg i hi₀ hiₙ) (G := simplex f g hg j hj₀ hjₙ) (fun _ => rfl)
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  change (simplex f g hg i hi₀ hiₙ).map (.mk (ULift.up a)) (.mk (ULift.up b)) =
    (simplex f g hg j hj₀ hjₙ).map (.mk (ULift.up a)) (.mk (ULift.up b))
  by_cases hOuter : a = 0 ∧ b = Fin.last (n+2)
  · obtain ⟨rfl,rfl⟩ := hOuter
    exact (HornAssembly.simplex_outer_map (BoundaryFaces.horn f i) hi₀ hiₙ g
      (horn_extension f g hg i hi₀ hiₙ)).trans
        (HornAssembly.simplex_outer_map (BoundaryFaces.horn f j) hj₀ hjₙ g
          (horn_extension f g hg j hj₀ hjₙ)).symm
  · by_cases hab : a ≤ b
    · have h : a ≠ 0 ∨ b ≠ Fin.last (n+2) := by
        by_cases ha : a = 0
        · exact Or.inr (fun hb => hOuter ⟨ha,hb⟩)
        · exact Or.inl ha
      exact (HornAssembly.simplex_ordered_map (BoundaryFaces.horn f i) hi₀ hiₙ g
        (horn_extension f g hg i hi₀ hiₙ) a b hab h).trans
        ((orderedMap_horn f i j hi₀ hiₙ hj₀ hjₙ a b hab h).trans
          (HornAssembly.simplex_ordered_map (BoundaryFaces.horn f j) hj₀ hjₙ g
            (horn_extension f g hg j hj₀ hjₙ) a b hab h).symm)
    · exact HomUnitsAndEmpty.empty_hom_ext
        (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n+3))) ≤ ULift.up b from hab) _ _

end CategoryTheory.CoherentRealization.BoundaryHomAssembly
