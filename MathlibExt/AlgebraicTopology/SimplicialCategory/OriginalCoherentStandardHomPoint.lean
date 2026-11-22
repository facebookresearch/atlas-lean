/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentPointedWeakPreservation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentStandardEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedOriginalIsomorphismHoms
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingSimplexTerminal

/-!
# Same original ordered standard coherent Hom point weakness

The complete original interval is the terminal object of the native
path-poset category. The existing genuine nerve contraction and the
same original enriched standard-simplex isomorphism prove point
weakness of the full original standard raw Hom, with its endpoints kept.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

open SimplicialEnrichment

/-- The full same original interval is terminal in its entire native path category. -/
def fullIntervalIsTerminal {J : Type u} [LinearOrder J] (a b : J) (hab : a ≤ b) :
    IsTerminal (show SimplicialThickening.Path a b from
      { I := Set.Icc a b
        left := ⟨le_rfl, hab⟩
        right := ⟨hab, le_rfl⟩
        left_le := fun _ h => h.1
        le_right := fun _ h => h.2 }) :=
  IsTerminal.ofUniqueHom (fun p => ⟨⟨⟨fun x hx => ⟨p.left_le x hx, p.le_right x hx⟩⟩⟩⟩)
    (by intro p f; apply InducedCategory.Hom.ext; exact Subsingleton.elim _ _)

/-- The point projection of the full original ordered native interval Hom is genuinely weak. -/
theorem intervalHom_point_weak {J : Type u} [LinearOrder J] (a b : J) (hab : a ≤ b) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (SimplicialThickening.Path a b))) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal
    (fullIntervalIsTerminal a b hab)

/-- The same full original raw standard-simplex Hom at ordered original ordinal endpoints has weak point projection. -/
theorem standardHom_point_weak (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (hom (Δ[n] : SSet.{u}) (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n a))
        (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n b)))) := by
  let e := (simplexIso.{u} ⦋n⦌).hom.map
    (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n a))
    (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n b))
  let _ : IsIso e := originalIso_hom_isIso (simplexIso.{u} ⦋n⦌) _ _
  have ha : (simplexIso.{u} ⦋n⦌).hom.obj (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n a)) =
      SimplicialThickening.mk (ULift.up.{u} a) := by
    exact (congrArg (simplexIso.{u} ⦋n⦌).hom.obj
      (SSet.yonedaEquiv_map (SimplexCategory.const ⦋0⦌ ⦋n⦌ a))).trans
        (simplexIso_hom_obj ⦋n⦌ a)
  have hb : (simplexIso.{u} ⦋n⦌).hom.obj (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n b)) =
      SimplicialThickening.mk (ULift.up.{u} b) := by
    exact (congrArg (simplexIso.{u} ⦋n⦌).hom.obj
      (SSet.yonedaEquiv_map (SimplexCategory.const ⦋0⦌ ⦋n⦌ b))).trans
        (simplexIso_hom_obj ⦋n⦌ b)
  let r := EqualityTransport.hom ha hb
  let _ : IsIso r := by unfold r EqualityTransport.hom; infer_instance
  have ht := intervalHom_point_weak (ULift.up.{u} a) (ULift.up.{u} b) hab
  have hw := SSet.realizationWeakEquivalences.comp_mem e r
    (SSet.realizationWeakEquivalences.of_isIso e) (SSet.realizationWeakEquivalences.of_isIso r)
  have h := SSet.realizationWeakEquivalences.comp_mem _ _ hw ht
  have he : e ≫ r ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))) =
      SSet.stdSimplex.isTerminalObj₀.from
        (hom (Δ[n] : SSet.{u}) (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n a))
          (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex n b))) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

end CategoryTheory.CoherentRealization
