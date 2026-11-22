/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingSimplexTerminal
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# The same full original ordinal right-mapping space is the point

For ordered endpoints the original successor map is constant at the
source on the whole original front, then takes the same final vertex
to the target. Its entire original right-mapping space is consequently
isomorphic to the original simplicial point, in every universe.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

/-- The same complete original successor order map, retaining the full front and final endpoint. -/
def simplexStep {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) (m : ℕ) : ⦋m + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    { toFun i := if i = Fin.last (m + 1) then b else a
      monotone' := by
        intro i j hij
        change (if i = Fin.last (m + 1) then b else a) ≤
          (if j = Fin.last (m + 1) then b else a)
        by_cases hi : i = Fin.last (m + 1)
        · have hj : j = Fin.last (m + 1) := le_antisymm (Fin.le_last j) (hi ▸ hij)
          rw [ite_eq_left hi, ite_eq_left hj]
        · by_cases hj : j = Fin.last (m + 1)
          · rw [ite_eq_right hi, ite_eq_left hj]
            exact hab
          · rw [ite_eq_right hi, ite_eq_right hj]
      }

/-- The entire same original ordinal mapping simplex, with the actual full front and target equations. -/
def simplexMappingSimplex {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) (m : ℕ) :
    (SSet.mappingSpaceRight (Δ[n] : SSet.{u}) (simplexVertex n a) (simplexVertex n b)) _⦋m⦌ :=
  (SSet.mappingSpaceRight.simplexEquivSucc (Δ[n] : SSet.{u})
    (simplexVertex n a) (simplexVertex n b) m).symm
    ⟨SSet.stdSimplex.map (simplexStep a b hab m), by
      rw [SSet.frontInclusion_eq]
      have hleft : SimplexCategory.δ (Fin.last (m + 1)) ≫ simplexStep a b hab m =
          SimplexCategory.const ⦋m⦌ ⦋n⦌ a := by
        apply SimplexCategory.Hom.ext
        ext i
        change (if (Fin.last (m + 1)).succAbove i = Fin.last (m + 1) then b else a).val = a.val
        rw [Fin.succAbove_last_apply, ite_eq_right (ne_of_lt (Fin.castSucc_lt_last i))]
      have ht := SSet.toDeltaZero_eq (SSet.stdSimplex.map (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0))
      exact (SSet.stdSimplex.map_comp _ _).symm.trans
        ((congrArg SSet.stdSimplex.map hleft).trans
          ((SSet.stdSimplex.map_comp (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0)
            (SimplexCategory.const ⦋0⦌ ⦋n⦌ a)).trans
              (congrArg (fun f => f ≫ simplexVertex n a) ht))), by
      rw [SSet.rightVertex_eq]
      have hright : AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌ ≫ simplexStep a b hab m =
          SimplexCategory.const ⦋0⦌ ⦋n⦌ b := by
        apply SimplexCategory.Hom.ext
        ext i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        change (if (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌).toOrderHom 0 =
          Fin.last (m + 1) then b else a).val = b.val
        rw [SSet.inr'_toOrderHom_zero, ite_eq_left rfl]
      exact (SSet.stdSimplex.map_comp _ _).symm.trans (congrArg SSet.stdSimplex.map hright)⟩

/-- Both full inverse maps identify the same original ordinal right-mapping space with the original simplicial point. -/
def simplexMappingPointIso {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    SSet.mappingSpaceRight (Δ[n] : SSet.{u}) (simplexVertex n a) (simplexVertex n b) ≅ (Δ[0] : SSet.{u}) where
  hom := SSet.stdSimplex.isTerminalObj₀.from _
  inv :=
    { app q := ↾fun _ => simplexMappingSimplex a b hab q.unop.len
      naturality q r θ := by
        apply ConcreteCategory.hom_ext
        intro x
        let _ := simplex_mapping_subsingleton (m := r.unop.len) a b
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro σ
    let _ := simplex_mapping_subsingleton (m := q.unop.len) a b
    exact Subsingleton.elim _ _
  inv_hom_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The same original ordinal right-mapping point projection is genuinely weak. -/
theorem simplexMappingPoint_weak {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.mappingSpaceRight (Δ[n] : SSet.{u}) (simplexVertex n a) (simplexVertex n b))) :=
  SSet.realizationWeakEquivalences.of_isIso (simplexMappingPointIso a b hab).hom

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
