/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConstructors
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadInputs

/-!
# Genuine normalization of the SAME whole original flagged bead

The native nondegenerate epi produces an actual original flagged map
from the entire original bead. Its full input and flag formulas are
retained, and its target's actual full bead input is nondegenerate.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead OriginalBead.TerminalFlag
open SSet.OriginalNecklace OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME native original nondegenerate epi between the two whole original bead necklaces. -/
def beadNormalizationMorphism (b : Bead K x y q) :
    beadData b.dimension ⟶ beadData (Nondegenerate.simplex b).dim where
  operator := Nondegenerate.operator b
  source := OriginalBead.OuterOperator.zero_of_epi (Nondegenerate.operator b)
  target := OriginalBead.OuterOperator.last_of_epi (Nondegenerate.operator b)
  lands := by
    rintro ⟨⟨d⟩⟩ s _hs
    change (SSet.stdSimplex.map (Nondegenerate.operator b)).app (op ⦋d⦌) s ∈
      (complex.{0} {0, Fin.last (Nondegenerate.simplex b).dim}).obj (op ⦋d⦌)
    rw [complex_endpoints]
    trivial

/-- The SAME native original epi retains both entire original input maps. -/
theorem beadNormalization_over (b : Bead K x y q) :
    (beadNormalizationMorphism b).map.{u} ≫ (ofBead (Nondegenerate.normalize b)).input =
      (ofBead b).input := by
  change (beadNormalizationMorphism b).map ≫
    ((complex (beadData (Nondegenerate.simplex b).dim).joints).ι ≫
      SSet.yonedaEquiv.symm (Nondegenerate.simplex b).simplex) =
    (complex (beadData b.dimension).joints).ι ≫ SSet.yonedaEquiv.symm b.simplex
  rw [← Category.assoc, SSet.OriginalNecklace.Morphism.map_ι, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun s => (complex (beadData b.dimension).joints).ι ≫ SSet.yonedaEquiv.symm s)
    (Nondegenerate.simplex_factor b)

/-- The SAME original full-bead normalization is an actual complete flagged-necklace map. -/
def beadNormalization (b : Bead K x y q) : ofBead b ⟶ ofBead (Nondegenerate.normalize b) where
  necklaceMap := beadNormalizationMorphism b
  over := beadNormalization_over b
  flags := rfl

/-- The full original nondegenerate-bead map has the SAME literal native epi operator. -/
theorem beadNormalization_operator (b : Bead K x y q) :
    (beadNormalization b).necklaceMap.operator = Nondegenerate.operator b := rfl

/-- Any actual positive bead of a full original bead has precisely its SAME original endpoints. -/
theorem beadData_endpoints {n : ℕ} {a b : Fin (n + 1)} (h : IsBead (beadData n) a b) :
    a = 0 ∧ b = Fin.last n := by
  have ha := h.source
  have hb := h.target
  rcases Finset.mem_insert.mp ha with ha | ha
  · have hb : b = Fin.last n := by
      rcases Finset.mem_insert.mp hb with hb | hb
      · exact False.elim ((not_lt_of_ge (hb ▸ Fin.zero_le a)) h.positive)
      · exact Finset.mem_singleton.mp hb
    exact ⟨ha, hb⟩
  · have ha := Finset.mem_singleton.mp ha
    exact False.elim ((not_lt_of_ge (ha ▸ Fin.le_last b)) h.positive)

/-- The full original bead input has its SAME genuine nondegenerate full-bead property. -/
theorem ofBead_totallyNondegenerate (b : Bead K x y q)
    (hND : b.simplex ∈ K.nonDegenerate b.dimension) : TotallyNondegenerate (ofBead b) := by
  intro a c h
  change IsBead (beadData b.dimension) a c at h
  obtain ⟨ha, hc⟩ := beadData_endpoints h
  subst a
  subst c
  have he : beadMap.{u} h ≫ (complex (beadData b.dimension).joints).ι =
      𝟙 (Δ[b.dimension] : SSet.{u}) := by
    rw [beadMap_ι]
    have ho : operator (0 : Fin (b.dimension + 1)) (Fin.last b.dimension) (Fin.zero_le _) =
        𝟙 ⦋b.dimension⦌ := by
      ext i : 3
      apply Fin.ext
      change 0 + i.val = i.val
      omega
    rw [ho]
    change SSet.stdSimplex.map (𝟙 ⦋b.dimension⦌) = 𝟙 (Δ[b.dimension] : SSet.{u})
    exact CategoryTheory.Functor.map_id _ _
  change SSet.yonedaEquiv (beadMap h ≫
    ((complex (beadData b.dimension).joints).ι ≫ SSet.yonedaEquiv.symm b.simplex)) ∈
      K.nonDegenerate b.dimension
  rw [← Category.assoc, he]
  change SSet.yonedaEquiv (𝟙 (Δ[b.dimension] : SSet.{u}) ≫ SSet.yonedaEquiv.symm b.simplex) ∈
    K.nonDegenerate b.dimension
  rw [Category.id_comp, Equiv.apply_symm_apply]
  exact hND

/-- The SAME actual whole-bead normalization target is genuinely totally nondegenerate. -/
theorem beadNormalization_target_totallyNondegenerate (b : Bead K x y q) :
    TotallyNondegenerate (ofBead (Nondegenerate.normalize b)) :=
  ofBead_totallyNondegenerate (Nondegenerate.normalize b) (Nondegenerate.normalize_nondegenerate b)

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
