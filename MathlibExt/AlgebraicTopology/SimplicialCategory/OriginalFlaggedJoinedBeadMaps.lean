/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentGenerators
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentJoinedCoefficient

/-!
# Both full native original joined-bead maps

The SAME actual two endpoint-interval beads map to the complete original
outer bead by the original joining ordinal. Both full native prefix and
suffix equations retain the entire original input interval operators.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBeadInterval SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts

variable {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c)

/-- The SAME full original native joined-bead map, including either zero-side bead. -/
def joinedBeadMorphism :
    (beadData (length a b)).concat (beadData (length b c)) ⟶ beadData (length a c) where
  operator := joinedOperator a b c hab hbc
  source := joinedOperator_zero a b c hab hbc
  target := joinedOperator_last a b c hab hbc
  lands := by
    rintro ⟨⟨d⟩⟩ s _hs
    change (SSet.stdSimplex.map (joinedOperator a b c hab hbc)).app (op ⦋d⦌) s ∈
      (complex.{0} {0, Fin.last (length a c)}).obj (op ⦋d⦌)
    rw [complex_endpoints]
    trivial

/-- The complete original first bead retains the SAME entire original outer input operator. -/
theorem joinedBead_prefix :
    concatLeft.{u} (beadData (length a b)) (beadData (length b c)) ≫
      (joinedBeadMorphism a b c hab hbc).map ≫ (beadChart (length a c)).hom ≫
        SSet.stdSimplex.map (OriginalBeadInterval.operator a c (hab.trans hbc)) =
      (beadChart (length a b)).hom ≫ SSet.stdSimplex.map (OriginalBeadInterval.operator a b hab) := by
  exact congrArg (fun θ => (complex.{u} (beadData (length a b)).joints).ι ≫ SSet.stdSimplex.map θ)
    (joined_prefix_square a b c hab hbc)

/-- The complete original second bead retains the SAME entire original outer input operator. -/
theorem joinedBead_suffix :
    concatRight.{u} (beadData (length a b)) (beadData (length b c)) ≫
      (joinedBeadMorphism a b c hab hbc).map ≫ (beadChart (length a c)).hom ≫
        SSet.stdSimplex.map (OriginalBeadInterval.operator a c (hab.trans hbc)) =
      (beadChart (length b c)).hom ≫ SSet.stdSimplex.map (OriginalBeadInterval.operator b c hbc) := by
  exact congrArg (fun θ => (complex.{u} (beadData (length b c)).joints).ι ≫ SSet.stdSimplex.map θ)
    (joined_suffix_square a b c hab hbc)

/-- The SAME full first interval input square retains the entire original input simplex. -/
theorem joinedBead_prefix_input (K : SSet.{u}) (σ : K _⦋n⦌) :
    concatLeft.{u} (beadData (length a b)) (beadData (length b c)) ≫
      (joinedBeadMorphism a b c hab hbc).map ≫ (beadChart (length a c)).hom ≫
        SSet.yonedaEquiv.symm (K.map (OriginalBeadInterval.operator a c (hab.trans hbc)).op σ) =
      (beadChart (length a b)).hom ≫
        SSet.yonedaEquiv.symm (K.map (OriginalBeadInterval.operator a b hab).op σ) := by
  have h := congrArg (fun e => e ≫ SSet.yonedaEquiv.symm σ) (joinedBead_prefix.{u} a b c hab hbc)
  simp only [Category.assoc] at h
  rw [SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_naturality_left] at h
  exact h

/-- The SAME full second interval input square retains the entire original input simplex. -/
theorem joinedBead_suffix_input (K : SSet.{u}) (σ : K _⦋n⦌) :
    concatRight.{u} (beadData (length a b)) (beadData (length b c)) ≫
      (joinedBeadMorphism a b c hab hbc).map ≫ (beadChart (length a c)).hom ≫
        SSet.yonedaEquiv.symm (K.map (OriginalBeadInterval.operator a c (hab.trans hbc)).op σ) =
      (beadChart (length b c)).hom ≫
        SSet.yonedaEquiv.symm (K.map (OriginalBeadInterval.operator b c hbc).op σ) := by
  have h := congrArg (fun e => e ≫ SSet.yonedaEquiv.symm σ) (joinedBead_suffix.{u} a b c hab hbc)
  simp only [Category.assoc] at h
  rw [SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_naturality_left] at h
  exact h

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
