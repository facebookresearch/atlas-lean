/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverRankCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# The SAME full original all-parent-cell rank pushout and weak inclusion

Actual full original range coverage and open-complement injection give
the native four-map pushout. Its SAME complete original old-stage
preimage inclusion is weak and mono. Genuine model-category cobase
change proves weakness of the actual original next-rank inclusion.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in the literal native attaching square. -/
private local instance coverQuiverForPushout : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The entire original cell map lands in the SAME actual native next stage. -/
def coverAllCellToNext (k : ℕ) : coverAllCells V z k ⟶ (coverRankStage V z (k + 1) : SSet.{max u v}) :=
  SSet.Subcomplex.lift (coverAllCellMap V z k) (coverAllCellMap_range_le_next V z k)

/-- The SAME four original all-parent-cell maps form an actual native simplicial pushout. -/
theorem original_coverRank_isPushout (k : ℕ) :
    IsPushout ((coverRankStage V z k).fromPreimage (coverAllCellMap V z k))
      ((coverRankStage V z k).preimage (coverAllCellMap V z k)).ι
      (SSet.Subcomplex.homOfLE (coverRankStage_mono V z (Nat.le_succ k)))
      (coverAllCellToNext V z k) := by
  have h := SSet.Subcomplex.preimageSupRange_isPushout (coverRankStage V z k) (coverAllCellMap V z k)
    (fun q a b ha _ hab => by
      rcases q with ⟨⟨n⟩⟩
      exact coverAllCellMap_complement_injective V z k n a b ha hab)
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (SSet.Subcomplex.eqToIso (coverRankStage_sup_range V z k))
      (by rfl) (by rfl) (by rfl) (by rfl)

/-- The full native next-stage cell map keeps its SAME original ambient inclusion. -/
lemma coverAllCellToNext_ι (k : ℕ) :
    coverAllCellToNext V z k ≫ (coverRankStage V z (k + 1)).ι = coverAllCellMap V z k :=
  SSet.Subcomplex.lift_ι _ _

/-- EVERY actual original rank-stage inclusion is weak from its full original all-cell attaching square. -/
theorem original_coverRank_inclusion_weak (k : ℕ) :
    SSet.realizationWeakEquivalences
      (SSet.Subcomplex.homOfLE (coverRankStage_mono V z (Nat.le_succ k))) := by
  let _ : HomotopicalAlgebra.ModelCategory SSet.{max u v} := SSet.modelCategoryQuillen.modelCategory
  let q := ((coverRankStage V z k).preimage (coverAllCellMap V z k)).ι
  have hc : HomotopicalAlgebra.Cofibration q := SSet.modelCategoryQuillen.cofibration_of_mono q
  have hw : HomotopicalAlgebra.WeakEquivalence q :=
    (HomotopicalAlgebra.weakEquivalence_iff q).mpr (coverAllCell_preimage_weak V z k)
  have htc : HomotopicalAlgebra.trivialCofibrations SSet.{max u v} q :=
    (HomotopicalAlgebra.mem_trivialCofibrations_iff q).mpr ⟨hc, hw⟩
  have hnew := (HomotopicalAlgebra.trivialCofibrations SSet.{max u v}).of_isPushout
    (original_coverRank_isPushout V z k) htc
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    ((HomotopicalAlgebra.mem_trivialCofibrations_iff _).mp hnew).2

end Quiver.FreeGroupoid.OriginalWords
