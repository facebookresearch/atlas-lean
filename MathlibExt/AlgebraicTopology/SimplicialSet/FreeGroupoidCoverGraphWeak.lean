/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverRankPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverRankZero

/-!
# The SAME entire original free-groupoid cover graph is weakly contractible

The native root point is the actual rank-zero graph. Every full original
rank inclusion is weak from the SAME all-parent-cell pushout. The native
sequential-mono colimit is the entire original covering graph, retaining
all vertices, generators and coefficients. This proves actual root
inclusion weakness; no tree or weak conclusion is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in its complete native rank colimit. -/
private local instance coverQuiverForWeak : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The whole original rank-zero-to-rank comparison keeps all original coefficients. -/
def coverZeroToRankDiagram :
    (Functor.const ℕ).obj (coverRankStage V z 0 : SSet.{max u v}) ⟶ coverRankDiagram V z where
  app n := SSet.Subcomplex.homOfLE (coverRankStage_mono V z (Nat.zero_le n))
  naturality := fun {_ _} _ => rfl

/-- Every SAME original rank-zero stage comparison is weak by its native original rank-cell construction. -/
lemma coverZeroToRankDiagram_weak (n : ℕ) :
    SSet.realizationWeakEquivalences ((coverZeroToRankDiagram V z).app n) := by
  induction n with
  | zero => exact SSet.realizationWeakEquivalences.id_mem _
  | succ n ih =>
    have he : (coverZeroToRankDiagram V z).app (n + 1) =
        (coverZeroToRankDiagram V z).app n ≫
          SSet.Subcomplex.homOfLE (coverRankStage_mono V z (Nat.le_succ n)) := rfl
    exact he ▸ SSet.realizationWeakEquivalences.comp_mem _ _ ih (original_coverRank_inclusion_weak V z n)

/-- The SAME actual native rank-zero constant cocone. -/
def coverZeroCocone : Cocone ((Functor.const ℕ).obj (coverRankStage V z 0 : SSet.{max u v})) where
  pt := coverRankStage V z 0
  ι.app _ := 𝟙 _
  ι.naturality := fun {_ _} _ => rfl

/-- The full original constant rank-zero cocone is a genuine native colimit. -/
def coverZeroCoconeIsColimit : IsColimit (coverZeroCocone V z) where
  desc c := c.ι.app 0
  fac c n := by
    have h := c.w (homOfLE (Nat.zero_le n))
    change c.ι.app n = c.ι.app 0 at h
    exact (Category.id_comp _).trans h.symm
  uniq c f h := (Category.id_comp f).symm.trans (h 0)

/-- The entire SAME original native rank-zero graph inclusion into the full cover graph. -/
def coverZeroToGraph : (coverRankStage V z 0 : SSet.{max u v}) ⟶ (coverGraph V z : SSet.{max u v}) :=
  SSet.Subcomplex.homOfLE (coverRankStage_le_graph V z 0)

/-- The SAME actual original identity-path root point maps into the entire original generating cover graph. -/
def coverRootToGraph : (Δ[0] : SSet.{max u v}) ⟶ (coverGraph V z : SSet.{max u v}) :=
  coverRootToZero V z ≫ coverZeroToGraph V z

/-- The full original native rank-zero inclusion is genuinely weak by its actual sequential-mono colimit. -/
theorem coverZeroToGraph_weak : SSet.realizationWeakEquivalences (coverZeroToGraph V z) := by
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono (coverZeroToRankDiagram V z)
    (coverZeroCoconeIsColimit V z) (coverRankCoconeIsColimit V z) (coverZeroToGraph V z)
    (fun _ => rfl)
  · intro i j f
    change Mono (𝟙 (coverRankStage V z 0 : SSet.{max u v}))
    infer_instance
  · intro i j f
    exact coverRankDiagram_map_mono V z f
  · exact coverZeroToRankDiagram_weak V z

/-- The actual original root point is realization weak in the SAME entire original cover graph. -/
theorem coverRootToGraph_weak : SSet.realizationWeakEquivalences (coverRootToGraph V z) :=
  SSet.realizationWeakEquivalences.comp_mem _ _ (SSet.realizationWeakEquivalences.of_isIso _)
    (coverZeroToGraph_weak V z)

/-- The whole native root-to-graph map keeps the SAME exact original point map. -/
lemma coverRootToGraph_ι : coverRootToGraph V z ≫ (coverGraph V z).ι = coverRootPoint V z := by
  exact coverRootToZero_ι V z

/-- The SAME original generating-cover free-path nerve has its actual original root-point weak inclusion. -/
theorem coverRootPoint_weak : SSet.realizationWeakEquivalences (coverRootPoint V z) := by
  rw [← coverRootToGraph_ι]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ (coverRootToGraph_weak V z)
    (CategoryTheory.FreePathNerveCoordinates.generatingGraph_inclusion_weak (CoverVertex V z))

/-- The SAME actual native full positive-cover path nerve maps weakly to the original point. -/
theorem coverPathNerve_to_point_weak :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (nerve (Paths (CoverVertex V z)) : SSet.{max u v})) := by
  apply SSet.realizationWeakEquivalences.of_precomp (coverRootPoint V z) _ (coverRootPoint_weak V z)
  have he : coverRootPoint V z ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve (Paths (CoverVertex V z))) = 𝟙 Δ[0] :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact SSet.realizationWeakEquivalences.id_mem _

end Quiver.FreeGroupoid.OriginalWords
