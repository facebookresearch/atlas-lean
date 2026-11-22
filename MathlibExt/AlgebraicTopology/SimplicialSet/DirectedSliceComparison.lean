/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OverSliceFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.DirectedFibrationCategorical
import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinDirectedAnodyne

/-!
# Native categorical and trivial comparisons for diagram slices

Both orientations use their original pullback comparison. Over a genuine
quasicategory base these are categorical fibrations. Endpoint-preserving
directed-anodyne restrictions have boundary lifting, both relatively and
in the actual base slice. No arbitrary right properness is used.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet

/-- The original under-slice comparison is a categorical fibration over a quasicategory base. -/
theorem sliceUnder.categoricalFibration_restrictionComparison {K₀ K X B : SSet.{u}}
    (i : K₀ ⟶ K) [Mono i] (t : K ⟶ X) (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    categoricalFibrations (sliceUnder.restrictionComparison i t p) := by
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  let _ : LeftFibration (sliceUnder.restrict B (t ≫ p) i) :=
    leftFibration_sliceUnder_restrict B (t ≫ p) i
  let _ : LeftFibration
      (pullback.fst (sliceUnder.map X (i ≫ t) p) (sliceUnder.restrict B (t ≫ p) i)) :=
    ⟨leftFibrations.pullback_fst _ _ LeftFibration.mem⟩
  let _ : Quasicategory
      (pullback (sliceUnder.map X (i ≫ t) p) (sliceUnder.restrict B (t ≫ p) i)) :=
    quasicategory_of_innerFibration
      (pullback.fst (sliceUnder.map X (i ≫ t) p) (sliceUnder.restrict B (t ≫ p) i))
  let _ : LeftFibration (sliceUnder.restrictionComparison i t p) :=
    leftFibration_sliceUnder_restrictionComparison i t p
  exact LeftFibration.categoricalFibration _

/-- The original over-slice comparison is a categorical fibration over a quasicategory base. -/
theorem sliceOver.categoricalFibration_restrictionComparison {K₀ K X B : SSet.{u}}
    (i : K₀ ⟶ K) [Mono i] (t : K ⟶ X) (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    categoricalFibrations (sliceOver.restrictionComparison i t p) := by
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  let _ : Quasicategory (sliceOver X (i ≫ t)) := quasicategory_sliceOver X (i ≫ t)
  let _ : RightFibration (sliceOver.restrict B (t ≫ p) i) :=
    rightFibration_sliceOver_restrict B (t ≫ p) i
  let _ : RightFibration
      (pullback.fst (sliceOver.map X (i ≫ t) p) (sliceOver.restrict B (t ≫ p) i)) :=
    inferInstance
  let _ : InnerFibration
      (pullback.fst (sliceOver.map X (i ≫ t) p) (sliceOver.restrict B (t ≫ p) i)) :=
    inferInstance
  let _ : Quasicategory
      (pullback (sliceOver.map X (i ≫ t) p) (sliceOver.restrict B (t ≫ p) i)) :=
    quasicategory_of_innerFibration
      (pullback.fst (sliceOver.map X (i ≫ t) p) (sliceOver.restrict B (t ≫ p) i))
  let _ : RightFibration (sliceOver.restrictionComparison i t p) :=
    rightFibration_sliceOver_restrictionComparison i t p
  exact RightFibration.categoricalFibration _

/-- A generated right-anodyne restriction in a quasicategory under-slice is boundary-trivial. -/
theorem sliceUnder.rlp_I_restrict_of_rightAnodyne {K₀ K : SSet.{u}} (X : SSet.{u})
    [Quasicategory X] (i : K₀ ⟶ K) (hi : rightHornInclusions.rlp.llp i) (t : K ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceUnder.restrict X t i) := by
  apply (modelCategoryQuillen.I.rlp.arrow_mk_iso_iff
    (sliceUnder.restrictionComparisonTerminalArrowIso
      (terminalIsTerminal : IsTerminal (⊤_ SSet.{u})) i t (terminal.from X))).mp
  exact sliceUnder.rlp_I_restrictionComparison_of_rightAnodyne i hi t (terminal.from X)

/-- A generated left-anodyne restriction in a quasicategory over-slice is boundary-trivial. -/
theorem sliceOver.rlp_I_restrict_of_leftAnodyne {K₀ K : SSet.{u}} (X : SSet.{u})
    [Quasicategory X] (i : K₀ ⟶ K) (hi : leftHornInclusions.rlp.llp i) (t : K ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X t i) := by
  apply (modelCategoryQuillen.I.rlp.arrow_mk_iso_iff
    (sliceOver.restrictionComparisonTerminalArrowIso
      (terminalIsTerminal : IsTerminal (⊤_ SSet.{u})) i t (terminal.from X))).mp
  exact sliceOver.rlp_I_restrictionComparison_of_leftAnodyne i hi t (terminal.from X)

end SSet
