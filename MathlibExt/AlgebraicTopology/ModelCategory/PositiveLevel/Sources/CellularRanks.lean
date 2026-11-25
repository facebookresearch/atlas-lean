/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationSmallness

/-!
# Actual common source ranks for the cellular R-module branch

The original base I/J source and target objects retain the cellular compactness
and relative smallness data. The established original cofibration-chain
transport gives a common regular rank for those very same objects. It is a
source-rank construction; it assumes no R-module model or factorization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.PositiveLevelModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)

local instance baseJSmall : d.J.IsSmall.{w} := d.J_smallObject.isSmall

/-- Each original J target retains the bound of its established actual relative-I smallness. -/
def cellularJTargetBound (j : d.J.toSet) : Cardinal.{w} :=
  (CellularLocalizationSmallness.J_codomain_uniformly_small h j).choose

/-- The actual original J target family has one genuine common bound. -/
def cellularJTargetCommonBound : Cardinal.{w} :=
  max Cardinal.aleph0
    (⨆ k : Shrink.{w} d.J.toSet, cellularJTargetBound d h ((equivShrink d.J.toSet).symm k))

/-- Every original J target bound lies below the same common family bound. -/
theorem cellularJTargetBound_le_common (j : d.J.toSet) :
    cellularJTargetBound d h j ≤ cellularJTargetCommonBound d h := by
  have hle := le_ciSup
    (f := fun k : Shrink.{w} d.J.toSet => cellularJTargetBound d h ((equivShrink d.J.toSet).symm k))
    Cardinal.bddAbove_of_small ((equivShrink d.J.toSet) j)
  simpa only [cellularJTargetCommonBound, Equiv.symm_apply_apply] using hle.trans (le_max_right _ _)

/-- A produced actual regular cardinal and original bottom for all four source/target families. -/
structure CellularModuleGenerationRank where
  /-- The actual common regular cardinal produced from the original cellular sources. -/
  cardinal : Cardinal.{w}
  regular : Fact cardinal.IsRegular
  /-- The ordinal bottom selected with this actual common cardinal. -/
  orderBot : OrderBot cardinal.ord.ToType
  baseCardinal_lt : κ < cardinal
  compact_lt : CellularLocalizationSmallness.commonCompactBound h < cardinal
  sourceJ_lt : CellularLocalizationSmallness.commonSmallBound h < cardinal
  targetJ_lt : cellularJTargetCommonBound d h < cardinal

/-- The original compact and small families produce the common rank through the existing source
bound theorem. -/
def cellularModuleGenerationRank : CellularModuleGenerationRank d h := by
  apply Classical.choice
  obtain ⟨μ, hμ, hκ, hi, hj, ht⟩ :=
    CellularLocalizationSmallness.existsCommonRegularBound h
      (cellularJTargetCommonBound d h).ord.ToType
  let _ : Fact μ.IsRegular := ⟨hμ⟩
  let _ : Nonempty μ.ord.ToType := Cardinal.nonempty_ord_toType hμ.ne_zero
  let bottom : OrderBot μ.ord.ToType := WellFoundedLT.toOrderBot μ.ord.ToType
  have htarget : cellularJTargetCommonBound d h < μ := by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using ht
  exact ⟨⟨μ, inferInstance, bottom, hκ, hi, hj, htarget⟩⟩

namespace CellularModuleGenerationRank

variable (e : CellularModuleGenerationRank d h)

local instance rankRegular : Fact e.cardinal.IsRegular := e.regular
/-- The retained ordinal bottom of the supplied source rank. -/
local instance rankBottom : OrderBot e.cardinal.ord.ToType := e.orderBot

/-- The original I domain Hom preserves the caller's exact continuous cofibration chain at the
produced rank. -/
theorem I_source_preservesColimit (i : d.I.toSet)
    (F : e.cardinal.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (f : a ⟶ b), cofibrations C (F.map f)) :
    PreservesColimit F (coyoneda.obj (op i.1.left)) :=
  CellularLocalizationSmallness.preserves_original_cofibration_chain_of_compact h
    (CellularLocalizationSmallness.domain_compact h i) e.cardinal e.compact_lt F
    (fun a _ => hF (homOfLE (Order.le_succ a)))

/-- The original I target Hom preserves the same entire actual chain at that exact rank. -/
theorem I_target_preservesColimit (i : d.I.toSet)
    (F : e.cardinal.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (f : a ⟶ b), cofibrations C (F.map f)) :
    PreservesColimit F (coyoneda.obj (op i.1.right)) :=
  CellularLocalizationSmallness.preserves_original_cofibration_chain_of_compact h
    (CellularLocalizationSmallness.codomain_compact h i) e.cardinal e.compact_lt F
    (fun a _ => hF (homOfLE (Order.le_succ a)))

/-- The original J source Hom preserves the caller's exact cofibration chain without a compactness
premise on J. -/
theorem J_source_preservesColimit (j : d.J.toSet)
    (F : e.cardinal.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (f : a ⟶ b), cofibrations C (F.map f)) :
    PreservesColimit F (coyoneda.obj (op j.1.left)) :=
  CellularCofibrationTransport.preservesOriginalCofibrationChain d (h.J_domains_small j) e.cardinal
    ((CellularLocalizationSmallness.smallBound_le_common h j).trans_lt e.sourceJ_lt) F
    (fun a _ => hF (homOfLE (Order.le_succ a)))

/-- The actual J target Hom preserves that same caller chain using the separately earned target
bound. -/
theorem J_target_preservesColimit (j : d.J.toSet)
    (F : e.cardinal.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (f : a ⟶ b), cofibrations C (F.map f)) :
    PreservesColimit F (coyoneda.obj (op j.1.right)) :=
  CellularCofibrationTransport.preservesOriginalCofibrationChain d
    (CellularLocalizationSmallness.J_codomain_uniformly_small h j) e.cardinal
    ((cellularJTargetBound_le_common d h j).trans_lt e.targetJ_lt) F
    (fun a _ => hF (homOfLE (Order.le_succ a)))

end CellularModuleGenerationRank

end HomotopicalAlgebra.PositiveLevelModel
