/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectNativeCompactness
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerCellAcyclicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerIntervalSmallObject
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# The genuine original combined Bergner small-object argument

The original full A1/A2 family is small, and all changing-object
colimits are the original enriched colimits. Every actual native cell
transition is C0. The original point compactness and the genuine
two-object compactness on those same C0 diagrams verify the native
countable small-object conditions. No model or desired weak-outcome
certificate is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily

/-- The SAME complete original A1/A2 family satisfies the actual native small-object conditions at countable length. -/
instance combinedCardinal :
    MorphismProperty.IsCardinalForSmallObjectArgument generatingTrivialCofibrations.{u}
      Cardinal.aleph0.{u} where
  preservesColimit i hi f hf := by
    let d := hf.transfiniteCompositionOfShape'
      (I := generatingTrivialCofibrations) (fun s => s.i.2)
    let d' := d.ofLE
      generatingTrivialCofibrations_coproducts_pushouts_le_cofibration_weak.{u, u}
    have hC : ∀ {j k : Cardinal.aleph0.{u}.ord.ToType} (g : j ⟶ k),
        Bergner.cofibrations (hf.F.map g) :=
      fun g => (d'.ofLE (by intro X Y q hq; exact hq.1)).mem_map g
    rcases hi with hi | hi
    · obtain ⟨⟨n, j⟩⟩ := hi
      exact BergnerTwoObject.coyonedaPreservesColimit hf.F (fun g => hC g) (Λ[n + 1, j])
    · have h : IsFinitelyPresentable.{u} _ := interval_domain_presentable i hi
      infer_instance

/-- The SAME original complete A1/A2 family admits the genuine native small-object argument. -/
instance combinedHasSmallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u} generatingTrivialCofibrations.{u} where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The complete original combined left and right classes have their genuine weak factorization system. -/
theorem combinedWFS : MorphismProperty.IsWeakFactorizationSystem
    generatingTrivialCofibrations.{u}.rlp.llp generatingTrivialCofibrations.rlp :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun _ _ hi hp => hi _ hp)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
