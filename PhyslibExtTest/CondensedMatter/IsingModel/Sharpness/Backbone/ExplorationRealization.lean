/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationRealization

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationRealization`

* `shb_segment_unrestricted_cut_factor`: the unrestricted mass factorizes across any segment cut
  (unconditional);
* `shb_segmentRho_eq_num_div`: the amplitude is the segment numerator over the partition function;
* `shb_randomCurrent_rho_eq_weight` applied under `LocalDomainResummation` (refuted on `K₄` in
  `SupportLexDomainResummationCounterexample`) and the cut resummation identities.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationRealization

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.shb_BackboneExplorationDomain

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The unrestricted mass factorizes across a segment cut.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (H : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) (s : shb_AmbientSegment V) :
    shb_fullWeightMass H β J =
      shb_cutLeftMass H β J (shb_segmentCut H s) * shb_cutRightMass H β J (shb_segmentCut H s) :=
  shb_segment_unrestricted_cut_factor H β J s

-- The segment amplitude.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    shb_BackboneExplorationDomain.amplitude β J d s =
      shb_segmentNum β J d s / currentSum d.graph β J ∅ :=
  shb_segmentRho_eq_num_div β J d s

-- The normalized `ρ` is the kernel weight, conditional on the domain resummation.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
    (f : shb_ExplorationFiberMass V) (hf : shb_LocalSelectorFiberCutResummation β J f)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho β J f d word =
      (shb_BackboneExplorationDomain.kernel β J hβ hJ hdom).weight d word :=
  shb_randomCurrent_rho_eq_weight β J hβ hJ hdom f hf d word

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationRealization
