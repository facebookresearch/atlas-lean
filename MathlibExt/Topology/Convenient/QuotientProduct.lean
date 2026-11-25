/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Constructions

/-!
# Whitehead product kernel for quotient maps

Product with the identity on a locally compact fixed factor preserves quotient
maps, in both orientations. This is the reusable kernel behind the staged
evaluation-quotient argument and the planned locally compact pushout bridge.
Mathematical source: Whitehead's lemma via the pinned
`continuous_lift_prod_left/right` characterization; reconstructed here from
pinned APIs only.

No `DeltaGeneratedSpace`, colimit, pushout, realization, or model-category
claim is made here. No `TopCat` transport is provided here.
-/

@[expose] public section

open Topology

namespace Topology.IsQuotientMap

variable {A B K : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace K] [LocallyCompactSpace K]

/-- Quotient on the left, identity on a locally compact right factor. -/
theorem prodMap_left {q : A → B} (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map q (id : K → K)) := by
  refine ⟨?_, hq.surjective.prodMap (fun y => ⟨y, rfl⟩)⟩
  · rw [isCoinducing_iff]
    intro s
    constructor
    · intro hPre
      rw [isOpen_iff_continuous_mem]
      have hPreCont : Continuous (· ∈ (Prod.map q id) ⁻¹' s) :=
        isOpen_iff_continuous_mem.mp hPre
      have hComp : Continuous ((· ∈ s) ∘ Prod.map q id) := hPreCont
      exact hq.continuous_lift_prod_left hComp
    · intro h
      exact h.preimage (hq.continuous.prodMap continuous_id)

/-- Identity on a locally compact left factor, quotient on the right. -/
theorem prodMap_right {q : A → B} (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map id q : K × A → K × B) := by
  have hMid : IsQuotientMap (Prod.map q id : A × K → B × K) :=
    hq.prodMap_left
  have hComm1 : IsQuotientMap (Homeomorph.prodComm K A) :=
    (Homeomorph.prodComm K A).isQuotientMap
  have hComm2 : IsQuotientMap (Homeomorph.prodComm B K) :=
    (Homeomorph.prodComm B K).isQuotientMap
  have hEq : Prod.map id q =
      (Homeomorph.prodComm B K) ∘ (Prod.map q id) ∘ (Homeomorph.prodComm K A) := by
    funext p
    rfl
  rw [hEq]
  exact hComm2.comp (hMid.comp hComm1)

variable {C D : Type*} [TopologicalSpace C] [TopologicalSpace D]

/-- Product of two quotient maps, factored left-then-right as
  `(q × id_C)` followed by `(id_B × r)`. Needs local compactness of the
  middle factors `C` (right source) and `B` (left target); no joint
  compactness on `A` or `D` is claimed. -/
theorem prodMap_prod {q : A → B} {r : C → D} [LocallyCompactSpace C]
    [LocallyCompactSpace B] (hq : IsQuotientMap q) (hr : IsQuotientMap r) :
    IsQuotientMap (Prod.map q r) := by
  have hLeft : IsQuotientMap (Prod.map q (id : C → C)) := hq.prodMap_left
  have hRight : IsQuotientMap (Prod.map (id : B → B) r) := hr.prodMap_right
  have hEq : Prod.map q r =
      (Prod.map (id : B → B) r) ∘ (Prod.map q (id : C → C)) := by
    funext ⟨a, c⟩
    rfl
  rw [hEq]
  exact hRight.comp hLeft

end Topology.IsQuotientMap
