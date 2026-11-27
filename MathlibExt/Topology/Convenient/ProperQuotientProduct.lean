/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Products of compact Hausdorff quotients

A continuous surjection from a compact space to a Hausdorff space is proper.
Consequently, its product with the identity on an arbitrary topological space
is a closed quotient map in either product orientation. No local compactness
or separation property is required of the arbitrary factor.
-/

@[expose] public section

open Function Topology

universe u v w

namespace Topology.IsQuotientMap

variable {A : Type u} {B : Type v} {K : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace K]
  [CompactSpace A] [T2Space B]

/-- A compact-to-Hausdorff quotient in the left coordinate remains quotient
after product with an arbitrary right factor. -/
theorem prodMap_left_of_compact_to_t2 {q : A → B}
    (hqcont : Continuous q) (hqsurj : Surjective q) :
    IsQuotientMap (Prod.map q (id : K → K)) := by
  have hqproper : IsProperMap q :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2
      ⟨hqcont, hqcont.isClosedMap, fun b =>
        (isClosed_singleton.preimage hqcont).isCompact⟩
  have hprod : IsProperMap (Prod.map q (id : K → K)) :=
    hqproper.prodMap isProperMap_id
  exact hprod.isClosedMap.isQuotientMap hprod.continuous
    (hqsurj.prodMap surjective_id)

/-- A compact-to-Hausdorff quotient in the right coordinate remains quotient
after product with an arbitrary left factor. -/
theorem prodMap_right_of_compact_to_t2 {q : A → B}
    (hqcont : Continuous q) (hqsurj : Surjective q) :
    IsQuotientMap (Prod.map (id : K → K) q) := by
  have hqproper : IsProperMap q :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2
      ⟨hqcont, hqcont.isClosedMap, fun b =>
        (isClosed_singleton.preimage hqcont).isCompact⟩
  have hprod : IsProperMap (Prod.map (id : K → K) q) :=
    isProperMap_id.prodMap hqproper
  exact hprod.isClosedMap.isQuotientMap hprod.continuous
    (surjective_id.prodMap hqsurj)

end Topology.IsQuotientMap
