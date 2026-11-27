/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Bases

/-!
# Second countability of one-point compactifications

Let X be a locally compact Hausdorff space with a countable topological
basis. Its one-point compactification, with neighborhoods of infinity given
by complements of compact sets, is second countable. A countable basis of X
and a compact exhaustion supply the basis at finite points and infinity.
Compact and empty X are included.
-/

@[expose] public section

open Set TopologicalSpace Topology

universe uX

namespace OnePoint

/-- Let X be a Hausdorff, locally compact, second-countable topological space.
The one-point compactification OnePoint X is second countable. -/
theorem secondCountableTopology (X : Type uX) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (OnePoint X) := by
  classical
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let tail : ℕ → Set (OnePoint X) := fun n ↦ (some '' K n)ᶜ
  let B : Set (Set (OnePoint X)) :=
    Set.image some '' countableBasis X ∪ range tail
  have hCount : B.Countable :=
    ((countable_countableBasis X).image (Set.image some)).union (countable_range tail)
  have hBasis : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with hU | hU
      · obtain ⟨V, hV, rfl⟩ := hU
        exact isOpen_image_coe.2 (isOpen_of_mem_countableBasis hV)
      · obtain ⟨n, rfl⟩ := hU
        exact isOpen_compl_image_coe.2 ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro x U hx hU
      induction x using OnePoint.rec with
      | infty =>
          obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact
            ((isOpen_iff_of_mem hx).1 hU).2
          refine ⟨tail n, Or.inr (mem_range_self n), ?_, ?_⟩
          · exact infty_notMem_image_coe
          · intro z hz
            induction z using OnePoint.rec with
            | infty => exact hx
            | coe z =>
                by_contra hzU
                exact hz (mem_image_of_mem some (hn hzU))
      | coe x =>
          obtain ⟨V, hV, hxV, hVU⟩ :=
            (isBasis_countableBasis X).exists_subset_of_mem_open hx
              (hU.preimage continuous_coe)
          refine ⟨some '' V, Or.inl (mem_image_of_mem (Set.image some) hV),
            mem_image_of_mem some hxV, ?_⟩
          rintro z ⟨w, hw, rfl⟩
          exact hVU hw
  exact hBasis.secondCountableTopology hCount

end OnePoint
