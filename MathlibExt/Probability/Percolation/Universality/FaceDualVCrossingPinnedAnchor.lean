/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingAnchor

/-!
# Pinning the anchor of the frontier faces

The anchor condition `ccc_FrontierReachesBottom` asks for *some* face reached in the box face
barrier from every right-frontier face. This file shows that the anchor can be taken to be the
face `![c₀, -1]` just below the row-`0` frontier `(c₀, 0)` (`cac_FrontierReachesBottomAtAnchor`),
and that the two conditions are equivalent under `¬ HorizontalCrossing ω 0 n 0 n`. It also
records that the box face barrier is a subgraph of the face boundary graph of the left cluster.

## Main definitions

* `cac_AllFrontierReachAnchor ω n a₀ b₀`: every right-frontier face reaches `![a₀, b₀]`.
* `cac_FrontierReachesBottomAtAnchor ω n`: every right-frontier face reaches `![c₀, -1]`,
  `c₀` the row-`0` frontier.

## Main results

* `cac_boxFaceBarrier_le_faceBoundaryGraph`:
  `pmd_boxFaceBarrier ω n ≤ faceBoundaryGraph (bcd_leftReach ω n)`.
* `cac_atom_of_pinned`, `cac_pinned_of_atom`: equivalence of the pinned and unpinned anchor
  conditions.
* `cac_wall_frontierReachesBottomAtAnchor`: the pinned condition holds on the wall configuration.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- The box face barrier is a subgraph of the face boundary graph of the left cluster. -/
theorem cac_boxFaceBarrier_le_faceBoundaryGraph (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pmd_boxFaceBarrier ω n ≤ faceBoundaryGraph (bcd_leftReach ω n) := by
  rintro f g ⟨hadj, p, q, hpq, hbd, _hp, _hq⟩
  exact ⟨hadj, by rw [hpq]; exact hbd⟩

/-- Every right-frontier face `![c, r]`, `r ∈ [0, n]`, reaches the face `![a₀, b₀]` in the box
face barrier. -/
def cac_AllFrontierReachAnchor (ω : ConfigSpace (Sym2 (Site 2))) (n a₀ b₀ : ℤ) : Prop :=
  ∀ (r : ℤ), 0 ≤ r → r ≤ n → ∀ (c : ℤ), mbc_IsRightFrontier ω n c r →
    (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀]

/-- An anchor in the admissible range gives the anchor condition `ccc_FrontierReachesBottom`. -/
theorem cac_frontierReachesBottom_of_anchor (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a₀ b₀ : ℤ} (ha0 : 0 ≤ a₀) (ha0' : a₀ ≤ n - 1) (hb0 : -1 ≤ b₀) (hb0' : b₀ ≤ n)
    (h : cac_AllFrontierReachAnchor ω n a₀ b₀) : ccc_FrontierReachesBottom ω n :=
  ⟨a₀, b₀, ha0, ha0', hb0, hb0', h⟩

/-- The row-`0` frontier face `![c₀, 0]` reaches the face `![c₀, -1]` below the box. -/
theorem cac_row0_frontier_reaches_bottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) {c₀ : ℤ} (h0 : mbc_IsRightFrontier ω n c₀ 0) :
    (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![c₀, -1] := by
  have h := ccc_frontierFace_down_adj ω n (le_refl 0) hn h0
  have he : ((0 : ℤ) - 1) = (-1 : ℤ) := by ring
  rw [he] at h
  exact h.reachable

/-- Pinned anchor condition: for the row-`0` frontier `c₀`, every right-frontier face reaches
`![c₀, -1]` in the box face barrier. A hypothesis, not proved for general `ω`. -/
def cac_FrontierReachesBottomAtAnchor (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ (c₀ : ℤ), mbc_IsRightFrontier ω n c₀ 0 →
    cac_AllFrontierReachAnchor ω n c₀ (-1)

/-- The pinned anchor condition implies the anchor condition (given no horizontal crossing). -/
theorem cac_atom_of_pinned (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (h : cac_FrontierReachesBottomAtAnchor ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  exact cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega) (h c₀ hc₀)

/-- The anchor condition implies the pinned anchor condition. -/
theorem cac_pinned_of_atom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (h : ccc_FrontierReachesBottom ω n) : cac_FrontierReachesBottomAtAnchor ω n := by
  obtain ⟨a₀, b₀, _, _, _, _, hanchor⟩ := h
  intro c₀ hc₀ r hr0 hrn c hc
  have h1 : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀] := hanchor r hr0 hrn c hc
  have h2 : (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![a₀, b₀] :=
    hanchor 0 (le_refl 0) hn c₀ hc₀
  have h3 : (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![c₀, -1] :=
    cac_row0_frontier_reaches_bottom ω n hn hc₀
  exact (h1.trans h2.symm).trans h3

/-- The pinned anchor condition holds for the wall configuration. -/
theorem cac_wall_frontierReachesBottomAtAnchor :
    cac_FrontierReachesBottomAtAnchor bcc_wallCfg 2 :=
  cac_pinned_of_atom bcc_wallCfg 2 (by norm_num) ccc_wall_frontierReachesBottom

end Universality

end StatMech
