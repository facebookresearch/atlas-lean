/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.PcFarContour

/-!
# Exit darts and the far-exit-heads condition

For a finite open cluster `C` of the origin in `ℤ²`, the right exit dart goes from `(j, 0)` to
`(j + 1, 0)`, where `j + 1` is the least positive integer with `(j + 1, 0) ∉ C`; the left exit dart
is its mirror image. This file computes when their heads lie outside the box `[-R, R]²` and shows
that the condition `StatMech.Percolation.pcFar_ExitHeadsFar` (both heads outside a box containing
`C`) forces the two exit indices to coincide with the radius of `C` along the axis. It fails for
the two-site cluster `{(0, 0), (0, 1)}`, so its universal form is unsatisfiable
(`StatMech.Percolation.not_forall_pcFar_ExitHeadsFar`).

It also shows that the far axis points `(± (R + 1), 0)` are joined outside every finite cluster
contained in `[-R, R]²` (`StatMech.Percolation.outC_farAxisHeadsFar_discharge`).

## Main definitions

* `StatMech.Percolation.outC_FarAxisHeadsFar`: the far axis points are outside a box containing
  the cluster and joined in its complement.
* `StatMech.Percolation.outC_upEdgeConfig`: the configuration whose only open edge joins `(0, 0)`
  and `(0, 1)`.

## Main results

* `StatMech.Percolation.outC_pcFarExitHeadsFar_forces_eq`: `pcFar_ExitHeadsFar` forces
  `exitIndex = leftExitIndex = R` and `C ⊆ [-R, R]²`.
* `StatMech.Percolation.not_forall_pcFar_ExitHeadsFar`: `pcFar_ExitHeadsFar` does not hold for
  every configuration with a finite origin cluster.
* `StatMech.Percolation.outC_farAxisHeadsFar_discharge`.
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}

private theorem outC_natAbs_succ (j : ℕ) : ((j : ℤ) + 1).natAbs = j + 1 := by
  rw [Int.natAbs_eq_iff]; left; push_cast; ring

private theorem outC_natAbs_neg_succ (j : ℕ) : (-((j : ℤ) + 1)).natAbs = j + 1 := by
  rw [Int.natAbs_eq_iff]; right; push_cast; ring

/-- The head `(j + 1, 0)` of the right exit dart lies outside `[-R, R]²` iff `R ≤ j`. -/
theorem outC_exitHead_mem_exterior_iff (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (exitDart (ω := ω) hfin).head ∈ exterior 2 R ↔ R ≤ exitIndex (ω := ω) hfin := by
  rw [exitDart_head]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · have hval : (axisSite (exitIndex (ω := ω) hfin + 1) : Site 2) ⟨0, by omega⟩
          = (exitIndex (ω := ω) hfin : ℤ) + 1 := by simp [axisSite]
      rw [hval, outC_natAbs_succ] at hi; omega
    · simp [axisSite] at hi
  · intro h
    refine ⟨0, ?_⟩
    have hval : (axisSite (exitIndex (ω := ω) hfin + 1) : Site 2) 0
        = (exitIndex (ω := ω) hfin : ℤ) + 1 := by simp [axisSite]
    rw [hval, outC_natAbs_succ]; omega

/-- The head `(-(j + 1), 0)` of the left exit dart lies outside `[-R, R]²` iff `R ≤ j`. -/
theorem outC_leftExitHead_mem_exterior_iff (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R ↔ R ≤ leftExitIndex (ω := ω) hfin := by
  rw [leftExitDart_head]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2) ⟨0, by omega⟩
          = -((leftExitIndex (ω := ω) hfin : ℤ) + 1) := by
        rw [leftAxisSite_succ_eq]; simp; ring
      rw [hval, outC_natAbs_neg_succ] at hi; omega
    · have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2) ⟨1, by omega⟩
          = 0 := by rw [leftAxisSite_succ_eq]; simp
      rw [hval] at hi; simp at hi
  · intro h
    refine ⟨0, ?_⟩
    have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2) 0
        = -((leftExitIndex (ω := ω) hfin : ℤ) + 1) := by
      rw [leftAxisSite_succ_eq]; simp; ring
    rw [hval, outC_natAbs_neg_succ]; omega

/-- If the cluster lies in `[-R, R]²`, the right exit index is at most `R`. -/
theorem outC_clusterBox_ge_exitIndex (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) : exitIndex (ω := ω) hfin ≤ R := by
  have hmem := axisSite_exit_mem (ω := ω) hfin
  have hbox := hR hmem
  have h0 := hbox 0
  simpa [axisSite] using h0

/-- If the cluster lies in `[-R, R]²`, the left exit index is at most `R`. -/
theorem outC_clusterBox_ge_leftExitIndex (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) : leftExitIndex (ω := ω) hfin ≤ R := by
  have hmem := leftAxisSite_exit_mem (ω := ω) hfin
  have hbox := hR hmem
  have h0 := hbox 0
  have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin) : Site 2) 0
      = -(leftExitIndex (ω := ω) hfin : ℤ) := rfl
  rw [hval] at h0
  rwa [Int.natAbs_neg, Int.natAbs_natCast] at h0

/-- `pcFar_ExitHeadsFar` forces the box radius to equal both exit indices. -/
theorem outC_pcFarExitHeadsFar_forces_eq (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : pcFar_ExitHeadsFar ω hfin) :
    ∃ R : ℕ, R = exitIndex (ω := ω) hfin ∧ R = leftExitIndex (ω := ω) hfin ∧
      cluster 2 ω (origin 2) ⊆ box 2 (exitIndex (ω := ω) hfin) := by
  obtain ⟨R, hR, hr, hl⟩ := h
  have h1 : R ≤ exitIndex (ω := ω) hfin := (outC_exitHead_mem_exterior_iff (ω := ω) hfin R).mp hr
  have h2 : exitIndex (ω := ω) hfin ≤ R := outC_clusterBox_ge_exitIndex (ω := ω) hfin R hR
  have h3 : R ≤ leftExitIndex (ω := ω) hfin :=
    (outC_leftExitHead_mem_exterior_iff (ω := ω) hfin R).mp hl
  have h4 : leftExitIndex (ω := ω) hfin ≤ R := outC_clusterBox_ge_leftExitIndex (ω := ω) hfin R hR
  have hRe : R = exitIndex (ω := ω) hfin := le_antisymm h1 h2
  have hRl : R = leftExitIndex (ω := ω) hfin := le_antisymm h3 h4
  refine ⟨R, hRe, hRl, ?_⟩
  rw [← hRe]; exact hR

/-- `pcFar_ExitHeadsFar` forces the right and left exit indices to be equal. -/
theorem outC_pcFarExitHeadsFar_imp_exitIndex_eq (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : pcFar_ExitHeadsFar ω hfin) :
    exitIndex (ω := ω) hfin = leftExitIndex (ω := ω) hfin := by
  obtain ⟨R, hRe, hRl, _⟩ := outC_pcFarExitHeadsFar_forces_eq (ω := ω) hfin h
  rw [← hRe, ← hRl]

/-- `pcFar_ExitHeadsFar` fails whenever the right and left exit indices differ. -/
theorem outC_not_pcFarExitHeadsFar_of_exitIndex_ne (hfin : (cluster 2 ω (origin 2)).Finite)
    (hne : exitIndex (ω := ω) hfin ≠ leftExitIndex (ω := ω) hfin) :
    ¬ pcFar_ExitHeadsFar ω hfin :=
  fun h => hne (outC_pcFarExitHeadsFar_imp_exitIndex_eq (ω := ω) hfin h)

/-- `(R + 1, 0)` is outside a cluster contained in `[-R, R]²`. -/
theorem outC_axisFarRight_mem_compl (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    (![(R : ℤ) + 1, 0] : Site 2) ∈ (cluster 2 ω (origin 2))ᶜ :=
  exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)

/-- `(-(R + 1), 0)` is outside a cluster contained in `[-R, R]²`. -/
theorem outC_axisFarLeft_mem_compl (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∈ (cluster 2 ω (origin 2))ᶜ :=
  exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)

/-- For some `R`, the cluster of the origin lies in `[-R, R]²`, the points `(± (R + 1), 0)` lie
outside `[-R, R]²`, and they are joined by a lattice path avoiding the cluster. -/
def outC_FarAxisHeadsFar (ω : ConfigSpace (Sym2 (Site 2)))
    (_hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R),
    (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R ∧
    (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R ∧
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨![(R : ℤ) + 1, 0], outC_axisFarRight_mem_compl R hR⟩
      ⟨![-((R : ℤ) + 1), 0], outC_axisFarLeft_mem_compl R hR⟩

/-- `outC_FarAxisHeadsFar` holds for every finite cluster of the origin. -/
theorem outC_farAxisHeadsFar_discharge (hfin : (cluster 2 ω (origin 2)).Finite) :
    outC_FarAxisHeadsFar ω hfin := by
  obtain ⟨R, hR⟩ := exists_clusterBox (ω := ω) hfin
  exact ⟨R, hR, axisFarRight_mem_exterior R, axisFarLeft_mem_exterior R,
    axisFar_reachable_in_clusterComplement (ω := ω) R hR⟩

/-- The configuration in which the single edge from the origin to `(0, 1)` is open. -/
def outC_upEdgeConfig : ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e => decide (e = s(origin 2, ![0, 1]))

/-- The cluster of the origin in `outC_upEdgeConfig` is contained in `{(0, 0), (0, 1)}`. -/
theorem outC_upEdgeConfig_cluster_subset :
    cluster 2 outC_upEdgeConfig (origin 2) ⊆ {origin 2, ![0, 1]} := by
  intro y hy
  obtain ⟨w⟩ := (show Connected 2 outC_upEdgeConfig (origin 2) y from hy)
  suffices ∀ {x y : Site 2} (w : (openSubgraph 2 outC_upEdgeConfig).Walk x y),
      x ∈ ({origin 2, ![0, 1]} : Set (Site 2)) → y ∈ ({origin 2, ![0, 1]} : Set (Site 2)) from
    this w (by simp)
  intro x y w
  induction w with
  | nil => exact id
  | cons hadj _ ih =>
    intro _
    apply ih
    have h2 := hadj.2
    simp only [outC_upEdgeConfig, decide_eq_true_eq] at h2
    rcases Sym2.eq_iff.mp h2 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- `(0, 1)` is in the cluster of the origin in `outC_upEdgeConfig`. -/
theorem outC_upEdgeConfig_up_mem :
    (![0, 1] : Site 2) ∈ cluster 2 outC_upEdgeConfig (origin 2) := by
  refine IsOpenEdge.connected ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj]; decide
  · simp [outC_upEdgeConfig]

/-- `pcFar_ExitHeadsFar` is not satisfied by every configuration with a finite origin cluster.
In `outC_upEdgeConfig` the cluster is `{(0, 0), (0, 1)}`: the right exit index is `0`, which
forces the box radius to be `0`, but `(0, 1)` is not in `[0, 0]²`. Hence every theorem assuming
`∀ ω hfin, pcFar_ExitHeadsFar ω hfin` is vacuous. -/
theorem not_forall_pcFar_ExitHeadsFar :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
      pcFar_ExitHeadsFar ω hfin := by
  intro h
  have hfin : (cluster 2 outC_upEdgeConfig (origin 2)).Finite :=
    (Set.toFinite _).subset outC_upEdgeConfig_cluster_subset
  obtain ⟨R, hR, hr, -⟩ := h _ hfin
  have hidx : exitIndex (ω := outC_upEdgeConfig) hfin = 0 := by
    classical
    refine Nat.eq_zero_of_le_zero (Nat.find_min' _ ?_)
    intro hmem
    rcases outC_upEdgeConfig_cluster_subset hmem with h | h
    · have := congrFun h 0; simp [axisSite, origin] at this
    · have := congrFun h 0; simp [axisSite] at this
  have hR0 : R = 0 := by
    have := (outC_exitHead_mem_exterior_iff hfin R).mp hr
    omega
  subst hR0
  have := hR outC_upEdgeConfig_up_mem 1
  simp at this

end Percolation

end StatMech
