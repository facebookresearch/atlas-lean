/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafSelection

/-!
# Boundary traces and arm injections

The boundary trace of a connected family of trifurcations bounds forest leaf selection; forest leaf
selection gives the boundary arm injection and the trifurcation count.

## i. Overview

`lhc_trace ω n x₀` is the set of boundary sites connected to `x₀`. When all trifurcations of the box
are connected to `x₀`, forest leaf selection `str_ForestLeafSelection` gives
`2 · Tcount + 1 ≤ |∂Λₙ|`. So a connected claw trace (`lhc_ConnectedClawTrace`), with fewer than
`2 · Tcount` boundary sites, rules out forest leaf selection. Forest leaf selection gives the
boundary arm injection `tfc_BoundaryArmInjection` and the count bound. A single trifurcation with a
boundary arm gives the injection directly.

The configuration-wide form of this condition, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`lhc_not_forall_boundaryArmInjection`). The Burton–Keane theorem that assumed it was removed as
vacuous.

## ii. Key results

- `lhc_twice_Tcount_succ_le_boundary` : `2 · Tcount + 1 ≤ |∂Λₙ|` from forest leaf selection.
- `lhc_boundaryArmInjection_of_forestLeafSelection` : the boundary arm injection from forest leaf
  selection.

## iii. Table of contents

- A. Boundary traces
- B. Connected claw traces
- C. Boundary arm injection
- D. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Boundary traces -/

open Classical in
/-- The boundary sites of the box of radius `n` connected to `x₀`. Same statement as
`bk2_armEndFinset`;
kept because replacing a definition changes the statements that mention it. -/
noncomputable def lhc_trace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d) :
    Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d ω x₀ z)

lemma lhc_mem_trace {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x₀ z : Site d} :
    z ∈ lhc_trace ω n x₀ ↔ z ∈ vertexBoundary d n ∧ Connected d ω x₀ z := by
  classical
  rw [lhc_trace, Finset.mem_filter, tfc_mem_boundaryFinset]

lemma lhc_trace_card_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d) :
    (lhc_trace ω n x₀).card ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_boundaryFinset_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

open Classical in
lemma lhc_two_le_trace_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d)
    (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
    (h : str_ForestLeafSelection ω n) :
    2 * Tcount d ω n ≤ (lhc_trace ω n x₀).card := by
  classical
  obtain ⟨r₀, ℓ, _hr₀, hℓbdry, hℓconn, _hℓr₀, hℓinj⟩ := h
  rw [← tfc_trifFinset_card]
  set T := tfc_trifFinset ω n with hT
  set ι := {x // x ∈ T} × Fin 2 with hι
  set f : ι → Site d := fun q => ℓ q.1.1 q.2 with hf
  have hfinj : Function.Injective f := by
    intro p q hpq
    have hp := tfc_mem_trifFinset.mp p.1.2
    have hq := tfc_mem_trifFinset.mp q.1.2
    obtain ⟨hxy, hjj⟩ := hℓinj p.1.1 hp.1 hp.2 q.1.1 hq.1 hq.2 p.2 q.2 hpq
    exact Prod.ext (Subtype.ext hxy) hjj
  have hfmem : ∀ q : ι, f q ∈ lhc_trace ω n x₀ := by
    intro q
    have hq := tfc_mem_trifFinset.mp q.1.2
    exact lhc_mem_trace.mpr ⟨hℓbdry q.1.1 hq.1 hq.2 q.2,
      (hconn q.1.1 hq.1 hq.2).trans (hℓconn q.1.1 hq.1 hq.2 q.2)⟩
  have hcardι : Fintype.card ι = 2 * T.card := by
    simp only [hι, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]; ring
  have hle := Finset.card_le_card_of_injOn (f := f) (s := (Finset.univ : Finset ι))
    (t := lhc_trace ω n x₀) (fun q _ => hfmem q) (fun p _ q _ hpq => hfinj hpq)
  rw [Finset.card_univ, hcardι] at hle
  omega

lemma lhc_twice_Tcount_succ_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    2 * Tcount d ω n + 1 ≤ boxSV_boundaryCard d n := by
  classical
  obtain ⟨r₀, ℓ, hr₀, hℓbdry, _hℓconn, hℓr₀, hℓinj⟩ := h
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  set T := tfc_trifFinset ω n with hT
  set ι := Option ({x // x ∈ T} × Fin 2) with hι
  set f : ι → Site d := fun p => p.elim r₀ (fun q => ℓ q.1.1 q.2) with hf
  have hfinj : Function.Injective f := by
    intro p q hpq
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q' =>
          exact absurd hpq.symm
            ((tfc_mem_trifFinset.mp q'.1.2).elim (fun hb ht => hℓr₀ q'.1.1 hb ht q'.2))
    | some p' =>
      cases q with
      | none =>
          exact absurd hpq
            ((tfc_mem_trifFinset.mp p'.1.2).elim (fun hb ht => hℓr₀ p'.1.1 hb ht p'.2))
      | some q' =>
          have hp := tfc_mem_trifFinset.mp p'.1.2
          have hq := tfc_mem_trifFinset.mp q'.1.2
          obtain ⟨hxy, hjj⟩ := hℓinj p'.1.1 hp.1 hp.2 q'.1.1 hq.1 hq.2 p'.2 q'.2 hpq
          exact congrArg some (Prod.ext (Subtype.ext hxy) hjj)
  have hfmem : ∀ p : ι, f p ∈ tfc_boundaryFinset d n := by
    intro p
    cases p with
    | none => exact tfc_mem_boundaryFinset.mpr hr₀
    | some q' =>
        have hq := tfc_mem_trifFinset.mp q'.1.2
        exact tfc_mem_boundaryFinset.mpr (hℓbdry q'.1.1 hq.1 hq.2 q'.2)
  have hcardι : Fintype.card ι = 2 * T.card + 1 := by
    simp only [hι, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    ring
  have hle := Finset.card_le_card_of_injOn (f := f) (s := (Finset.univ : Finset ι))
    (t := tfc_boundaryFinset d n) (fun p _ => hfmem p) (fun p _ q _ hpq => hfinj hpq)
  rw [Finset.card_univ, hcardι] at hle
  omega

/-! ## B. Connected claw traces -/

/-- All trifurcations of the box are connected to some `x₀` whose boundary trace has fewer than
`2 · Tcount` sites. -/
def lhc_ConnectedClawTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ x₀ : Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x) ∧
    (lhc_trace ω n x₀).card < 2 * Tcount d ω n

lemma lhc_not_forestLeafSelection_of_clawTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : lhc_ConnectedClawTrace ω n) :
    ¬ str_ForestLeafSelection ω n := by
  rintro h
  obtain ⟨x₀, hconn, hsmall⟩ := hclaw
  have hge := lhc_two_le_trace_of_forestLeafSelection ω n x₀ hconn h
  omega

lemma lhc_clawTrace_excludes_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : lhc_ConnectedClawTrace ω n) (h : str_ForestLeafSelection ω n) : False :=
  lhc_not_forestLeafSelection_of_clawTrace ω n hclaw h

lemma lhc_clawTrace_card_consistent {T : ℕ} (hT : 3 ≤ T) :
    T + 2 ≤ T + 2 ∧ T + 2 < 2 * T :=
  ⟨le_refl _, by omega⟩

lemma lhc_clawTrace_of_smallTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d)
    (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
    (hsmall : (lhc_trace ω n x₀).card < 2 * Tcount d ω n) :
    lhc_ConnectedClawTrace ω n :=
  ⟨x₀, hconn, hsmall⟩

/-! ## C. Boundary arm injection -/

lemma lhc_boundaryArmInjection_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    tfc_BoundaryArmInjection ω n := by
  obtain ⟨r₀, ℓ, _hr₀, hℓbdry, _hℓconn, _hℓr₀, hℓinj⟩ := h
  refine ⟨fun x => ℓ x 0, ?_, ?_⟩
  · intro x hxbox htri; exact hℓbdry x hxbox htri 0
  · intro x hxbox htri y hybox htriy hxy
    exact (hℓinj x hxbox htri y hybox htriy 0 0 hxy).1

lemma lhc_Tcount_le_boundary_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_residue ω n
    (lhc_boundaryArmInjection_of_forestLeafSelection ω n h)

lemma lhc_boundaryArmInjection_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r a : Site d} (ha : a ∈ vertexBoundary d n)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
    tfc_BoundaryArmInjection ω n := by
  refine ⟨fun _ => a, fun x _ _ => ha, ?_⟩
  intro x hxbox htri y hybox htriy _
  exact (hsingle x hxbox htri).trans (hsingle y hybox htriy).symm

/-! ## D. Unsatisfiability of the configuration-wide conditions -/

/-- `tfc_BoundaryArmInjection` for every configuration and every box of radius `n ≥ 1` is impossible
when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma lhc_not_forall_boundaryArmInjection (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      tfc_BoundaryArmInjection ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    tfc_Tcount_le_boundary_of_residue ω n (h ω n hn)

end Percolation

end StatMech
