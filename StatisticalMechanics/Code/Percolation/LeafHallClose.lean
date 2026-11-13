/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.ForestLeafCountClose
import Code.Percolation.SpanningTreeRealiseClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}









open Classical in

noncomputable def lhc_trace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d) :
    Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d ω x₀ z)

theorem lhc_mem_trace {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x₀ z : Site d} :
    z ∈ lhc_trace ω n x₀ ↔ z ∈ vertexBoundary d n ∧ Connected d ω x₀ z := by
  classical
  rw [lhc_trace, Finset.mem_filter, tfc_mem_boundaryFinset]


theorem lhc_trace_card_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d) :
    (lhc_trace ω n x₀).card ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_boundaryFinset_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)








open Classical in



theorem lhc_two_le_trace_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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






theorem lhc_twice_Tcount_succ_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
















def lhc_ConnectedClawTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ x₀ : Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x) ∧
    (lhc_trace ω n x₀).card < 2 * Tcount d ω n




theorem lhc_not_forestLeafSelection_of_clawTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : lhc_ConnectedClawTrace ω n) :
    ¬ str_ForestLeafSelection ω n := by
  rintro h
  obtain ⟨x₀, hconn, hsmall⟩ := hclaw
  have hge := lhc_two_le_trace_of_forestLeafSelection ω n x₀ hconn h
  omega





theorem lhc_clawTrace_excludes_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : lhc_ConnectedClawTrace ω n) (h : str_ForestLeafSelection ω n) : False :=
  lhc_not_forestLeafSelection_of_clawTrace ω n hclaw h















theorem lhc_clawTrace_card_consistent {T : ℕ} (hT : 3 ≤ T) :
    T + 2 ≤ T + 2 ∧ T + 2 < 2 * T :=
  ⟨le_refl _, by omega⟩







theorem lhc_clawTrace_of_smallTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d)
    (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
    (hsmall : (lhc_trace ω n x₀).card < 2 * Tcount d ω n) :
    lhc_ConnectedClawTrace ω n :=
  ⟨x₀, hconn, hsmall⟩


















theorem lhc_boundaryArmInjection_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    tfc_BoundaryArmInjection ω n := by
  obtain ⟨r₀, ℓ, _hr₀, hℓbdry, _hℓconn, _hℓr₀, hℓinj⟩ := h
  refine ⟨fun x => ℓ x 0, ?_, ?_⟩
  · intro x hxbox htri; exact hℓbdry x hxbox htri 0
  · intro x hxbox htri y hybox htriy hxy
    exact (hℓinj x hxbox htri y hybox htriy 0 0 hxy).1





theorem lhc_Tcount_le_boundary_of_boundaryArmInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tfc_BoundaryArmInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_residue ω n h






theorem lhc_Tcount_le_boundary_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  lhc_Tcount_le_boundary_of_boundaryArmInjection ω n
    (lhc_boundaryArmInjection_of_forestLeafSelection ω n h)





theorem lhc_boundaryArmInjection_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r a : Site d} (ha : a ∈ vertexBoundary d n)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
    tfc_BoundaryArmInjection ω n := by
  refine ⟨fun _ => a, fun x _ _ => ha, ?_⟩
  intro x hxbox htri y hybox htriy _
  exact (hsingle x hxbox htri).trans (hsingle y hybox htriy).symm





















theorem lhc_burton_keane_bernoulli_of_boundaryArmInjection (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfc_BoundaryArmInjection ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (fun ω n hn => lhc_Tcount_le_boundary_of_boundaryArmInjection ω n (hres ω n hn))
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation

end StatMech
