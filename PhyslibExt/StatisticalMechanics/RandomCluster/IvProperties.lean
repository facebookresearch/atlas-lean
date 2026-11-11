/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC
/-!
# Extremality of the free and wired boundary conditions

For `q ≥ 1` every boundary wiring supported on the boundary lies between free and wired.

## i. Overview

The free measure is `φ_⊥` and the wired measure is `φ_K` with `K` the clique on the boundary.
A wiring `C` whose edges join boundary vertices satisfies `⊥ ≤ C ≤ K`, so `bcProb_mono_bc`
gives `φ_free(A) ≤ φ_C(A) ≤ φ_wired(A)` for every increasing event `A`.

## ii. Key results

- `bcProb_bot_eq_fkProb`, `bcProb_clique_eq_wiredFkProb` : free and wired as wirings.
- `fkProb_le_bcProb_le_wiredFkProb` : the sandwich free ≼ `φ_C` ≼ wired.

## iii. Table of contents

- A. Free and wired measures as boundary wirings
- B. The sandwich

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-!
## A. Free and wired measures as boundary wirings
-/

/-- A wiring whose edges join boundary vertices lies below the boundary clique. -/
lemma bc_le_boundaryClique (C : SimpleGraph V)
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y) :
    C ≤ StatMech.Lattice.boundaryCliqueGraph bdry := by
  intro x y hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  obtain ⟨hx, hy⟩ := hC x y hxy
  exact ⟨C.ne_of_adj hxy, hx, hy⟩

/-- The empty wiring gives the free random-cluster measure. -/
lemma bcProb_bot_eq_fkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    bcProb G (⊥ : SimpleGraph V) p q ω = fkProb G p q ω := by
  have hw : ∀ η, bcWeight G (⊥ : SimpleGraph V) p q η = fkWeight G p q η := by
    intro η
    rw [bcWeight, fkWeight, numClustersBC_bot]
  have hZ : bcZ G (⊥ : SimpleGraph V) p q = fkZ G p q := by
    rw [bcZ, fkZ]; exact Finset.sum_congr rfl (fun η _ => hw η)
  rw [bcProb, fkProb, hw, hZ]

/-- The boundary clique gives the wired random-cluster measure. -/
lemma bcProb_clique_eq_wiredFkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω
      = wiredFkProb G bdry p q ω := by
  have hw : ∀ η, bcWeight G (StatMech.Lattice.boundaryCliqueGraph bdry) p q η
      = wiredFkWeight G bdry p q η := by
    intro η
    rw [bcWeight, wiredFkWeight, numClustersBC_boundaryClique]
  have hZ : bcZ G (StatMech.Lattice.boundaryCliqueGraph bdry) p q = wiredFkZ G bdry p q := by
    rw [bcZ, wiredFkZ]; exact Finset.sum_congr rfl (fun η _ => hw η)
  rw [bcProb, wiredFkProb, hw, hZ]

/-!
## B. The sandwich
-/

lemma bcProb_free_le (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω :=
  bcProb_mono_bc G (⊥ : SimpleGraph V) C bot_le hp hp1 hq hA

lemma bcProb_le_wired (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  bcProb_mono_bc G C (StatMech.Lattice.boundaryCliqueGraph bdry)
    (bc_le_boundaryClique bdry C hC) hp hp1 hq hA

lemma bcProb_extremality (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
        ≤ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
            * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  ⟨bcProb_free_le G C hp hp1 hq hA, bcProb_le_wired G bdry C hC hp hp1 hq hA⟩

/-- For `q ≥ 1` and a wiring `C` supported on the boundary, free ≤ `φ_C` ≤ wired on every increasing
event. -/
lemma fkProb_le_bcProb_le_wiredFkProb (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω)
        ≤ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω := by
  obtain ⟨hfree, hwired⟩ := bcProb_extremality G bdry C hC hp hp1 hq hA
  constructor
  · refine le_trans (le_of_eq ?_) hfree
    exact Finset.sum_congr rfl fun ω _ => by rw [bcProb_bot_eq_fkProb]
  · refine le_trans hwired (le_of_eq ?_)
    exact Finset.sum_congr rfl fun ω _ => by rw [bcProb_clique_eq_wiredFkProb]

end FK

end StatMech
