/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.FK.RandomCluster
import Code.FK.MonoBC
import Code.FK.InfiniteVolume
import Code.Lattice.BoundaryConditions
import Code.Foundations.StochasticDomination

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]












theorem bc_le_boundaryClique (C : SimpleGraph V)
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y) :
    C ≤ StatMech.Lattice.boundaryCliqueGraph bdry := by
  intro x y hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  obtain ⟨hx, hy⟩ := hC x y hxy
  exact ⟨C.ne_of_adj hxy, hx, hy⟩






theorem bcProb_bot_eq_fkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    bcProb G (⊥ : SimpleGraph V) p q ω = fkProb G p q ω := by
  have hw : ∀ η, bcWeight G (⊥ : SimpleGraph V) p q η = fkWeight G p q η := by
    intro η
    rw [bcWeight, fkWeight, numClustersBC_bot]
  have hZ : bcZ G (⊥ : SimpleGraph V) p q = fkZ G p q := by
    rw [bcZ, fkZ]; exact Finset.sum_congr rfl (fun η _ => hw η)
  rw [bcProb, fkProb, hw, hZ]





theorem bcProb_clique_eq_wiredFkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω
      = wiredFkProb G bdry p q ω := by
  have hw : ∀ η, bcWeight G (StatMech.Lattice.boundaryCliqueGraph bdry) p q η
      = wiredFkWeight G bdry p q η := by
    intro η
    rw [bcWeight, wiredFkWeight, numClustersBC_boundaryClique]
  have hZ : bcZ G (StatMech.Lattice.boundaryCliqueGraph bdry) p q = wiredFkZ G bdry p q := by
    rw [bcZ, wiredFkZ]; exact Finset.sum_congr rfl (fun η _ => hw η)
  rw [bcProb, wiredFkProb, hw, hZ]










theorem bcProb_free_le (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω :=
  bcProb_mono_bc G (⊥ : SimpleGraph V) C bot_le hp hp1 hq hA





theorem bcProb_le_wired (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  bcProb_mono_bc G C (StatMech.Lattice.boundaryCliqueGraph bdry)
    (bc_le_boundaryClique bdry C hC) hp hp1 hq hA













theorem bcProb_extremality (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
        ≤ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
            * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  ⟨bcProb_free_le G C hp hp1 hq hA, bcProb_le_wired G bdry C hC hp hp1 hq hA⟩







theorem fkProb_le_bcProb_le_wiredFkProb (C : SimpleGraph V) [DecidableRel C.Adj]
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
