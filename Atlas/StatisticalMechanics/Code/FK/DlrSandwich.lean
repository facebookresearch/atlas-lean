/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.FK.RandomCluster
import Code.FK.MonoBC
import Code.FK.DomainMarkov
import Code.Lattice.BoundaryConditions
import Code.Inequalities.IncreasingEvent

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
















theorem bcProb_free_le_bc (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω :=
  bcProb_mono_bc G (⊥ : SimpleGraph V) C bot_le hp hp1 hq hA

variable (bdry : V → Prop) [DecidablePred bdry]









theorem bcProb_bc_le_wired (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : C ≤ StatMech.Lattice.boundaryCliqueGraph bdry)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  bcProb_mono_bc G C (StatMech.Lattice.boundaryCliqueGraph bdry) hC hp hp1 hq hA


















theorem bcProb_dlr_sandwich (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : C ≤ StatMech.Lattice.boundaryCliqueGraph bdry)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω
    ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
            * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  ⟨bcProb_free_le_bc G C hp hp1 hq hA,
   bcProb_bc_le_wired G bdry C hC hp hp1 hq hA⟩









theorem bcProb_dlr_sandwich_top (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω
    ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
            * bcProb G (⊤ : SimpleGraph V) p q ω :=
  ⟨bcProb_mono_bc G (⊥ : SimpleGraph V) C bot_le hp hp1 hq hA,
   bcProb_mono_bc G C (⊤ : SimpleGraph V) le_top hp hp1 hq hA⟩




















theorem condFkProb_expect_eq_inducedFkProb_expect {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) (f : ConfigSpace (Sym2 V) → ℝ) :
    (∑ ω ∈ condFibre F ψ, f ω * condFkProb G p q F ψ ω)
      = ∑ ω ∈ condFibre F ψ, f ω * inducedFkProb G p q F ψ ω :=
  Finset.sum_congr rfl
    (fun ω _ => by rw [condFkProb_eq_inducedFkProb G hp hp1 hq F ψ ω])

end FK

end StatMech
