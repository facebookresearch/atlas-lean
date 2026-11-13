/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.DomainMarkov
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC

/-!
# Free and wired bounds for random-cluster measures with boundary conditions

For `q ≥ 1`, every random-cluster measure with a boundary-condition graph `C` lies between the
free measure (`C = ⊥`) and the wired measure on increasing events.

## i. Overview

The measures `bcProb G C p q` count clusters of `G ∪ C`. Adding boundary edges merges clusters,
so for increasing events the free measure is the smallest; when `C` is contained in the clique on
the boundary vertices, the wired measure (`boundaryCliqueGraph`) is the largest. Conditional
expectations on a fibre agree with expectations under the induced measure (from `DomainMarkov`).

## ii. Key results

- `bcProb_free_le_bc` : `φ^0(A) ≤ φ^C(A)` for increasing `A`.
- `bcProb_bc_le_wired` : `φ^C(A) ≤ φ^1(A)` when `C` is inside the boundary clique.
- `bcProb_dlr_sandwich` : both bounds together.

## iii. Table of contents

- A. The free–wired sandwich
- B. Conditional expectations on a fibre

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Lemma 4.14.
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

/-! ## A. The free–wired sandwich -/

lemma bcProb_free_le_bc (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω :=
  bcProb_mono_bc G (⊥ : SimpleGraph V) C bot_le hp hp1 hq hA

variable (bdry : V → Prop) [DecidablePred bdry]

lemma bcProb_bc_le_wired (C : SimpleGraph V) [DecidableRel C.Adj]
    (hC : C ≤ StatMech.Lattice.boundaryCliqueGraph bdry)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω :=
  bcProb_mono_bc G C (StatMech.Lattice.boundaryCliqueGraph bdry) hC hp hp1 hq hA

/-- For `q ≥ 1` and `C` inside the boundary clique, `φ^0(A) ≤ φ^C(A) ≤ φ^1(A)` for every increasing
event `A`.
-/
lemma bcProb_dlr_sandwich (C : SimpleGraph V) [DecidableRel C.Adj]
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

/-- The free lower bound together with the bound by the boundary condition `⊤` (all vertices
wired).
-/
lemma bcProb_dlr_sandwich_top (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω
    ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω)
        ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
            * bcProb G (⊤ : SimpleGraph V) p q ω :=
  ⟨bcProb_mono_bc G (⊥ : SimpleGraph V) C bot_le hp hp1 hq hA,
   bcProb_mono_bc G C (⊤ : SimpleGraph V) le_top hp hp1 hq hA⟩

/-! ## B. Conditional expectations on a fibre -/

lemma condFkProb_expect_eq_inducedFkProb_expect {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) (f : ConfigSpace (Sym2 V) → ℝ) :
    (∑ ω ∈ condFibre F ψ, f ω * condFkProb G p q F ψ ω)
      = ∑ ω ∈ condFibre F ψ, f ω * inducedFkProb G p q F ψ ω :=
  Finset.sum_congr rfl
    (fun ω _ => by rw [condFkProb_eq_inducedFkProb G hp hp1 hq F ψ ω])

end FK

end StatMech
