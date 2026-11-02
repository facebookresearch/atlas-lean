/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination

/-!
# Conditioning on a fibre of the boundary-conditioned measure

The mass of an event inside a conditioning fibre is the fibre mass times the conditional probability
of the event.

## i. Overview

Fix a set `F` of edges and a configuration `ψ`; the fibre consists of the configurations agreeing
with `ψ` off `F`. Each configuration in the fibre has the same fibre and the same conditional law,
so the factorization `μ(ρ) = μ(fibre) · μ(ρ | fibre)` sums to `μ(A ∩ fibre) = μ(fibre) · μ(A |
fibre)`. This is the law of total probability for the boundary-conditioned random-cluster measure.

The result is proved unconditionally, under only `0 < p < 1` and `0 < q`.

## ii. Key results

- `condBcProb_event_fibre_eq_mass_mul_cond` : `μ(A ∩ fibre) = μ(fibre) · μ(A | fibre)`.

## iii. Table of contents

- A. Event mass in a fibre

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

namespace StatMech.FK

noncomputable section

/-! ## A. Event mass in a fibre -/

/-- The boundary-conditioned mass of `A` inside the fibre of `ψ` off `F` is the fibre mass times the
conditional probability of `A`. -/
theorem condBcProb_event_fibre_eq_mass_mul_cond
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (psi : ConfigSpace (Sym2 V))
    (A : Set (ConfigSpace (Sym2 V))) :
    (∑ rho ∈ condFibre F psi,
        A.indicator (fun _ => (1 : Real)) rho * bcProb G C p q rho) =
      (∑ sigma ∈ condFibre F psi, bcProb G C p q sigma) *
        (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
          condBcProb G C p q F psi rho) := by
  have hrestrict :
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
          condBcProb G C p q F psi rho) =
        ∑ rho ∈ condFibre F psi,
          A.indicator (fun _ => (1 : Real)) rho *
            condBcProb G C p q F psi rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho _ hrho
    rw [mem_condFibre] at hrho
    unfold condBcProb
    rw [ite_eq_right hrho, mul_zero]
  rw [hrestrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hbc := bcProb_eq_fibreMass_mul_condBcProb
    G C hp hp1 hq F rho
  have hfib : condFibre F rho = condFibre F psi := by
    ext sigma
    rw [mem_condFibre, mem_condFibre,
      agreesOff_congr (agreesOff_symm hrho)]
  rw [hfib] at hbc
  have hcond : condBcProb G C p q F rho rho =
      condBcProb G C p q F psi rho :=
    condBcProb_congr_dom G C p q F rho psi rho
      (agreesOff_symm hrho)
  rw [hcond] at hbc
  rw [hbc]
  ring

end

end StatMech.FK
