/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.OffCentreDomination








namespace StatMech.FK

noncomputable section



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
    rw [if_neg hrho, mul_zero]
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
    ocd_condBcProb_congr_dom G C p q F rho psi rho
      (agreesOff_symm hrho)
  rw [hcond] at hbc
  rw [hbc]
  ring

end

end StatMech.FK
