/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamComponentAssociationReduction
import Code.Probability.HolleyFKG










open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Probability

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem grahamCutPositiveAssociation_of_fkg_pushforward
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (m : V)
    {Omega : Type*} [Fintype Omega]
    [DistribLattice Omega] [OrderBot Omega]
    (mu : Omega -> Real) (cut : Omega -> Finset V)
    (hmu0 : (0 : Omega -> Real) <= mu)
    (hmu1 : ∑ omega, mu omega = 1)
    (hmuFKG : forall x y,
      mu x * mu y <= mu (x ⊓ y) * mu (x ⊔ y))
    (hcut : Antitone cut)
    (hpush : forall S : Finset V,
      isingCutMass G beta J m S =
        ∑ omega : Omega, if cut omega = S then mu omega else 0) :
    GrahamCutPositiveAssociation G beta J m := by
  classical
  intro f g hf hg
  have hexpect (F : Finset V -> Real) :
      (∑ S : Finset V, isingCutMass G beta J m S * F S) =
        ∑ omega : Omega, mu omega * F (cut omega) := by
    simp_rw [hpush]
    calc
      (∑ S : Finset V,
          (∑ omega : Omega, if cut omega = S then mu omega else 0) * F S) =
          ∑ S : Finset V, ∑ omega : Omega,
            if cut omega = S then mu omega * F S else 0 := by
              apply sum_congr rfl
              intro S _
              rw [sum_mul]
              apply sum_congr rfl
              intro omega _
              split <;> simp_all
      _ = ∑ omega : Omega, ∑ S : Finset V,
          if cut omega = S then mu omega * F S else 0 := sum_comm
      _ = ∑ omega : Omega, mu omega * F (cut omega) := by
        apply sum_congr rfl
        intro omega _
        simp
  have hfanti : Antitone (fun omega => f (cut omega)) := fun a b hab =>
    hf (hcut hab)
  have hganti : Antitone (fun omega => g (cut omega)) := fun a b hab =>
    hg (hcut hab)
  have hnF : Monotone (fun omega => -f (cut omega)) := fun a b hab =>
    neg_le_neg (hfanti hab)
  have hnG : Monotone (fun omega => -g (cut omega)) := fun a b hab =>
    neg_le_neg (hganti hab)
  have hassoc := StatMech.Probability.fkg_inequality
    hmu0 hmu1 hmuFKG hnF hnG
  have hnegF : (∑ omega : Omega, mu omega * -f (cut omega)) =
      -(∑ omega : Omega, mu omega * f (cut omega)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro omega _
    ring
  have hnegG : (∑ omega : Omega, mu omega * -g (cut omega)) =
      -(∑ omega : Omega, mu omega * g (cut omega)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro omega _
    ring
  rw [hnegF, hnegG] at hassoc
  simp only [neg_mul_neg] at hassoc
  rw [hexpect f, hexpect g, hexpect (fun S => f S * g S)]
  exact hassoc

end StatMech.FrontierA
