/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Unramified.EtaleAt

@[expose] public section

universe u v

-- exactSource consumer, with the original binders.
example (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q]
    (hdim : ringKrullDim (Localization.AtPrime (q.under R)) ≤
      ringKrullDim (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q ∧ Module.Flat R (Localization.AtPrime q) :=
  Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le R S q hdim

example :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
      (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
      (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q],
      ringKrullDim (Localization.AtPrime (q.under R)) ≤
        ringKrullDim (Localization.AtPrime q) →
      Algebra.IsEtaleAt R q ∧ Module.Flat R (Localization.AtPrime q) :=
  @Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le

-- Boundary case: for `S = R` the dimension hypothesis is an equality, and
-- the conclusion says a ring unramified over itself at `q` is étale there.
example (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (q : Ideal R) [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
    Algebra.IsEtaleAt R q ∧ Module.Flat R (Localization.AtPrime q) :=
  Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le R R q (by
    show ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim (Localization.AtPrime q)
    exact le_rfl)
