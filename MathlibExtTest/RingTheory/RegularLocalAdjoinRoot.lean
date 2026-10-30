/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RegularLocalRing.AdjoinRoot

@[expose] public section

open Polynomial

example (S : Type*) [CommRing S] [IsRegularLocalRing S]
    (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ IsLocalRing.maximalIdeal S)
    (h0 : g.coeff 0 ∉ IsLocalRing.maximalIdeal S ^ 2) :
    IsRegularLocalRing (AdjoinRoot g) ∧ ringKrullDim (AdjoinRoot g) = ringKrullDim S :=
  IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
    S g hg hn hcoeff h0
