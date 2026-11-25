/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.BGW.ResharingPrivacy
public import Mathlib.Algebra.Field.ZMod

/-!
# Tests for BGW re-sharing view uniformity

Two-party threshold-1 instance over `ZMod 5`: the R3 uniformity instance,
its pointwise form on the support, a marginal instance, the R4 boundary
instances, and axiom checks.
-/

@[expose] public section

namespace CSLibExtTest.Crypto.Protocols.BGW

open CSLibExt.Crypto.Protocols.BGW
open Cslib.Crypto.Protocols.SecretSharing

/-- Two parties. -/
abbrev TestParty := Fin 2

/-- Small prime field. -/
abbrev TestField := ZMod 5

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_iff.mpr (by decide)⟩

/-- Threshold-1 Shamir parameters on two parties. -/
def testParams : Shamir.Params TestField TestParty where
  threshold := 1
  threshold_lt_card := by decide
  point := fun i => ((i.val + 1 : ℕ) : TestField)
  point_injective := by decide
  point_nonzero := by decide

/-- Uniform tail sampler for the test parameters. -/
noncomputable def testSampler : Shamir.TailSampler testParams :=
  Shamir.uniformTailSampler testParams

/-- Singleton (unauthorized) coalition. -/
def testCoalition : Finset TestParty := {0}

/-- Dealer values differing everywhere, even on the coalition. -/
def testDealA : TestParty → TestField := fun i => (i.val : TestField)

/-- Dealer values differing everywhere, even on the coalition. -/
def testDealB : TestParty → TestField := fun _ => 4

/-- R3 on two parties over `ZMod 5`: the received matrix does not see the
re-shared values, although they differ on the coalition itself. -/
example : dealerViews testParams testSampler testCoalition testDealA =
    dealerViews testParams testSampler testCoalition testDealB :=
  dealerViews_eq_of_unauthorized testParams testSampler testCoalition
    (by decide) testDealA testDealB

/-- Pointwise form of the R3 instance on the support: both matrices assign
every supported matrix the same mass. -/
example (g : TestParty → testCoalition → TestField)
    (_hg : g ∈ (dealerViews testParams testSampler testCoalition testDealA).support) :
    dealerViews testParams testSampler testCoalition testDealA g =
      dealerViews testParams testSampler testCoalition testDealB g := by
  rw [dealerViews_eq_of_unauthorized testParams testSampler testCoalition
    (by decide) testDealA testDealB]

/-- Marginal instance: row `0` is dealer `0`'s own view. -/
example : (dealerViews testParams testSampler testCoalition testDealA).map (fun g => g 0) =
    viewDistOf testSampler.gen (Shamir.share testParams) testCoalition (testDealA 0) :=
  dealerViews_map_eval testParams testSampler testCoalition testDealA 0

/-- R4: the empty coalition sees the same trivial matrix. -/
example : dealerViews testParams testSampler ∅ testDealA =
    dealerViews testParams testSampler ∅ testDealB :=
  dealerViews_empty_eq testParams testSampler testDealA testDealB

/-- R4: single-row sanity over the unauthorized singleton coalition. -/
example (g0 : TestParty → testCoalition → TestField) :
    dealerViewsAux
        (fun j => viewDistOf testSampler.gen (Shamir.share testParams) testCoalition
          (testDealA j)) [0] g0 =
      dealerViewsAux
        (fun j => viewDistOf testSampler.gen (Shamir.share testParams) testCoalition
          (testDealB j)) [0] g0 :=
  dealerViewsAux_singleton_eq testParams testSampler (by simp only [Shamir.authorized]; decide)
    testDealA testDealB 0 g0

#print axioms dealerViews_eq_of_unauthorized
#print axioms dealerViews_eq_of_agree_on
#print axioms dealerViews_map_eval

end CSLibExtTest.Crypto.Protocols.BGW
