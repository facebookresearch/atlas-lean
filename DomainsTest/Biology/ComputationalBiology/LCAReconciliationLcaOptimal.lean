/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.ComputationalBiology.LCAReconciliationLcaOptimal

/-!
# LCA optimality corollaries

These tests derive uniqueness from a loss or deep-coalescence cost no greater than the LCA cost.
-/

namespace DomainsTest.Biology.ComputationalBiology.LCAReconciliationLcaOptimal

open WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted

example {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (f : G → S) (hf : IsReconciliation TG TS lab f)
    (hcost : gl TG TS f ≤ gl TG TS M) : f = M := by
  have h := lca_optimal TG TS lab hlab M hM f hf
  exact h.2.1.2 (le_antisymm hcost h.2.1.1)

example {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (M : G → S)
    (hM : IsLCAReconciliation TG TS lab M) (f : G → S) (hf : IsReconciliation TG TS lab f)
    (hcost : dc TG TS f ≤ dc TG TS M) : f = M := by
  have h := lca_optimal TG TS lab hlab M hM f hf
  exact h.2.2.1.2 (le_antisymm hcost h.2.2.1.1)

end DomainsTest.Biology.ComputationalBiology.LCAReconciliationLcaOptimal
