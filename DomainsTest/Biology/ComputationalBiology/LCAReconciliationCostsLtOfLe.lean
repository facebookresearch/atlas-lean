/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe

/-!
# Tests for monotonicity of reconciliation costs

Loss and deep-coalescence cost inequalities force equality of comparable reconciliations.

Source: T. Wu and L. Zhang, "Structural properties of the reconciliation space and their
applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree",
BMC Bioinformatics 12 (Suppl 9) (2011) S7, doi:10.1186/1471-2105-12-S9-S7, definitions (1)–(3),
Theorem 2 and Corollary 4.
-/

namespace DomainsTest.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe

open WantedExt.Biology.ComputationalBiology.LCAReconciliationWanted

example {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (f f' : G → S)
    (hf : IsReconciliation TG TS lab f) (hf' : IsReconciliation TG TS lab f')
    (hle : ∀ v, TS.Le (f' v) (f v)) (hcost : gl TG TS f ≤ gl TG TS f') : f' = f := by
  by_contra hne
  exact (not_lt_of_ge hcost) (costs_lt_of_le TG TS lab hlab f f' hf hf' hle hne).2.1

example {G S : Type*} [Fintype G] [Fintype S]
    (TG : RootedBinTree G) (TS : RootedBinTree S) (lab : G → S)
    (hlab : ∀ x, TG.IsLeaf x → TS.IsLeaf (lab x)) (f f' : G → S)
    (hf : IsReconciliation TG TS lab f) (hf' : IsReconciliation TG TS lab f')
    (hle : ∀ v, TS.Le (f' v) (f v)) (hcost : dc TG TS f ≤ dc TG TS f') : f' = f := by
  by_contra hne
  exact (not_lt_of_ge hcost) (costs_lt_of_le TG TS lab hlab f f' hf hf' hle hne).2.2

end DomainsTest.Biology.ComputationalBiology.LCAReconciliationCostsLtOfLe
