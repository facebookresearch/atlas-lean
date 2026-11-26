/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.FlowShop.Hardness
public import CSLibExt.Computability.Complexity.Karp.FlowShop.Verifier

/-!
# NP-completeness of three-machine flow-shop scheduling

Three-machine flow-shop scheduling is in NP and every language in NP reduces to it in
polynomial time.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShop

/-- **3-MACHINE FLOW SHOP SCHEDULING is NP-complete.** The 3-machine flow shop scheduling
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey, D. S. Johnson, and
R. Sethi, "The complexity of flowshop and jobshop scheduling", Mathematics of Operations
Research 1 (1976), 117-129; T. F. Gonzalez and S. Sahni, "Flowshop and jobshop schedules:
complexity and approximation", Operations Research 26 (1978), 36-52. -/
theorem flowShop_npComplete :
    flowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flowShopDec :=
  ⟨flowShop_mem_NP, flowShop_hard⟩

end MetaMathlibExt.Complexity.NPComplete.FlowShop
