/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ladner's theorem: NP-intermediate languages exist

Source:
R. E. Ladner, "On the structure of polynomial time reducibility", Journal of the ACM 22 (1975),
155-171.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Ladner

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Ladner's theorem: NP-intermediate languages exist

If `P ≠ NP`, then there is a language in `NP` that is neither in `P` nor `NP`-complete: it lies
strictly between `P` and the `NP`-complete languages, where `NP`-completeness is polynomial-
time many-one completeness (`Cslib.CookLevin.PolyManyOneRed`) for the canonical classes.
-/

/-- **Ladner's theorem: NP-intermediate languages exist.** Source: R. E. Ladner, "On the
structure of polynomial time reducibility", Journal of the ACM 22 (1975), 155-171. -/
public theorem_wanted ladner :
    MetaMathlibExt.ComplexityTheory.P ≠ MetaMathlibExt.ComplexityTheory.NP →
      ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP ∧ L ∉ MetaMathlibExt.ComplexityTheory.P ∧
          ¬ (∀ L' : MetaMathlibExt.ComplexityTheory.DecisionProblem,
            L' ∈ MetaMathlibExt.ComplexityTheory.NP →
              Cslib.CookLevin.PolyManyOneRed L' L)

end MetaMathlibExt.Complexity.KeyTheorems.Ladner
