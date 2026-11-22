/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A non-squarefree base-two pseudoprime beyond `10 ^ 13`
-/
module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.FermatPsp
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.NonSquarefreeBaseTwoPseudoprimeWanted

/-! Source record `UnsolvedMath GUY-A12a` (numeric id `1875`), "Square Pseudoprimes". -/

/-- Guy reports 54 non-squarefree base-two pseudoprimes up to `10 ^ 13`, all
multiples of `1093 ^ 2` or `3511 ^ 2`, and asks whether there are any other
"square psp"s. Here "square psp" means a non-squarefree base-two pseudoprime,
not a number that is itself a perfect square. Guy poses this as a question, so
the statement below is the affirmative existence form (a witness beyond
`10 ^ 13`) without predicting its polarity. -/
def conjecture : Prop :=
  ∃ n : ℕ,
    Nat.FermatPsp n 2 ∧
    ¬ Squarefree n ∧
    10 ^ 13 < n

/--
Resolved true: OEIS A158358 gives the witness 10063351640161 > 10^13, with factorization 73 ·
257 · 449 · 1093², so a non-squarefree base-two pseudoprime beyond 10^13 exists. Source: OEIS
A158358, nonsquarefree Poulet numbers, https://oeis.org/A158358. Moved from
`OpenConjectures/NumberTheory/NonSquarefreeBaseTwoPseudoprime`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.NonSquarefreeBaseTwoPseudoprimeWanted
