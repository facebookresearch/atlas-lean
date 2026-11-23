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

/-- **Guy's question on non-squarefree base-two pseudoprimes beyond $10^{13}$.** The statement
that there is a natural number $n > 10^{13}$ that is a Fermat pseudoprime to base $2$ (a
composite number $n > 1$ with $n \mid 2^{n-1} - 1$) and is not squarefree.

Guy reports 54 non-squarefree base-two pseudoprimes up to $10^{13}$, all multiples of $1093^2$ or
$3511^2$, and asks whether there are any other "square psp"s. Here "square psp" means a
non-squarefree base-two pseudoprime, not a number that is itself a perfect square. Guy poses this
as a question; this is its affirmative existence form, which does not predict the answer. -/
def conjecture : Prop :=
  ∃ n : ℕ,
    Nat.FermatPsp n 2 ∧
    ¬ Squarefree n ∧
    10 ^ 13 < n

/--
**A non-squarefree base-two pseudoprime beyond $10^{13}$ exists.** There is a natural number
$n > 10^{13}$ that is a Fermat pseudoprime to base $2$ (a composite number $n > 1$ with
$n \mid 2^{n-1} - 1$) and is not squarefree.

OEIS A158358 gives the witness $n = 10063351640161 = 73 \cdot 257 \cdot 449 \cdot 1093^2$.

Source: OEIS A158358, nonsquarefree Poulet numbers, https://oeis.org/A158358. Moved from
`OpenConjectures/NumberTheory/NonSquarefreeBaseTwoPseudoprime`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.NonSquarefreeBaseTwoPseudoprimeWanted
