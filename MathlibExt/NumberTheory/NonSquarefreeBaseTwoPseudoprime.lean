/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.FermatPsp
import Mathlib.Tactic.ReduceModChar

/-!
# A non-squarefree base-two pseudoprime beyond `10 ^ 13`

The theorem `conjecture_holds` verifies the Fermat congruence and a square divisor for the
witness 10063351640161.
-/

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
theorem conjecture_holds : conjecture := by
  have hnsq : ¬ Squarefree (10063351640161 : ℕ) := by
    intro h
    have hunit := h 1093 (by decide)
    norm_num [Nat.isUnit_iff] at hunit
  refine ⟨10063351640161, ⟨?_, fun hp => hnsq hp.prime.squarefree, by decide⟩, hnsq, by decide⟩
  apply (Nat.probablePrime_iff_zmod_one _ (by decide)).2
  reduce_mod_char

end MathlibExt.NumberTheory.NonSquarefreeBaseTwoPseudoprimeWanted
