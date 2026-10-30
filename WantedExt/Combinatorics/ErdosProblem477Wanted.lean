/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 477
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem477Wanted

/-! Source record `UM-00002137-Q001`. -/
/-- Some integer polynomial `f` of degree at least two and some `A ⊆ ℤ` represent every integer
uniquely as `a + f(k)` with `a ∈ A` (the pair `(a, f(k))` is unique). -/
def conjecture : Prop :=
  ∃ (f : Polynomial ℤ) (A : Set ℤ),
    (↑(2 : ℕ) : WithBot ℕ) ≤ Polynomial.degree f ∧
      ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ Set.range (fun k : ℤ => Polynomial.eval k f) ∧ n =
        p.1 + p.2

-- Carried source audit `UM-00002137-Q001` (see the Moved/ record).

/--
Resolved true: Resolved true, against Erdős and Graham's expectation: erdosproblems.com/477
records that GPT (prompted independently by L. Price and pipeline-math) proved such an A exists
for f(n) = n^d with every even d >= 6, so f = X^6 witnesses the existential statement. Source:
T. F. Bloom, Erdős Problem #477, erdosproblems.com (live page, LaTeX source and forum threads
read 2026-10-22), https://www.erdosproblems.com/477. Moved from
`OpenConjectures/Combinatorics/ErdosProblem477`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem477Wanted
