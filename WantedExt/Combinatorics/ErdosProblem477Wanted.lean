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
/-- **Erdős Problem 477.** The statement that there are a polynomial $f$ with integer
coefficients of degree at least $2$ and a set $A$ of integers such that for every integer $n$
there is exactly one pair $(a, b)$ with $a \in A$, $b = f(k)$ for some integer $k$, and
$n = a + b$. Only the pair is required to be unique, not the integer $k$. -/
def conjecture : Prop :=
  ∃ (f : Polynomial ℤ) (A : Set ℤ),
    (↑(2 : ℕ) : WithBot ℕ) ≤ Polynomial.degree f ∧
      ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ Set.range (fun k : ℤ => Polynomial.eval k f) ∧ n =
        p.1 + p.2

-- Carried source audit `UM-00002137-Q001` (see the Moved/ record).

/--
**Erdős Problem 477 has a positive answer.** There are a polynomial $f$ with integer
coefficients of degree at least $2$ and a set $A$ of integers such that for every integer $n$
there is exactly one pair $(a, b)$ with $a \in A$, $b = f(k)$ for some integer $k$, and
$n = a + b$.

Contrary to Erdős and Graham's expectation, GPT (prompted independently by L. Price and
pipeline-math) proved that such a set $A$ exists for $f(k) = k^d$ with every even $d \ge 6$, so
$f(k) = k^6$ is a witness.

Source:
T. F. Bloom, Erdős Problem #477, erdosproblems.com (live page, LaTeX source and forum threads
read 2026-10-22), https://www.erdosproblems.com/477. Moved from
`OpenConjectures/Combinatorics/ErdosProblem477`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem477Wanted
